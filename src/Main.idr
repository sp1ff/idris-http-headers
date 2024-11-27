{- Copyright (C) 2024 Michael Herstine <sp1ff@pobox.com>

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
  General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>. -}

||| A simple demonstration program that represents HTTP/1.1 headers
||| using dependent types. Invoke it as:
|||
||| ```text
||| demo [name0 value0] [name1 value1]...
||| ```
|||
||| It will add a few constant values as well as the header named `name0`
||| with value `value0` and so on, and print the resulting header map
||| on stdout.
module Main

import Header

import Decidable.Equality
import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Maybe
import System

||| Divide a list into pairs of its elements
-- I'm a bit surprised this isn't in the stdlib
asPairs : List a -> List (a, a)
asPairs [] = []
asPairs [_] = []
asPairs (x1 :: x2 :: xs) = (x1, x2) :: asPairs xs 

addHeader : HeaderMap -> (String, String) -> IO HeaderMap
addHeader hmap (name, value) = do
  let Just hmap = tryAppendS hmap name value
      | Nothing => do putStrLn $ "Failed to parse header: " ++ name ++ ", " ++ value
                      pure hmap
  pure hmap

main : IO ()
main = do
  {- Demonstrate adding a few headers known at compile-time: -}
  let headers = insert empty ContentLength 16
  {- Would be nice if we could implement FromString for Hostname... -}
  let headers = insert headers Host (mkHostnameStr "localhost:8000")
  {- This is regrettable, as addHeader can fail. I *know* these
     parameters are a legit header name & value, resp. -}
  headers <- addHeader headers ("X-Custom", "test")

  {- Now parse the command line for additional headers: -}
  argv <- getArgs
  let args = asPairs $ drop 1 argv
  headers <- foldlM addHeader headers args
  putStrLn $ show headers
