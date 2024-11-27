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

||| A dependently-typed implementation of HTTP/1.1 Headers
|||
||| # Introduction
|||
||| This module provides basic facilities around parsing, forming &
||| using HTTP/1.1 message headers. The implementation is inspired by 
||| the Rust hyper crate
||| <https://docs.rs/hyper/latest/hyper/index.html>, discussed in
||| Amos' great article "Aiming for Correctness with Types"
||| <https://fasterthanli.me/articles/aiming-for-correctness-with-types>.
||| It was also written after reading the implementation of the
||| idris2-http <https://github.com/idris-community/idris2-http> 
||| package, which I was pleased to see incorporated some of the same
||| techniques.
|||
||| # Headers
|||
||| Headers consist of a name paired with a value. The rules for forming
||| both use the following definitions:
|||
||| ```text
||| SP    = the space character; ASCII code 32 = 0x20
||| HT    = the horizontal tab character; ASCII code 9 = 0x09
||| CTL   = any US-ASCII control character (octets 0 - 31) and DEL (127)
||| VCHAR = any visible ASCII character
||| ```
|||
||| ## Header Names
|||
||| Syntactically, a header name is consistently defined as a 'token'
||| across all the RFCs (see below). The format for a token is defined
||| in RFC 2616 sec. 2.2, RFC 7230 sec. 3.2.6, and RFC 9110 sec. 5.6.2. 
||| I'll use the BNF from RFC 2616:
|||
||| ```text
||| token       = 1*<any ASCII character except CTLs or separators>
||| separators  = '(' | ')' | '<' | '>' | '@'
|||             | ',' | ';' | ':' | '\' | '"'
|||             | '/' | '[' | ']' | '?' | '='
|||             | '{' | '}' | SP  | HT
||| ```
||| 
||| In other words, header names are made-up of a certain subset of the ASCII
||| character set, not a general Idris String which can contain non-ASCII
||| characters.
|||
||| ## Header Values
|||
||| Header values are a little more interesting. RFC 9110 says
|||
||| ```text
||| field-value   = *field-content
||| field-content = field-vchar [ 1*( SP | HTAB | field-vchar ) field-vchar ]
||| field-vchar   = VCHAR | obs-text
||| obs-text      = %x80-FF
||| ```
||| 
||| Prior versions of the RFC allowed for "folding" field values, e.g.
|||
||| ```text
||| header-name: line1
|||  line2
|||  line3
||| next-header: ...
||| ```
|||
||| However, RFC 9110 removes that: "Field values containing CR, LF, or NUL 
||| characters are invalid and dangerous, due to the varying ways that
||| implementations might parse and interpret those characters; a
||| recipient of CR, LF, or NUL within a field value MUST either reject
||| the message or replace each of those characters with SP before further
||| processing or forwarding of that message." 
||| <https://www.ietf.org/rfc/rfc9110.html#section-5.5-5>
||| Therefore, this implementation provides no support for that.
|||
||| Regarding the obs-text token above "Field values are usually constrained 
||| to the range of US-ASCII characters. Fields needing a greater range of
||| characters can use an encoding, such as the one defined in RFC 8187. 
||| Historically, HTTP allowed field content with text in the ISO-8859-1
||| charset, supporting other charsets only through use of RFC 2047
||| encoding. Specifications for newly defined fields SHOULD limit their
||| values to visible US-ASCII octets (VCHAR), SP, and HTAB. A recipient
||| SHOULD treat other allowed octets in field content (i.e., obs-text) 
||| as opaque data." <https://www.ietf.org/rfc/rfc9110.html#section-5.5-4>
|||
||| # References
|||
||| The HTTP protocol is documented in a series of RFCs:
|||
||| - RFC 822 Standard for ARPA Internet Text Messages
|||   <https://www.ietf.org/rfc/rfc822.html>, released in 1982
||| - RFC 2616 Hypertext Transfer Protocol - HTTP/1.1
|||   <https://www.ietf.org/rfc/rfc2616.html>, released in 1999
||| - RFC 7230 Hypertext Transfer Protocol (HTTP/1.1): Message Syntax and Routing
|||   <https://www.ietf.org/rfc/rfc7230.html>, released in 2014
|||   and revising RFC 2616
||| - RFC 9110 HTTP Semantics <https://www.ietf.org/rfc/rfc9110.html>, 
|||   released in 2022 & revising RFC 7230
||| - RFC 9112 HTTP/1.1, <https://www.ietf.org/rfc/rfc9112.html> also
|||   released in 2022
|||
||| The format for hostnames is documented in
|||
||| - RFC 3986 Uniform Resource Identifier (URI): Generic Syntax
|||   <https://www.ietf.org/rfc/rfc3986.html>, released in 2005
|||   and obsoleting RFCs 2732, 2396 & 1808
module Header

import Decidable.Equality
import Data.List
import Data.List.Quantifiers
import Data.List.Views
import Data.List1
import Data.Refined.String
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

||| Return True if the given Char represents a token constituent
public export
isTokenChar : Char -> Bool
isTokenChar '"' = False -- 0x22
isTokenChar '(' = False -- 0x28
isTokenChar ')' = False -- 0x29
isTokenChar ',' = False -- 0x2c
isTokenChar '/' = False -- 0x2f
isTokenChar ':' = False -- 0x3a
isTokenChar ';' = False -- 0x3b
isTokenChar '<' = False -- 0x3c
isTokenChar '=' = False -- 0x3d
isTokenChar '>' = False -- 0x3e
isTokenChar '?' = False -- 0x3f
isTokenChar '@' = False -- 0x40
isTokenChar '[' = False -- 0x5b
isTokenChar '\\'= False -- 0x5c
isTokenChar ']' = False -- 0x5d
isTokenChar '{' = False -- 0x7b
isTokenChar '}' = False -- 0x7d
isTokenChar x   = (x > '\32') && (x < '\127')

||| Return True if the given byte contains the ASCII code for a token
||| constituent
public export
isTokenByte : Bits8 -> Bool
isTokenByte = isTokenChar . chr . cast

||| The `All` predicate adapted to `List1`
-- I'm a bit surprised this isn't available in the stdlib, somewhere.
public export
data All1 : (0 p: a -> Type) -> List1 a -> Type where
  All1_head : {0 x : a} -> p x -> All1 p (x ::: [])
  All1_tail : {0 xs : List a} -> p x -> All p xs -> All1 p (x ::: xs)

||| An assertion that all octets in a List1 of Bits8 are token
||| constituents
public export
Token : List1 Bits8 -> Type
Token = All1 (\b => isTokenByte b === True)

||| Given a List of Bits8, along with an assertion that they're all
||| token constituents, return the List with all upper-case ASCII 
||| characters mapped to their lower-case counterparts.
bufToLower : (buf : List Bits8) ->
             {auto is_tok : All (\c => isTokenByte c === True) buf} -> 
             List Bits8
{- I had originally implemented this so as to return a List of Char,
   and much more succinctly

       bufToLower buf = map go buf
                        where go : Bits8 -> Char
                              go b = if (0x40 < b) && (0x5b > b)
                                     then chr $ cast $ b + 32
                                     else chr $ cast b
                                     
   but this made it impossible for Idris to find the required proof
   term (I suspect due to the extensive use of primitive functions
   in that implementation).
   
   Proof search works *much* better with this more prolix
   implementation: -}             
bufToLower [] = []
bufToLower (65 :: xs) {is_tok = pf_x :: pf_xs} = 97  :: bufToLower xs
bufToLower (66 :: xs) {is_tok = pf_x :: pf_xs} = 98  :: bufToLower xs
bufToLower (67 :: xs) {is_tok = pf_x :: pf_xs} = 99  :: bufToLower xs
bufToLower (68 :: xs) {is_tok = pf_x :: pf_xs} = 100 :: bufToLower xs
bufToLower (69 :: xs) {is_tok = pf_x :: pf_xs} = 101 :: bufToLower xs
bufToLower (70 :: xs) {is_tok = pf_x :: pf_xs} = 102 :: bufToLower xs
bufToLower (71 :: xs) {is_tok = pf_x :: pf_xs} = 103 :: bufToLower xs
bufToLower (72 :: xs) {is_tok = pf_x :: pf_xs} = 104 :: bufToLower xs
bufToLower (73 :: xs) {is_tok = pf_x :: pf_xs} = 105 :: bufToLower xs
bufToLower (74 :: xs) {is_tok = pf_x :: pf_xs} = 106 :: bufToLower xs
bufToLower (75 :: xs) {is_tok = pf_x :: pf_xs} = 107 :: bufToLower xs
bufToLower (76 :: xs) {is_tok = pf_x :: pf_xs} = 108 :: bufToLower xs
bufToLower (77 :: xs) {is_tok = pf_x :: pf_xs} = 109 :: bufToLower xs
bufToLower (78 :: xs) {is_tok = pf_x :: pf_xs} = 110 :: bufToLower xs
bufToLower (79 :: xs) {is_tok = pf_x :: pf_xs} = 111 :: bufToLower xs
bufToLower (80 :: xs) {is_tok = pf_x :: pf_xs} = 112 :: bufToLower xs
bufToLower (81 :: xs) {is_tok = pf_x :: pf_xs} = 113 :: bufToLower xs
bufToLower (82 :: xs) {is_tok = pf_x :: pf_xs} = 114 :: bufToLower xs
bufToLower (83 :: xs) {is_tok = pf_x :: pf_xs} = 115 :: bufToLower xs
bufToLower (84 :: xs) {is_tok = pf_x :: pf_xs} = 116 :: bufToLower xs
bufToLower (85 :: xs) {is_tok = pf_x :: pf_xs} = 117 :: bufToLower xs
bufToLower (86 :: xs) {is_tok = pf_x :: pf_xs} = 118 :: bufToLower xs
bufToLower (87 :: xs) {is_tok = pf_x :: pf_xs} = 119 :: bufToLower xs
bufToLower (88 :: xs) {is_tok = pf_x :: pf_xs} = 120 :: bufToLower xs
bufToLower (89 :: xs) {is_tok = pf_x :: pf_xs} = 121 :: bufToLower xs
bufToLower (90 :: xs) {is_tok = pf_x :: pf_xs} = 122 :: bufToLower xs
bufToLower ( x :: xs) {is_tok = pf_x :: pf_xs} = x   :: bufToLower xs

-- ======================================================================
--                           Header Names
-- ======================================================================

||| A list of octets together with a proof of the statement that
||| they are all token constituents
{- Export this, but not as public, since we don't want callers
   instantiating CustomHeaderNames of "Content-Type", e.g.
   Regrettably, this makes unit testing much more difficult. I think I
   prefer Rust's approach to locating the unit tests with the code
   under test (and pre-processing the code out in non-test builds).-}
export
record CustomHeaderName where
  constructor MkCustomHeaderName
  value : List1 Bits8
  {- Can't erase this as its used in the implementation of `Show`. -}
  {auto prf : Token value}

{- I'm going to hand-implement show to print lower-case: -}
public export
Show CustomHeaderName where
  show (MkCustomHeaderName (x ::: []) {prf = (All1_head pf_x)}) = 
    pack $ map (chr . cast) (bufToLower [x])
  show (MkCustomHeaderName (x ::: xs) {prf = (All1_tail pf_x pf_xs)}) = 
    pack $ map (chr . cast) (bufToLower $ x :: xs)

public export
Eq CustomHeaderName where
  (==) x y = (show x) == (show y)

public export
Ord CustomHeaderName where
  compare x y = compare (show x) (show y)

||| HTTP/1.1 compliant header name implementation
|||
||| Obviously, there are many more "standard" headers than just these!
||| This is a demo project.
public export
data HeaderName = Host | ContentLength | CustomHeader CustomHeaderName

%runElab derive "HeaderName" [Eq]

public export
Show HeaderName where
  show Host = "host"
  show ContentLength = "content-length"
  show (CustomHeader cus) = show cus

public export
Ord HeaderName where
  compare x y = compare (show x) (show y)

||| Given a buffer of octets, together with an assertion that the buffer
||| is not empty, and that its contents are all token constituents,
||| return a `HeaderName` instance.
{- I suppose I could have written this in terms of `List1` and
   disposed of the first implicit auto parameter, but `List` seems
   more idiomatic (lots of pre-defined predicates & utility functions
   defined for it, e.g.) and so, hopefully, more ergonomic for
   consumers of the function. -}
public export
mkHeaderName : (buf : List Bits8) -> 
               {auto 0 not_nil : NonEmpty buf} ->
               {auto is_tok : All (\b => isTokenByte b === True) buf} -> 
               HeaderName
mkHeaderName buf@(b :: bs) {not_nil = IsNonEmpty} {is_tok = pf_b :: pf_bs} = 
  {- It's a small pity that I can't just convert these to Char & call
     `pack`; this would allow my match arms to look like
     "content-length", for instance. However, if I do that, the
     primitives involved defeat Idris' proof-finding. -}
  case bufToLower buf of
  [99, 111, 110, 116, 101, 110, 116, 45, 108, 101, 110, 103, 116, 104] => ContentLength
  [104, 111, 115, 116] => Host  
  {- Note that this line will *not* lowercase the header name; I think
     at this point, having verified that it's not equal, modulo ASCII
     casing, to a standard header, I'd like to preserve the caller's
     choice of case. Also, getting a proof term for
     `MkCustomHeaderName` for the lower-cased list is going to be
     bear. -} 
  _ => CustomHeader $ MkCustomHeaderName (b ::: bs)

||| Given an arbitrary buffer of octets, return the corresponding HeaderName
||| if the buffer is a valid header name
{- Of course, we can't always know at compile-time that a proposed
   header name is valid; suppose we're serving HTTP requests and we
   just read the name off the wire, say. -}
public export
tryMkHeaderName : (buf : List Bits8) -> Maybe HeaderName
tryMkHeaderName [] = Nothing
{- This is interesting; the pattern match gives us a proof term for
   `not_nil`; but how to get one for `is_tok`? Ah. That's what the
   `all` function is for, given a suitable proposition. Nb that I
   didn't just write that out the first time; I leaned heavily on the
   type checker to guide me & then simplified what I had come-up with.
   -}
tryMkHeaderName buf@(b :: bs) = 
  case all (\x => decEq (isTokenByte x) True) buf of
  Yes pf_is_tok => Just $ mkHeaderName (b :: bs)
  No _ => Nothing

{- Cool, cool. But this all just lets us build HeaderName instances
   from lists of Bits8. That's useful when, say, we're reading octets
   off the wire (i.e. while parsing requests), but not terribly useful
   when we're *forming* them. -}

{- This all seems rather crude, but since `ord` is a primitive, I
   don't think Idris can "see" inside of its implementation to prove
   what I know is true. -}
tokenCharGivesTokenBits : isTokenChar c === True -> 
                          isTokenByte (believe_me $ ord c) === True
tokenCharGivesTokenBits = believe_me

{- Given a Char known to be a token constituent, return the
   corresponding octet, together with a proof that that octet remains
   a token constituent. -}
fromTokenChar : (c : Char) ->
                {auto 0 is_tok : isTokenChar c === True} ->
                DPair Bits8 (\b => isTokenByte b === True)
fromTokenChar c {is_tok} = MkDPair (believe_me $ ord c) 
                                   (tokenCharGivesTokenBits (believe_me $ ord c))

||| Given a non-empty list of Chars that are token constituents, return
||| a list of equivalent Bits8s (containing their ASCII codes) along with 
||| two proof terms: one for the proposition that the returned list is
||| non-nil, and a second for the proposition that they are all token
||| constituents.
{- I'm at the point where I can't tell whether I've finally grasped
   dependently-typed programming, or have gone off down the garden
   path. This is the problem: below, I want to take a List of Char,
   convert it to a List of Bits8, and then call MkHeaderName. In order
   to make that call, I'm going to need to, implicitly or explicitly,
   provide some proof terms. The only way I can see to get them is to
   have them returned from the conversion function. Namely, this
   function: -}
bits8FromTokenChars : (str : List Char) ->
                      {auto 0 prf0 : NonEmpty str} ->
                      {auto prf1 : All (\c => isTokenChar c === True) str} ->
                      {- I was familiar with this from Coq (IIRC, it's
                         called `SumBool` or some such), but it took a
                         little research to figure-out how to represent
                         this in Idris. The key is a dependent pair, where
                         the second element is conjunction represented by a
                         Pair of propositions. -}
                      DPair (List Bits8)
                            (\ls => (Pair (NonEmpty ls) 
                                          (All (\b => isTokenByte b === True) ls)))
bits8FromTokenChars (c :: []) {prf0 = IsNonEmpty} {prf1 = pf_c :: Nil} = 
  let pr = fromTokenChar c
  in MkDPair [(fst pr)] (IsNonEmpty, (snd pr) :: Nil)
bits8FromTokenChars (c :: cs@(c1 :: c1s)) {prf0 = IsNonEmpty} {prf1 = prf_c :: prf_cs} = 
  let pr = fromTokenChar c
      rest = bits8FromTokenChars cs
  in MkDPair ((fst pr) :: (fst rest)) (IsNonEmpty, (snd pr) :: (snd (snd rest)))

||| Given a non-empty List of Char that are token consituents, return a
||| HeaderName instance
{- I suspect this function can be elided; I'm just building toward an
   implementation for `String` one step at a time. -}
public export
mkHeaderNameChars : (str : List Char) ->
                    {auto not_nil : NonEmpty str} ->
                    {auto is_tok : All (\c => isTokenChar c === True) str} ->
                    HeaderName
mkHeaderNameChars str {not_nil} {is_tok} = 
  {- Alright-- I *could* just re-implement the logic in MkHeaderName
     here, but I'd like to re-use that; that is, I want to call
     MkHeaderName. That means I need:
     
         - a List of Bits8
         - a proof term for the fact that that list is not empty
         - a proof term for the fact that every element of that list
           is a token byte
           
    Fortunately, I have something to work with: not_nil & is_tok.
    Hmph. Alrigh. Let's see. 
    
    I want to build a function that will take what I've got & return
    not only a List of Bits8, but the proof terms I need: -}
  let bits = bits8FromTokenChars str
  {- At this point, we have:
  
     bits : DPair (List Bits8)
                  (\ls => (Pair (NonEmpty ls) 
                                (All (\b => isTokenByte b === True) ls)))
                                
     regrettably, if I destructure the outer (dependent) pair into
     more mnemonic names, Idris can't "see" that they apply to the
     list; hence all the `fst`s and `snd`s. -}
  in mkHeaderName (fst bits) {not_nil = (fst (snd bits))} {is_tok = (snd (snd bits))}

||| Given an arbitrary list of Char, return a HeaderName instance if
||| the form a valid header name
public export
tryMkHeaderNameChars : (str : List Char) -> Maybe HeaderName
tryMkHeaderNameChars [] = Nothing
tryMkHeaderNameChars str@(c :: cs) = 
  case all (\x => decEq (isTokenChar x) True) str of
  Yes pf_is_tok => Just $ mkHeaderNameChars (c :: cs)
  No _ => Nothing

public export
0 NonEmptyStr : String -> Type
NonEmptyStr = Str NonEmpty

||| Given a non-empty String made-up of token consituents, return a
||| HeaderName instance
public export
mkHeaderNameStr : (str : String) ->
                  {auto not_empty : NonEmptyStr str} ->
                  {auto is_tok : Str (All (\c => isTokenChar c === True)) str} ->
                  HeaderName
mkHeaderNameStr str {not_empty = (HoldsOn pf_not_nil)} {is_tok = HoldsOn pf_all} = 
  mkHeaderNameChars (unpack str) 

-- Again, how is this not available in the stdlib? Am I missing something?
StrConsNotNil : {c : Char} -> 
                {cs : String} -> 
                On NonEmpty Prelude.Types.unpack (strCons c cs)
StrConsNotNil {c} {cs} = believe_me (strCons c cs)

||| Given an arbitrary String, return a HeaderName instance if the string
||| forms a valid header name
public export
tryMkHeaderNameStr : (str : String) -> Maybe HeaderName
tryMkHeaderNameStr str with (strM str)
  tryMkHeaderNameStr "" | StrNil = Nothing
  tryMkHeaderNameStr str@(strCons c cs) | StrCons c cs = 
    case all (\x => decEq (isTokenChar x) True) (unpack (strCons c cs)) of
    Yes pf_is_tok => 
      Just $ mkHeaderNameStr (strCons c cs) {not_empty = StrConsNotNil}
    No _ => Nothing

-- ======================================================================
--                          Header Values
-- ======================================================================

public export
isValueChar : Char -> Bool
isValueChar c = (c >= '\32' && c /= '\127') || c == '\9' -- 👈 HTAB
  
||| Return True if the given byte is a valid header value constituent
public export
isValueByte : Bits8 -> Bool
isValueByte = isValueChar . chr . cast
  
||| An assertion that all octets in a List of Bits8 are token
||| constituents (empty header values, while odd, are technically
||| legal)
public export
Value : List Bits8 -> Type
Value = All (\b => isValueByte b === True)

||| An assertion that all Chars in a String are token
||| constituents (empty header values, while odd, are technically
||| legal)
public export
ValueStr : List Char -> Type
ValueStr = All (\b => isValueChar b === True)

||| RFC 9110-compliant header value
public export
record RawHeaderValue where
  constructor MkRawHeaderValue
  value : List Bits8
  {auto 0 prf : Value value}

%runElab derive "RawHeaderValue" [Show, Eq]

public export
tryMkRawHeaderValue : List Bits8 -> Maybe RawHeaderValue
tryMkRawHeaderValue buf = 
  case all (\b => decEq (isValueByte b) True) buf of
       Yes pf => Just $ MkRawHeaderValue buf
       No _ => Nothing

valueCharGivesValueBits : isValueChar c === True -> 
                          isValueByte (believe_me $ ord c) === True
valueCharGivesValueBits = believe_me

{- Given a Char known to be a value constituent, return the
   corresponding octet, together with a proof that that octet remains
   a value constituent. -}
fromValueChar : (c : Char) ->
                {auto 0 is_tok : isValueChar c === True} ->
                DPair Bits8 (\b => isValueByte b === True)
fromValueChar c {is_tok} = MkDPair (believe_me $ ord c) 
                                   (valueCharGivesValueBits (believe_me $ ord c))

bits8FromValueChars : (str : List Char) ->
                      {auto 0 is_value : All (\c => isValueChar c === True) str} ->
                      DPair (List Bits8)
                            (\ls => (All (\b => isValueByte b === True) ls))
bits8FromValueChars [] {is_value = []} = ([] ** [])
bits8FromValueChars (c :: cs) {is_value = (pf_c :: pf_cs)} = 
  let (b ** pf_b) = fromValueChar c
      (bs ** pf_bs) = bits8FromValueChars cs
  in ((b :: bs) ** (pf_b :: pf_bs))

public export
mkRawHeaderValueChars : (str : List Char) ->
                        {auto 0 is_value : All (\c => isValueChar c === True) str} ->
                        RawHeaderValue
mkRawHeaderValueChars [] = MkRawHeaderValue []
mkRawHeaderValueChars (c :: cs) = 
  let (bs ** pf_bs) = bits8FromValueChars (c :: cs)
  in MkRawHeaderValue bs

public export
mkRawHeaderValueStr : (str : String) -> 
                      {auto 0 is_value : (Str ValueStr) str} ->
                      RawHeaderValue
mkRawHeaderValueStr str {is_value = HoldsOn pf_is_value} = 
  mkRawHeaderValueChars (unpack str) {is_value = pf_is_value}

public export
tryMkRawHeaderValueStr : (str : String) -> Maybe RawHeaderValue
tryMkRawHeaderValueStr str = 
  case all (\x => decEq (isValueChar x) True) (unpack str) of
  Yes pf_is_val => Just $ mkRawHeaderValueStr str
  No _ => Nothing

tryParsePositiveBytes : List Bits8 -> Maybe Nat
tryParsePositiveBytes buf = parsePositive $ pack $ map (chr . cast) buf

-- ======================================================================
--                            Hostname
-- ======================================================================

{- The grammar for hosts & ports:

   ```text
   Host = host [ ":" port ]
   port = *DIGIT
  
   host        = IP-literal | IPv4address | reg-name
   IP-literal  = "[" ( IPv6address | IPvFuture  ) "]"
   IPvFuture   = "v" 1*HEXDIG "." 1*( unreserved | sub-delims | ":" )
   IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet
   dec-octet   = DIGIT                 ; 0-9
               | %x31-39 DIGIT         ; 10-99
               | "1" 2DIGIT            ; 100-199
               | "2" %x30-34 DIGIT     ; 200-249
               | "25" %x30-35          ; 250-255

   reg-name    = *( unreserved | pct-encoded | sub-delims )
   unreserved  = ALPHA | DIGIT | "-" | "." | "_" | "~"
   pct-encoded = "%" HEXDIG HEXDIG
   sub-delims  = "!" | "$" | "&" | "'" | "(" | ")"
                   | "*" | "+" | "," | ";" | "="
   ```
   
   This implementation will only support hosts given as IPv4 addresses
   or `reg-name`s. -}

||| Return True if the given Char is one of 0..9
public export -- [1]
isDigitChar : Char -> Bool
isDigitChar c = c >= '\x30' && c <= '\x39'

public export -- [1]
isDigitByte : Bits8 -> Bool
isDigitByte = isDigitChar . chr . cast

||| Return True if the given Char is one of 0..9 or a..f
isHexChar : Char -> Bool
isHexChar c = isDigitChar c                ||
              (c >= '\x61' && c <= '\x66') ||
              (c >= '\x41' && c <= '\x46')
              
isHexByte : Bits8 -> Bool
isHexByte = isHexChar . chr . cast

||| Return True if the given Char is either unreserved for a sub-delimiter
public export -- [1]
isUnreservedOrSubDelim : Char -> Bool
isUnreservedOrSubDelim '-'  = True
isUnreservedOrSubDelim '.'  = True
isUnreservedOrSubDelim '_'  = True
isUnreservedOrSubDelim '~'  = True
isUnreservedOrSubDelim '!'  = True
isUnreservedOrSubDelim '$'  = True
isUnreservedOrSubDelim '&'  = True
isUnreservedOrSubDelim '\'' = True
isUnreservedOrSubDelim '('  = True
isUnreservedOrSubDelim ')'  = True
isUnreservedOrSubDelim '*'  = True
isUnreservedOrSubDelim '+'  = True
isUnreservedOrSubDelim ','  = True
isUnreservedOrSubDelim ';'  = True
isUnreservedOrSubDelim '='  = True
isUnreservedOrSubDelim c    = (c >= '\x30' && c <= '\x39') ||
                              (c >= '\x61' && c <= '\x7a') ||
                              (c >= '\x41' && c <= '\x5a')

||| Return True if the argument is a valid "IPv4address" or "reg-name"
||| component of the hostname portion of a URI (i.e. no port)
public export -- [1]
isHostChars : List Char -> Bool
isHostChars [] = True
isHostChars ('%' :: []) = False
isHostChars ('%' :: (c :: [])) = False
isHostChars ('%' :: (c1 :: (c2 :: cs))) = 
  isHexChar c1 && isHexChar c2 && isHostChars cs
isHostChars (c :: cs) = isUnreservedOrSubDelim c && isHostChars cs

public export
isHostBytes : List Bits8 -> Bool
isHostBytes = isHostChars . map (chr . cast)

||| Take a list of octets, interpret them as ASCII, and attempt to
||| parse an integer value. Demand that the list be non-empty; we
||| want to distinguish between '0' and "not there".
public export -- [1]
parseInteger : (ls : List Bits8) ->
               {auto 0 _ : NonEmpty ls} ->
               {auto 0 _ : All (\b => isDigitByte b === True) ls} ->
               Integer
parseInteger ls = foldl (\acc => \c => acc * 10 + cast (c - 0x30)) 0 ls

{- Now wrap that implementation in one that can fail at runtime.
   Delegate overflow checking to a higher level. -}
public export -- [1]
tryParseInteger : (ls : List Bits8) ->
                    Maybe Integer
tryParseInteger [] = Nothing
tryParseInteger (x :: xs) = case all (\x => decEq (isDigitByte x) True) (x :: xs) of
                                 Yes pf_are_digits => Just $ parseInteger (x :: xs)
                                 No _ => Nothing
                              
{- Now, finally, do the range-checking:-}
public export -- [1]
tryParseBits16 : (ls : List Bits8) -> Maybe Bits16
tryParseBits16 ls = case tryParseInteger ls of
                         Nothing => Nothing
                         Just n => if n < 65536
                                   then Just $ cast n
                                   else Nothing

public export
record Hostname where
  constructor MkHostname
  host : List Bits8
  port : Maybe Bits16
  {- This works because I can express the syntax of the hostname
     portion in a function, then "hoist" it up to the type level: -}
  {auto 0 prf : isHostBytes host === True}

%runElab derive "Hostname" [Show]

||| Attempt to parse a Hostname from a buffer of octets
public export
tryParseHostname : List Bits8 -> Maybe Hostname
tryParseHostname buf = 
  let (before, and_after) = break (\b => b == 0x3a) buf -- 👈 ':'
      eq = decEq (isHostBytes before) True
  in case and_after of
     [] => case eq of
                Yes witness => Just $ MkHostname before Nothing
                No _ => Nothing
     (_ :: []) => Nothing -- Ends in ':'-- illegal
     (_ :: b :: bs) => case tryParseBits16 (b :: bs) of
                            Nothing => Nothing
                            Just port => case eq of
                                         Yes witness => Just $ MkHostname before (Just port)
                                         No _ => Nothing

public export -- [1]
maybeMkHostnameChars : List Char -> Maybe Hostname
maybeMkHostnameChars cs = tryParseHostname $ map (cast . ord) cs

public export -- [1]
mkHostnameChars : (buf : List Char) ->
                  {auto 0 parses : IsJust (maybeMkHostnameChars buf)} ->
                  Hostname
mkHostnameChars buf with (maybeMkHostnameChars buf)
  mkHostnameChars _ | Just h = h
  mkHostnameChars _ | Nothing impossible

public export
tryMkHostnameStr : (str : String) -> Maybe Hostname
tryMkHostnameStr = maybeMkHostnameChars . unpack

public export
mkHostnameStr : (str : String) -> 
                {auto 0 parses : IsJust (tryMkHostnameStr str)} ->
                Hostname
mkHostnameStr str with (tryMkHostnameStr str)
  mkHostnameStr _ | Just h = h
  mkHostnameStr _ | Nothing impossible

{- [1] This is regrettable; without making these public, callers can't
   find the necessary proofs. -}

-- ======================================================================
--                    A Dependently-Typed Header Map
-- ======================================================================

public export
headerValueType : HeaderName -> Type
headerValueType Host = Hostname
headerValueType ContentLength = Nat
headerValueType _ = RawHeaderValue

trimL : List Bits8 -> List Bits8
trimL [] = []
trimL (x :: xs) = case x of
                       9 => trimL xs
                       32 => trimL xs
                       _ => x :: xs
                       
trimR : List Bits8 -> List Bits8
trimR buf with (snocList buf)
  trimR [] | Empty = []
  trimR (xs ++ [x]) | Snoc x xs sxs = 
    case x of 
         9 => trimR $ assert_smaller (xs ++ [x]) xs
         32 => trimR $ assert_smaller (xs ++ [x]) xs
         _ => xs ++ [x]

trim : List Bits8 -> List Bits8
trim = trimL . trimR

||| Parse a colon-delimited name/value pair
public export
parseNameValuePair : List Bits8 -> Maybe (DPair HeaderName (\h => headerValueType h))
{- OK, so this is awful. Laying it out to see if I can see a better
   way... -}
parseNameValuePair buf = 
  let (before, and_after) = break (\x => x == 58) buf
  in case and_after of
          [] => Nothing
          (x :: xs) => 
            case before of
                 [] => Nothing
                 (_ :: _) => 
                   case tryMkHeaderName $ trim before of
                        Nothing => Nothing
                        Just Host => case tryParseHostname (trim xs) of
                                          Nothing => Nothing
                                          Just hostname => Just $ MkDPair Host hostname
                        Just ContentLength => case tryParsePositiveBytes (trim xs) of
                                                   Nothing => Nothing
                                                   Just n => Just $ MkDPair ContentLength n
                        Just (CustomHeader name) => 
                          case tryMkRawHeaderValue (trim xs) of
                               Nothing => Nothing
                               Just val => Just $ MkDPair (CustomHeader name) val

{- The plan here is to implement the map as a 

   List (h : HeaderName ** List1 (headerValueType h)
   
   in which HeaderName instances that compare equal via (==) are
   considered "the same". The first thing I'm going to need to do
   is claim a lemma: -}

||| Map of `HeaderName`s to corresponding header values
|||
||| Lookup is done by case-insensitive comparison.
public export
HeaderMap : Type
HeaderMap = List $ DPair HeaderName (\h => List1 (headerValueType h))

public export
Show (DPair HeaderName (\h => List1 (headerValueType h))) where
  show (h ** lst) with (headerValueType h)
    show (h ** lst) | Hostname = (show h) ++ ": " ++ (show lst)
    show (h ** lst) | Nat = (show h) ++ ": " ++ (show lst)
    show (h ** lst) | _ = (show h) ++ ": <raw header values>"

||| Convenience variable giving an empty HeaderMap
public export
empty : HeaderMap
empty = []

eqNoCaseGivesSameHeaderType : {x : HeaderName} ->
                              {y : HeaderName} ->
                              ((x == y) === True) -> 
                              headerValueType x = headerValueType y
{- I can't prove this, of course, because this isn't expressed in the
   type system. In fact, this is really dangerous because it's truth
   depends on consumers of this module *not* being allowed to create
   `CustomHeader` instances with strings like "HoSt", e.g. -}
eqNoCaseGivesSameHeaderType = believe_me

findPrec : (name : HeaderName) ->
           (hmap : HeaderMap) ->
           Maybe $ DPair (DPair HeaderName (\h => List1 (headerValueType h)))
                         (\h => (h.fst == name) === True)
findPrec name [] = Nothing
findPrec name ((h ** hs) :: xs) = 
  case decEq (h == name) True of
  Yes witness => Just $ MkDPair (h ** hs) witness
  No _ => findPrec name xs

||| Lookup the value(s) associated with a header
public export
lookup : HeaderMap -> (name : HeaderName) -> List (headerValueType name)
lookup hmap name = 
  case findPrec name hmap of
       Nothing => []
       Just ((key ** lst) ** witness) => 
         {- Ah... the joys of dependently-typed programming. I *need* a 
            `List1 (headerValueTYpe name)`, but I *have* a 
            `List1 (headerValueType key)`. Now, we know that name == key,
            and we've got a proof term for that proposition, so we use
            `replace`: 

            replace: {0 p : _ -> Type} -> (0 _ : x = y) -> (1 _ : p x) -> p y
                        -------------        ---------        -------     ---
                               |                |                |         |
          p = \a => List1 a <--+                |                |         |
            witness : (key == name) === True <--+                |         |
            => eqNoCaseGivesSameHeaderType witness :             |         |
               headerValueType key = headerValueType name        |         |
               x = headerValueType key => p x = List1 key <------+         |
                 y = headerValueType name => p x = List1 name <------------+

           -}                    
         forget $ replace {p = \a => List1 a} (eqNoCaseGivesSameHeaderType witness) lst

||| Insert a header into a HeaderMap
public export
insert : HeaderMap -> (name : HeaderName) -> (headerValueType name) -> HeaderMap
insert hmap name value =
  case findPrec name hmap of
  Nothing => ((name ** (value ::: [])) :: hmap)
  Just ((h ** old_vals) ** pf) => 
    let pf_hvt_same = sym $ eqNoCaseGivesSameHeaderType pf
        {- x is `headerValueType name` and y is `hederValueType h`.
           In `pf_hvt_same` I have a proof term for `x = y`.
           Let p be \k => k. 
           Then `p x` is just `headerValueType name` -}
        new_value = replace {p = \k => k} pf_hvt_same value
    in (h ** (new_value ::: [])) ::
      (deleteBy (\a, pr => a == (fst pr)) name hmap)

||| Append a header in a HeaderMap
public export
append : HeaderMap -> (name : HeaderName) -> (headerValueType name) -> HeaderMap
append hmap name value =
  case findPrec name hmap of
    Nothing => ((name ** (value ::: [])) :: hmap)
    Just ((h ** old_vals) ** pf)  =>
      let pf_hvt_same = sym $ eqNoCaseGivesSameHeaderType pf
          new_value = replace {p = \k => k} pf_hvt_same value
      in (h ** (new_value ::: (forget old_vals))) ::
        (deleteBy (\a, pr => a == (fst pr)) name hmap)

tryAdd : (HeaderMap -> (name : HeaderName) -> (headerValueType name) -> HeaderMap) -> 
         HeaderMap -> 
         HeaderName -> 
         String -> 
         Maybe HeaderMap
tryAdd f hmap Host str = case tryMkHostnameStr str of
                              Nothing => Nothing
                              Just h => Just $ f hmap Host h
tryAdd f hmap ContentLength str = case parsePositive str of
                                       Nothing => Nothing
                                       Just n => Just $ f hmap ContentLength n
tryAdd f hmap (CustomHeader x) str = case tryMkRawHeaderValueStr str of
                                          Nothing => Nothing
                                          Just raw => Just $ f hmap (CustomHeader x) raw

{- Later: implement `insert` & `append`: versions of these two that take
   auto implicit proof terms, as well. -}

public export
tryInsert : HeaderMap -> HeaderName -> String -> Maybe HeaderMap
tryInsert hmap h str = tryAdd insert hmap h str

public export
tryInsertS : HeaderMap -> String -> String -> Maybe HeaderMap
tryInsertS hmap name value = case tryMkHeaderNameStr name of
                                Nothing => Nothing
                                Just h => tryInsert hmap h value
public export
tryAppend : HeaderMap -> HeaderName -> String -> Maybe HeaderMap
tryAppend hmap h str = tryAdd append hmap h str

public export
tryAppendS : HeaderMap -> String -> String -> Maybe HeaderMap
tryAppendS hmap name value = case tryMkHeaderNameStr name of
                                Nothing => Nothing
                                Just h => tryAppend hmap h value
