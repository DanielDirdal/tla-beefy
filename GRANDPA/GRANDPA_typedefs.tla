-------------------- MODULE GRANDPA_typedefs ---------------------------
(*
 Type definitions:
 @typeAlias: voter = Str;
 @typeAlias: block = Str;
 @typeAlias: height = Int;
 @typeAlias: step = Str;
 @typeAlias: round = Int;

 @typeAlias: message = {
    voter: $voter,
    round: $round,
    block: $block,
    type: $step };
*)
GRANDPA_TypeAliases == TRUE

=============================================================================