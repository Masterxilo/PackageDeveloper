(* ::Package:: *)

(* Mathematica Package *)
(* Created by Mathematica Plugin for IntelliJ IDEA *)

(* :Title: PackageDeveloper *)
(* :Context: PackageDeveloper` *)
(* :Author: Paul *)
(* :Date: 2016-08-08 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: *)
(* :Copyright: (c) 2016 Paul *)
(* :Keywords: *)
(* :Discussion:
Contains various meta commands to make package development easier.
*)

(* TODO error checking
TODO support = definitions
TODO allow hiding internal operations such as destructuring of data if desired (easier to understand)

TODO don't force usage message for different internal variants: maybe separate internally? overhead!*)
(* Needs paul`paul`MessageAbort to be defined *)
BeginPackage["PackageDeveloper`"]

ClearAll["PackageDeveloper`*", "PackageDeveloper`Private`*"]

(* Usage messages *)
PublicSymbols::usage = "Wrapper for any symbols that will be public. Undefines all DownValueUsage such that DefinePublicFunction may be used
on the given symbols, not just RedefinePublicFunction."

DeclareDPrint::usage = "DeclareDPrint[] within the public or private
section of a package to define a DPrint function that works like Print
after EnableDPrint[] has been called, otherwise is left unevaluated."

DefinePublicFunction::usage = "DeclarePublicFunction[f[args] /; cond, \"usage\", body]

Use like := to declare public functions.
All Messages and Exceptions that are generated are caught and translated to a
package specific message and error value, by default $Failed.

Also defines a 'wrong argument specification' handler that catches all calls with unknown arguments.

TODO this could also set the usage message and documentation
TODO this could also handle syntax hints for 'too many argument' type situations."

MessageAssert::usage = "MessageAssert[condition, message, messageArguments...]
If condition is false, throw an exception and generate the given message."

DownValueUsage::usage = "Extended usage information for a specific down value (HoldPattern left hand side). Use in combination with
WhichDownValue"

RedefinePublicFunction::usage = "Same as define, but first clears the symbol and its DownValueUsage"

(* Error messages *)
(* We use ::msg only the initial name of the message is displayed: make that readable *)
(* final `` is for user's error message/hint (if any), \n `` is for paul`StackTrace[] *)
IllegalContext::msg = "Illegal context of definition symbol `` in definition ``.\n``"
AlreadyDefined::msg = "``. Or DownValueUsage was not properly cleaned: Are PublicSymbols[] set? Did you mean *Re*definePublicFunction?\n``"
Undefined::msg = "``. Check argument count and definition conditions.\n``"
UnexpectedMessages::msg = "in `` when called like ``. There is a bug. ``\n``"
UnexpectedResultType::msg = "Expected result type `` got ``. ``\n``"
UncaughtException::msg = "``\n``"

Begin["`Private`"]

PublicSymbols[s___] := (
    (* Unset all DownValueUsage definitions *)
  (
    (* definition Without Condition*)
    UnsetMatching[
      (
        Verbatim[HoldPattern]@
            DownValueUsage@
                Verbatim[Verbatim]@Verbatim[HoldPattern]@HoldPattern@#[___] (* we only care about this # *)
      )
    ];
    (* With Condition*)
    UnsetMatching[
      (
        Verbatim[HoldPattern]@
            DownValueUsage@
                Verbatim[Verbatim]@Verbatim[HoldPattern]@HoldPattern@Verbatim[Condition][#[___],_] (* we only care about this # *)
      )
    ];
  )& ~Scan~ {s}

)



(*TODO SameQOrUndefined should display both sides once evaluated, once not*)
SameQOrUndefined[a_, a_] := True;
Format[SameQOrUndefined[a_,b_], StandardForm] := Row@{a,"===",b};
SameQOrUndefined /: Format[SameQOrUndefined@@{a_,b_}, StandardForm] := Row@{a,"===",b};

MessageAssert~SetAttributes~HoldAll
MessageAssert[e_, message_MessageName, args___] := Assert[e,StringTemplate[message][args]] (* todo format args differently, e.g. using input form*)
MessageAssert[e_, args___] := Assert[e, args]

DefinePublicFunction~SetAttributes~HoldAll

CountArgumentsFromSyntaxInformation[s_Symbol] :=
    LengthOrMissing[SyntaxInformation[s]~Lookup~"ArgumentsPattern"];

SyntaxInformationArgumentPatternForFixedArgumentCountRange[
  min_Integer, max_Integer] /; min <= max :=
    Table[_, min]~Join~Table[_., max - min]


CatchMessagesAndTypeCheck~SetAttributes~HoldAll
CatchMessagesAndTypeCheck[body_, resultPattern_, error_] :=
    Check[
      With[{result = body}, If[Not[result~MatchQ~resultPattern], paul`MessageAbort[UnexpectedResultType::msg, resultPattern, HoldForm@result, error], result]]
      , paul`MessageAbort[UnexpectedMessages::msg, f, HoldForm@call, error]
    ]


(* -- Core --- *)
(*
Makes a definition, wrapping it in all handlers so as to catch uncaught things
(TODO consider aborting early instead -- or have the function declare what it can normally throw)
check return types, fail on messages generated on the inside etc.

TODO use runtime changeable functions for callbacks, instead of hardcoding the wrappers
*)
DefinePublicFunction[
  f_Symbol, (* tag with which the definition will be associated *)
  def_, (* actual definition, not yet evaluated*)
  args_List, (* arguments inside of definition *)
  cond : Null | _, (* condition, Null if none *)
  usage_String, (* ::usage message *)
  body_, (* definition *)
  resultPattern_ : _, (* return type spec *)
  error_: "" (* user message displayed on function error, e.g. telling about the likely cause, what to do next*)
] := (

  (* Create usage message *)
  MessageAssert[Context@f =!= "System`", IllegalContext::msg, Context@f, HoldForm@def];
  MessageAssert[Head@DownValueUsage@HoldPattern@def === DownValueUsage, AlreadyDefined::msg, HoldForm@def];

  (* usage message as expected by Mathematica front end for proper output formatting and recognition of variants
  (on the blue dropdown menu)
  TODO extract short parameter names *)
  DownValueUsage[Verbatim[HoldPattern@def]] = StringTemplate["\!\(\*RowBox[{\"``\", \"[\", ``, \"]\"}]\)`` ``"][
    ToString@f
    , StringRiffle[StringTemplate["StyleBox[\"``\", \"TI\"]"] /@ ToString /@ args, ",\",\","]
    , If[Hold@cond === Hold@Null,"", " /; "<>ToString@Unevaluated@cond]
    , usage
  ];

  MessageAssert[Head@DownValueUsage@HoldPattern@def =!= DownValueUsage, General::whatTheHeck];
  StringJoinToOrSet[f::usage, DownValueUsage@HoldPattern@def, StringRiffle -> "\n"];

  (* Extend syntaxInformation *)
  Module[{
    minmaxargc = MinMax@DeleteMissing@{CountArgumentsFromSyntaxInformation@f, Length@args}
  },
    SyntaxInformation[f] = {"ArgumentsPattern"->SyntaxInformationArgumentPatternForFixedArgumentCountRange@@minmaxargc};
  ];

  (* do the definition *)
  call : def := CatchMessagesAndTypeCheck[body, resultPattern, error];

  (* Do the undefined fallback definition, but only once and put it at the end of the list
  (if mathematica cannot order the patterns, this is the only way to ensure it is there) *)
  DownValues@f = DeleteCases[DownValues@f, HoldPattern[Verbatim@HoldPattern[a : f[___]] :> _]];
  DownValues@f~AppendTo~(HoldPattern[a : f[___]] :> (StackInhibit@Message[Undefined::msg, HoldForm@a, StackInhibit@paul`StackTrace[]]; Abort[]));

);

(* -- End of core --- *)

(* usability *)

DefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _, error_: ""] :=
    DefinePublicFunction[f, d, {args}, Null, usage, body,resultPattern,error]

DefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _, error_: ""] :=
    DefinePublicFunction[f, d, {args}, c, usage, body,resultPattern,error]

RedefinePublicFunction~SetAttributes~HoldAll
RedefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _, error_: ""] := (
    ClearAll[f];
    PublicSymbols[f];
    DefinePublicFunction[d, usage, body,resultPattern,error];
);

RedefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _, error_: ""] := (
  ClearAll[f];
  PublicSymbols[f];
  DefinePublicFunction[d, usage, body,resultPattern,error];
);

(* errors *)
a:DefinePublicFunction[___] := (Message[Undefined::msg, HoldForm@a, StackInhibit@stackTrace[]];Abort[]);
a:RedefinePublicFunction[___] := (Message[Undefined::msg, HoldForm@a, StackInhibit@stackTrace[]];Abort[]);


End[] (* `Private` *)

EndPackage[]
