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
BeginPackage["PackageDeveloper`", {"paul`"}]


ClearAll["PackageDeveloper`*", "PackageDeveloper`Private`*"]

PublicSymbols::usage = "Wrapper for any symbols that will be public."

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

DebugBreak::usage = "TODO Ideally, this starts the debugger (or only works when it is running)
and stops the execution right where we are.
Opening a Dialog[] and reporting where we are is a starting point."

BeginPackage2::usage = "Like BeginPackage, but anything declared within that is
not in DeclarePublicFunction is put in the `Private` namespace."


DownValueUsage::usage = "Extended usage information for a specific down value (HoldPattern left hand side). Use in combination with
WhichDownValue"


SameQOrUndefined

RedefinePublicFunction::usage = "Same as define, but first clears the symbol and its DownValueUsage"

General::undefined = "Undefined function call ``. Check argument count and definition conditions."

General::illegalContext = "Illegal context of definition symbol `` in definition ``."
General::alreadyDefined = "Already defined `` (or DownValueUsage was not properly cleaned: Are PublicSymbols[] set?). "


General::unexpectedMessages = "Unexpected messages generated in `` when called like ``. There is a bug. ``"
(*MessageAssert::assertionFailed = "``. Generating message ``. ``"*)
General::unexpectedResultType = "Expected result type `` got ``. ``"
Throw::nocatch = "Exception was not caught. ``"

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


MessageAssert~SetAttributes~HoldAll

(*TODO SameQOrUndefined should display both sides once evaluated, once not*)
SameQOrUndefined[a_, a_] := True;
Format[SameQOrUndefined[a_,b_], StandardForm] := Row@{a,"===",b};
SameQOrUndefined /: Format[SameQOrUndefined@@{a_,b_}, StandardForm] := Row@{a,"===",b};

MessageAssert[a_===b_, r___] := MessageAssert[SameQOrUndefined@@{a,b}, r];


MessageAssert[e_, message_MessageName, args___] := Assert[e,StringTemplate[message][args]] (* todo format args differently, e.g. using input form*)
(*StackInhibit@If[!TrueQ@e
  ,
  (*
  Message[MessageAssert::assertionFailed, Rule[HoldForm@e, e], HoldForm@message, Most@Stack[], {(*$InputFileName, $Line doesn't work*)}];
  *)
  Message[message, args];
  Abort[]
  (*Throw@{$Failed, MessageAssert, Rule[HoldForm@e, e], HoldForm@message, Rule[HoldForm@{args}, {args}]}*)
];
*)
MessageAssert[e_, args___] := Assert[e, args](*StackInhibit@If[!TrueQ@e
  ,
  Message[MessageAssert::assertionFailed, Rule[HoldForm@e, e], "<no message>", {}];
  (*Throw@{$Failed, MessageAssert, Rule[HoldForm@e, e], Rule[HoldForm@{args}, {args}]}*)
  Abort[]
];*)

DefinePublicFunction~SetAttributes~HoldAll


CountArgumentsFromSyntaxInformation[s_Symbol] :=
    LengthOrMissing[SyntaxInformation[s]~Lookup~"ArgumentsPattern"];

SyntaxInformationArgumentPatternForFixedArgumentCountRange[
  min_Integer, max_Integer] /; min <= max :=
    Table[_, min]~Join~Table[_., max - min]

(* -- core --- *)
(*
Makes a definition, wrapping it in all handlers so as to catch uncaught things
(TODO consider aborting early instead -- or have the function declare what it can normally throw)
check return types, fail on messages generated on the inside etc.

TODO use runtime changeable functions for callbacks, instead of hardcoding the wrappers
*)
DefinePublicFunction[f_Symbol, def_, args_List, cond : Null | _, usage_String, body_, resultPattern_ : _, error_: Null] := (

  MessageAssert[Context@f =!= "System`", General::illegalContext, Context@f, HoldForm@def];
  MessageAssert[Head@DownValueUsage@HoldPattern@def === DownValueUsage, General::alreadyDefined, HoldForm@def];

  DownValueUsage[Verbatim[HoldPattern@def]] = StringTemplate["\!\(\*RowBox[{\"``\", \"[\", ``, \"]\"}]\)`` ``"][
    ToString@f
    , StringRiffle[StringTemplate["StyleBox[\"``\", \"TI\"]"] /@ ToString /@ args, ",\",\","]
    , If[Hold@cond === Hold@Null,"", " /; "<>ToString@Unevaluated@cond]
    , usage
  ];

  MessageAssert[Head@DownValueUsage@HoldPattern@def =!= DownValueUsage, General::whatTheHeck];


  StringJoinToOrSet[f::usage, DownValueUsage@HoldPattern@def, StringRiffle -> "\n"];

  call : def := StackComplete@Check[CatchAll[ (*StackComplete for debuggability, remove in release version *)

    {result=body}~With~(
      MessageAssert[result~MatchQ~resultPattern, General::unexpectedResultType, resultPattern, HoldForm@result, error];
      result)

    , (Message[Throw::nocatch, Row@{##, error}]; Abort[])&]
    , Message[General::unexpectedMessages, f, HoldForm@call, error]; Abort[]];

  Module[{
    minmaxargc = MinMax@DeleteMissing@{CountArgumentsFromSyntaxInformation@f, Length@args}
  },
    SyntaxInformation[f] = {"ArgumentsPattern"->SyntaxInformationArgumentPatternForFixedArgumentCountRange@@minmaxargc};
  ];

  DownValues@f = DeleteCases[DownValues@f, HoldPattern[Verbatim@HoldPattern[a : f[___]] :> _]];
  DownValues@f~AppendTo~(HoldPattern[a : f[___]] :> (StackInhibit@Message[General::undefined, HoldForm@a]; Abort[]));
);

(* usability *)

DefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _, error_: Null] :=
    DefinePublicFunction[f, d, {args}, Null, usage, body,resultPattern,error]

DefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _, error_: Null] :=
    DefinePublicFunction[f, d, {args}, c, usage, body,resultPattern,error]

RedefinePublicFunction~SetAttributes~HoldAll
RedefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _, error_: Null] := (
    ClearAll[f];
    PublicSymbols[f];
    DefinePublicFunction[d, usage, body,resultPattern,error];
);

RedefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _, error_: Null] := (
  ClearAll[f];
  PublicSymbols[f];
  DefinePublicFunction[d, usage, body,resultPattern,error];
);

(* errors *)
a:DefinePublicFunction[___] := (Message[General::undefined, HoldForm@a];Abort[]);
a:RedefinePublicFunction[___] := (Message[General::undefined, HoldForm@a];Abort[]);


End[] (* `Private` *)

EndPackage[]
