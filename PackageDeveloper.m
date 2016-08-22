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

General::undefined = "`` is undefined. Check argument count and definition conditions. Stack: ``"

DownValueUsage::usage = "Extended usage information for a specific down value (HoldPattern left hand side). Use in combination with
WhichDownValue"

General::alreadyDefined = "`` is already defined (or DownValueUsage was not properly cleaned: Are PublicSymbols[] set?)"

MessageAssert::assertionFailed = "``. Generating message ``. Stack: ``. Extra Context: ``"

SameQOrUndefined

RedefinePublicFunction::usage = "Same as define, but first clears the symbol and its DownValueUsage"

General::unexpectedMessages = "Unexpected messages where generated. The function `` failed unbeknownst to it when called like ``. There is a bug"

General::unexpectedResultType = "Expected `` got ``"


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


MessageAssert[e_, message_MessageName, args___] := StackInhibit@If[!TrueQ@e
  ,
  (*
  Message[MessageAssert::assertionFailed, Rule[HoldForm@e, e], HoldForm@message, Most@Stack[], {(*$InputFileName, $Line doesn't work*)}];
  *)
  Message[message, args];
  Throw@{$Failed, MessageAssert, Rule[HoldForm@e, e], HoldForm@message, Rule[HoldForm@{args}, {args}]}
];

MessageAssert[e_, args___] := StackInhibit@If[!TrueQ@e
  ,
  Message[MessageAssert::assertionFailed, Rule[HoldForm@e, e], "<no message>", Most@Stack[], {}];
  Throw@{$Failed, MessageAssert, Rule[HoldForm@e, e], Rule[HoldForm@{args}, {args}]}
];

DefinePublicFunction~SetAttributes~HoldAll


CountArgumentsFromSyntaxInformation[s_Symbol] :=
    LengthOrMissing[SyntaxInformation[s]~Lookup~"ArgumentsPattern"];

SyntaxInformationArgumentPatternForFixedArgumentCountRange[
  min_Integer, max_Integer] /; min <= max :=
    Table[_, min]~Join~Table[_., max - min]

DefinePublicFunction[f_Symbol, def_, args_List, cond : Null | _, usage_String, body_, resultPattern_ : _] := (

  MessageAssert[Head@DownValueUsage@HoldPattern@def === DownValueUsage, General::alreadyDefined, HoldForm@def];

  DownValueUsage[Verbatim[HoldPattern@def]] = StringTemplate["``[\!\(\*StyleBox[\"``\", \"TI\"]\)]``\n\t``"][
    ToString@f
    , CommaRiffle[ToString /@ args]
    , If[Hold@cond === Hold@Null,"", " /; "<>ToString@Unevaluated@cond]
    , usage
  ];

  MessageAssert[Head@DownValueUsage@HoldPattern@def =!= DownValueUsage, General::whatTheHeck];


  StringJoinToOrSet[f::usage, DownValueUsage@HoldPattern@def, StringRiffle -> "\n"];

  call : def := StackComplete@Check[CatchAll[ (*StackComplete for debuggability, remove in release version *)

    {result=body}~With~(MessageAssert[result~MatchQ~resultPattern, General::unexpectedResultType, resultPattern, HoldForm@result]; result)

    , (Message[Throw::nocatch, ##];$Failed )&]
    , Message[General::unexpectedMessages, f, HoldForm@call];Throw@$Failed];

  Module[{
    minmaxargc = MinMax@DeleteMissing@{CountArgumentsFromSyntaxInformation@f, Length@args}
  },
    SyntaxInformation[f] = {"ArgumentsPattern"->SyntaxInformationArgumentPatternForFixedArgumentCountRange@@minmaxargc};
  ];

  DownValues@f = DeleteCases[DownValues@f, HoldPattern[Verbatim@HoldPattern[a : f[___]] :> _]];
  DownValues@f~AppendTo~(HoldPattern[a : f[___]] :> (StackInhibit@Message[General::undefined, HoldForm@a, Stack[]];Throw@$Failed));
);

DefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _] :=
    DefinePublicFunction[f, d, {args}, Null, usage, body,resultPattern]

DefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _] :=
    DefinePublicFunction[f, d, {args}, c, usage, body,resultPattern]

RedefinePublicFunction~SetAttributes~HoldAll
RedefinePublicFunction[d : f_Symbol[args___], usage_String, body_, resultPattern_ : _] := (
    ClearAll[f];
    PublicSymbols[f];
    DefinePublicFunction[d, usage, body,resultPattern];
);

RedefinePublicFunction[d : (f_Symbol[args___]~Verbatim[Condition]~c_), usage_String, body_, resultPattern_ : _] := (
  ClearAll[f];
  PublicSymbols[f];
  DefinePublicFunction[d, usage, body,resultPattern];
);

(* errors *)
a:DefinePublicFunction[___] := (Message[General::undefined, HoldForm@a, Stack[]];$Failed);
a:RedefinePublicFunction[___] := (Message[General::undefined, HoldForm@a, Stack[]];$Failed);


End[] (* `Private` *)

EndPackage[]
