import Formalism.LocalToGlobal.GlobalTheory.BlockActions.ArchimedeanSignatureMatchingOfTrivialBranchingSymm
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

def ClassMapInjective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    Function.Injective (D.fm u).til

def StabiliserMapBijective : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (_ : FormsTiedSym D u Ch chOf),
    ∀ c, Function.Bijective ((D.fm u).stabMap c)

def FormsCarriedToComplement : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → ∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC

def NormBoundAtInfinity : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u →
    ∀ (h : (D.fm u).PRat) (v : NumberField.InfinitePlace D.what₂.LL) (x : Vl D u D.R.m),
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
        ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re

def ClassMapPropertiesOfSymmetricForms : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf),
    Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → ClassMapInjectiveBijectiveNorms D u

theorem symmetric_clauses_of_four (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) (h3 : FormsCarriedToComplement) (h4 : NormBoundAtInfinity) : ClassMapPropertiesOfSymmetricForms :=
  fun D u Ch chOf Tf hL hB =>
    ⟨h1 D u Ch chOf Tf, h2 D u Ch chOf Tf, h3 D u Ch chOf Tf hL, h4 D u Ch chOf Tf hL hB⟩

theorem lowerMapTieSym_of (Tf : FormsTiedSym D u Ch chOf) (h : Formalism.L2.Rows.LowerMapTieS Tf) : LowerMapTieSym Tf := h

end Formalism.L2.GlobalTheoryTheory.Br
