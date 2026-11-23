import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def admissibleIndexBoundAllPowers (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

def goodTwistExistsAllCoprimePowers (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

def TwGoodAtAll (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧ ∀ a : ℤ, IsCoprime a (D.ntw.l (C.twI w) : ℤ) →
    TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w ^ a)

variable {Y} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

def Ball (i : X.Tw) (j : ℕ) (b : Bool) (B : ℝ) : Set (Y.Fm i j b) :=
  {f | f ∈ T.FmUr i j b ∧ ∀ y, ‖T.ev i j b f y‖ ≤ B}

def SupBdd : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ f ∈ T.FmUr i j b, ∃ B, f ∈ Ball T i j b B

def GKeeps : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b g, ∀ f ∈ Ball T i j b 1,
  Y.actG i j b g f ∈ Ball T i j b 1

def HkKeeps : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P → ∀ f ∈ Ball T i j b 1,
  Y.hkF i j b k P f ∈ Ball T i j b 1

def UnivBdd (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, ∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M,
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q → Disjoint Q (X.S0 i) → Disjoint Q (Y.lev i j b a) →
  ∃ Xi : DelQM D.host (X.l i) Q M →₀ Y.Fm i j b,
    Y.thU i j b Q M a = Xi.sum (fun δ f => f ⊗ₜ[X.O i] AddMonoidAlgebra.single δ (1 : X.O i)) ∧
    ∀ δ, Xi δ ∈ Fm0 Y i j b ∧ Xi δ ∈ Submodule.span (X.O i) (Ball T i j b ((X.l i : ℝ) ^ c))

def TypeKept (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k Q
  (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ → ∀ a ∈ E.Dat0 i j b,
    Y.thPsi i j b k Q ψ a ⊆ ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))

end GlobalTheory.TwAll
