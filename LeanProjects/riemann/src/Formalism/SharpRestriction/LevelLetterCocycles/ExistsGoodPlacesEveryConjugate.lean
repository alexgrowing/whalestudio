import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.VKEqOfFrac
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LinearIndependentSmulOfNeZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.MainNotions.N.TwAll

section Conj

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem psiAt_side_zpow {Γ A : Type} [Group Γ] [CommGroup A] (b b' : Bool) (ψ : Γ →* A) (a : ℤ) :
    ∃ a' : ℤ, a'.natAbs = a.natAbs ∧ Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b' (ψ ^ a) = Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (ψ ^ a') := by
  cases b <;> cases b'
  · exact ⟨a, rfl, rfl⟩
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · refine ⟨-a, Int.natAbs_neg a, ?_⟩
    simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, zpow_neg]
  · exact ⟨a, rfl, rfl⟩

end Conj

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions

open Formalism.MainNotions.N.TwAll

def TwGoodAll (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) → TwGoodOne D I i b Q k' (ψ ^ a)

theorem TwGoodAll.one {D : D7} {I : TwIn D} {i : D.ntw.Tw} {b : Bool} {Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ} (h : TwGoodAll D I i b Q k' ψ) : TwGoodOne D I i b Q k' ψ := by
  have := h 1 (by simp)
  rwa [zpow_one] at this

theorem TwGoodAll.side {D : D7} {I : TwIn D} {i : D.ntw.Tw} {b : Bool} {Q : Finset (PlE D.host)} {k' : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ} (h : TwGoodAll D I i b Q k' ψ) (b' : Bool) :
    TwGoodAll D I i b' Q k' ψ := by
  intro a ha
  obtain ⟨a', h1, h2⟩ := psiAt_side_zpow b b' ψ a
  unfold TwGoodOne
  rw [h2]
  exact h a' (by rw [h1]; exact ha)

def rawPack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D := ⟨C.twI w, C.Q w, C.k' w, C.psi' w⟩

def TwConjAllAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w w', TwistedAt D w → TwistedAt D w' → C.twI w' = C.twI w →
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) ∧
      rawPack C w' = ⟨C.twI w, C.Q w, C.k' w, C.psi' w ^ a⟩

def IntegralHeckeEveryConjugate (D : D7) (bkP : BlochKatoReduction.BK D) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.pin bkP) i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp E i j b (IntegralHeckeForms.SgJ D.nexp E i j b)) →
    ∀ S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b),
      (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (IntegralHeckeForms.SgJ D.nexp E i j b) (S j b)) →
    ∀ A : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ),
      ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) →
        IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.pin bkP) E N0 i eps' S A Q k' (ψ' ^ a)

def TwADOne (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  BlochKatoReduction.Gen.partAT (BlochKatoReduction.bk0 D) i Q k' (BlochKatoReduction.Gen.psiAt b ψ) (twEps D i) ∧
    BlochKatoReduction.Gen.partD i Q k' (BlochKatoReduction.Gen.psiAt b ψ) (twEps D i)

def TwADAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → TwADOne D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

end Formalism.MainNotions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Kill

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

end Kill

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section C6

variable {D : D7} (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

def SelTie (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i →
    ∀ π ∈ D.nd.Zgood i, ∃ s : D.ntw.Sig (C.twI (D.nd.w i)),
      Formalism.MainNotions.BlochKatoReduction.Gen.goodS (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s ∧
      (Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
                (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i))) ≠ ⊤ → Br.sFin D.loc D.nbr i (ρ i) π) ∧
      ENNReal.ofReal (Br.sPi D.loc D.nbr i (ρ i) π : ℝ) ≤
        Formalism.MainNotions.BlochKatoReduction.Gen.sLen (Formalism.MainNotions.BlochKatoReduction.bk0 D) (C.twI (D.nd.w i)) s (C.k' (D.nd.w i)) (C.Q (D.nd.w i))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt (D.ntw.side _ s) (psiW C (D.nd.w i)))

def CondTie (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → ∀ v ∈ D.nd.Q i,
    ((lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) ≤
      Formalism.MainNotions.BlochKatoReduction.Gen.tameVal (D.ntw.l (C.twI (D.nd.w i))) (psiW C (D.nd.w i)) (D.nd.plOm.1 v)

end C6

end Formalism.MainNotions.N.KillingConditions

namespace Formalism.MainNotions.LatticeVariant

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

variable (Y) in
open Classical in

def AdmRunEveryConjugate (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A0 : Finset (PlE D.host),
  ∀ (J : ℕ) (sd : Fin J → Bool) (h : Fin J → ∀ Q M, LamO X i Q M) (v : Fin J → ℝ),
    (∀ x, 0 ≤ v x) → (∀ x, Good Y i A0 (h x) (v x)) →
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (M : ℕ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M) ∧
      ∃ ep : Fin J → ℝ, (∀ x, 0 ≤ ep x) ∧ ∑ x, ep x ≤ eps' ∧
      ∀ a : ℤ, a.natAbs.Coprime (X.l i) →
        PsiOk i A0 Q k' (ψ' ^ a) ∧ (ψ' ^ a).comp (X.art i Q) = (χ ^ a).comp (Y.delU i Q M) ∧
        partA bkP i Q k' (ψ' ^ a) eps' ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps' ∧
        ∀ x, evA i Q M k' (psiAt (sd x) (χ ^ a)) (h x Q M) ≠ 0 ∧
          nval (X.Ok i k') (X.l i) (evA i Q M k' (psiAt (sd x) (χ ^ a)) (h x Q M)) ≤ v x + ep x

variable (Y) in

def admissibleIndexBoundAllPowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : Formalism.MainNotions.IntegralHeckeForms.RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, Formalism.MainNotions.IntegralHeckeForms.ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      ∀ a : ℤ, a.natAbs.Coprime (X.l i) →
        PsiOk i A0 Q k' (ψ' ^ a) ∧ partAT bkP i Q k' (ψ' ^ a) eps' ∧
        partC N0 i Q k' (ψ' ^ a) eps' ∧ partD i Q k' (ψ' ^ a) eps' ∧
        Formalism.MainNotions.IntegralHeckeForms.partAB Y i F Q k' (ψ' ^ a) eps'

end All

end Formalism.MainNotions.LatticeVariant

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

section All

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} {Y : NExp D.R D.host D.what₂ D.LL0 N X}

variable (Y) in

def goodTwistExistsAllCoprimePowers (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
    ∀ a : ℤ, a.natAbs.Coprime (X.l i) → GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

end All

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

end Formalism.MainNotions

namespace Formalism.MainNotions.N.TwAll

open Formalism.MainNotions.BlochKatoReduction.Gen (nval)

theorem nval_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ) : nval O l 0 = 0 := by
  unfold nval
  simp

section Tame

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}

end Tame

end Formalism.MainNotions.N.TwAll

namespace Formalism.MainNotions.N.KillingConditions

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.N.TwAll

section DensityAveraging

variable {D : D7}

def TameCyc (C : NChoice D) : Prop :=
  ∀ i : D.nd.Loc, Formalism.MainNotions.TwistedPlaces.TwLoc D i → ∀ v ∈ D.nd.Q i, ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ m : ℤ, (C.psi' (D.nd.w i)).comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) σ =
      ((C.psi' (D.nd.w i)).comp (D.ntw.art (C.twI (D.nd.w i)) (C.Q (D.nd.w i))) (D.nd.gam0 i v)) ^ m

end DensityAveraging

end Formalism.MainNotions.N.KillingConditions

end
