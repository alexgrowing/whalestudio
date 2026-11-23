import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def resD (l : ℕ) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ) :
    DelQM D.host l Q M →+ DelQM D.host l Q' M where
  toFun f p := f ⟨p.1, h p.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def projA (i : X.Tw) {Q' Q : Finset (PlE D.host)} (h : Q' ⊆ Q) (M : ℕ) :
    LamO X i Q M →ₐ[X.O i] LamO X i Q' M :=
  AddMonoidAlgebra.mapDomainAlgHom (X.O i) (X.O i) (resD (X.l i) h M)

def augA (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : LamO X i Q M →ₐ[X.O i] X.O i :=
  AddMonoidAlgebra.lift (X.O i) (X.O i) (DelQM D.host (X.l i) Q M) 1

def evA (i : X.Tw) (Q : Finset (PlE D.host)) (M k : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) : LamO X i Q M →ₐ[X.O i] X.Ok i k :=
  AddMonoidAlgebra.lift (X.O i) (X.Ok i k) (DelQM D.host (X.l i) Q M) ((Units.coeHom (X.Ok i k)).comp χ)

def grp (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) (γ : DelQM D.host (X.l i) Q M) : LamO X i Q M :=
  AddMonoidAlgebra.single γ 1

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

structure RFam (i : X.Tw) where
  B : ∀ j b, Submodule (X.O i) (Y.Fm i j b)
  A : ∀ j b, Module.End (X.O i) (Y.Fm i j b)
  Sg : ∀ j b, Set (Y.Dat i j b)
  S : ∀ j b, Finset (Y.Dat i j b)
  kap : ∀ j b, Module.End (X.O i) (Y.Fm i j b)

variable {Y}

def RFam.Th {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) : Submodule (X.O i) (Y.Fm i j b) :=
  (Formalism.MainNotions.IntegralHeckeForms.Th Y i j b (F.Sg j b)).map (F.A j b)

def RFam.ThPsi {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  (Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i j b k Q ψ (F.Sg j b)).map ((F.A j b).baseChange (X.Ok i k))

def RFam.w {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ)
    (a : Y.Dat i j b) : Y.Fm i j b ⊗[X.O i] LamO X i Q M :=
  (F.A j b).rTensor _ (Y.thU i j b Q M a)

def RFam.VK {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) :
    Submodule (FractionRing (X.O i)) (Y.Fm i j b) :=
  Submodule.span (FractionRing (X.O i)) (F.B j b : Set (Y.Fm i j b))

def RFam.VKk {i : X.Tw} (F : RFam Y i) (j : ℕ) (b : Bool) (k : ℕ) :
    Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b) :=
  ((F.VK j b).restrictScalars (X.O i)).baseChange (X.Ok i k)

variable (Y)

def RHyp (i : X.Tw) (F : RFam Y i) (j : ℕ) (b : Bool) : Prop :=

  (F.B j b).FG ∧
  (∀ k P, HkIdx i k P → (F.B j b).map (hkO Y i j b k P) ≤ F.B j b) ∧

  (F.B j b).map (F.A j b) ≤ F.B j b ∧

  (∀ k P, HkIdx i k P → F.A j b ∘ₗ hkO Y i j b k P = hkO Y i j b k P ∘ₗ F.A j b) ∧

  ↑(F.S j b) ⊆ F.Sg j b ∧
  LinearIndependent (X.O i) (fun a : ↥(F.S j b) => F.A j b (Y.th i j b a)) ∧
  Submodule.span (X.O i) ((fun a => F.A j b (Y.th i j b a)) '' ↑(F.S j b)) = F.Th j b ∧

  Submodule.span (FractionRing (X.O i)) (F.Th j b : Set (Y.Fm i j b)) = F.VK j b ∧

  (∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, IsSplitPl D.host P) → Disjoint Q (X.S0 i) → ConjCl Q → DelOn Y i Q M →
    ∀ a ∈ F.S j b, Disjoint Q (Y.lev i j b a) →
    ((X.l i : X.O i) ^ c) • F.w j b Q M a ∈ LinearMap.range ((F.B j b).subtype.rTensor _)) ∧

  T3 Y i j b (F.B j b) ∧

  (∀ k Q ψ, TwOK i k Q ψ → F.ThPsi j b k Q ψ ≤
    ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)).map ((F.kap j b).baseChange (X.Ok i k))) ∧

  (∀ k Q ψ, TwOK i k Q ψ → F.ThPsi j b k Q ψ ≤ F.VKk j b k)

def partBR (i : X.Tw) (F : RFam Y i) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
    ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IsLatIn (F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q)))) (F.VKk j b k') ∧
      sIdx (X.l i) ((F.B j b).baseChange (X.Ok i k')) (F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q)))) ≤
        sIdx (X.l i) (F.B j b) (F.Th j b) + epsB j b

def IdxM (i : X.Tw) (F : RFam Y i) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (e : ℝ) : Prop :=
  ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra (X.Ok i k) O']
    [Algebra (X.O i) O'] [IsScalarTower (X.O i) (X.Ok i k) O'],
    Function.Injective (algebraMap (X.Ok i k) O') → Module.Finite (X.Ok i k) O' →
    ∀ M : Submodule O' (O' ⊗[X.O i] Y.Fm i j b),
      IsLatIn M (((F.VK j b).restrictScalars (X.O i)).baseChange O') →
      sIdx (X.l i) M (Submodule.span O'
          ((LinearMap.rTensor (Y.Fm i j b) (IsScalarTower.toAlgHom (X.O i) (X.Ok i k) O').toLinearMap) ''
            (F.ThPsi j b k Q ψ : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b)))) ≤
        sIdx (X.l i) M ((F.Th j b).baseChange O') + e

def partBM (i : X.Tw) (F : RFam Y i) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (eps' : ℝ) : Prop :=
  ∃ epsB : ℕ → Bool → ℝ, (∀ j b, 0 ≤ epsB j b) ∧
    ∑ j ∈ Finset.Icc 1 D.R.m, ∑ b : Bool, epsB j b ≤ eps' ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool,
      IsLatIn (F.ThPsi j b k' Q (psiAt b (ψ'.comp (X.art i Q)))) (F.VKk j b k') ∧
      IdxM Y i F j b k' Q (psiAt b (ψ'.comp (X.art i Q))) (epsB j b)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def TwistTheoremAtIndex (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, RHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
      partBR Y i F Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

def ArbitraryLatticeAtSetting (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, RHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
      partBM Y i F Q k' ψ' eps' ∧ partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps'

variable (X) in

def Pq1 (i : X.Tw) (s : X.Sig i) (P : PlE D.host) : X.O i :=
  1 + ∑ k ∈ Finset.Icc 1 D.R.r, (-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2) *
    X.hEig i s k P

open Classical in

def StepOK (i : X.Tw) (A0 Q'' Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  (∀ P ∈ Q, IsSplitPl D.host P) ∧ Disjoint Q (X.S0 i ∪ A0) ∧ ConjCl Q ∧ ConjCl Q'' ∧ DelOn Y i Q M ∧
    (∀ P ∈ Q'', ∀ s : X.Sig i, IsUnit (Pq1 X i s P)) ∧ Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q

open Classical in

def Good (i : X.Tw) (A0 : Finset (PlE D.host)) (h : ∀ Q M, LamO X i Q M) (v : ℝ) : Prop :=
  ∃ n0 : ℕ, ∀ (M : ℕ) (Q'' Q : Finset (PlE D.host)) (hs : Q'' ⊆ Q), StepOK Y i A0 Q'' Q M →
    ∃ Dd g : LamO X i Q'' M, projA i hs M (h Q M) = Dd * g ∧
      augA i Q'' M g ≠ 0 ∧ nval (X.O i) (X.l i) (augA i Q'' M g) ≤ v ∧
      ∃ L : List (X.O i × DelQM D.host (X.l i) Q'' M), L.length ≤ n0 * (Q \ Q'').card ∧
        (∀ p ∈ L, ∃ P ∈ Q \ Q'', ∃ σ : G D.host.E N.Om, IsFrob (N.plOm.1 P) (normV P) σ ∧
          p.2 = Multiplicative.toAdd (Y.delU i Q'' M σ)) ∧
        Dd - (L.map fun p => 1 - p.1 • grp i Q'' M p.2).prod ∈
          Ideal.map (algebraMap (X.O i) (LamO X i Q'' M)) (IsLocalRing.maximalIdeal (X.O i))

def SelmerSeriesChoice (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ A0 : Finset (PlE D.host),
  ∀ (J : ℕ) (sd : Fin J → Bool) (h : Fin J → ∀ Q M, LamO X i Q M) (v : Fin J → ℝ),
    (∀ x, 0 ≤ v x) → (∀ x, Good Y i A0 (h x) (v x)) →
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ) (M : ℕ)
      (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k')ˣ),
      PsiOk i A0 Q k' ψ' ∧ ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M) ∧
      partA bkP i Q k' ψ' eps' ∧ partAT bkP i Q k' ψ' eps' ∧
      partC N0 i Q k' ψ' eps' ∧ partD i Q k' ψ' eps' ∧
      ∃ ep : Fin J → ℝ, (∀ x, 0 ≤ ep x) ∧ ∑ x, ep x ≤ eps' ∧
        ∀ x, evA i Q M k' (psiAt (sd x) χ) (h x Q M) ≠ 0 ∧
          nval (X.Ok i k') (X.l i) (evA i Q M k' (psiAt (sd x) χ) (h x Q M)) ≤ v x + ep x

def PowerSeriesPrimePowerSubstNeZero : Prop :=
  ∀ (k : Type) [Field k] (l : ℕ), l.Prime → ∀ (ρ : ℕ) (F : MvPowerSeries (Fin ρ) k), F ≠ 0 →
    ∀ lb : (m : ℕ) → (Fin m → ℕ) → ℕ,
    ∃ e : Fin ρ → ℕ, StrictMono e ∧
      (∀ m : Fin ρ, lb m (fun t : Fin m => e (Fin.castLE m.is_lt.le t)) ≤ e m) ∧
      MvPowerSeries.subst (fun m => (PowerSeries.X : PowerSeries k) ^ (l ^ e m)) F ≠ 0

def PowerSeriesProductNotMemPowerIdeal : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (Dd g : PowerSeries R) (m0 n : ℕ),
    (∃ a ≤ m0, PowerSeries.coeff a Dd ∉ IsLocalRing.maximalIdeal R) →
    PowerSeries.constantCoeff g ≠ 0 →
    n = (IsDiscreteValuationRing.addVal R (PowerSeries.constantCoeff g)).toNat + 1 →
    Dd * g ∉ Ideal.map (PowerSeries.C : R →+* PowerSeries R) (IsLocalRing.maximalIdeal R ^ n) ⊔
      Ideal.span {(PowerSeries.X : PowerSeries R) ^ (n * m0 + 1)}

variable (X) in

def PolynomialValuationAtRootOfUnity : Prop :=
  ∀ (i : X.Tw) (J : ℕ) (h : Fin J → Polynomial (X.O i)) (MG : ℕ) (v : Fin J → ℝ) (eps : ℝ) (k0 : ℕ),
    0 < eps → (∀ x, 0 ≤ v x) →
    (∀ x, ∃ a ≤ MG, (h x).coeff a ≠ 0 ∧ nval (X.O i) (X.l i) ((h x).coeff a) ≤ v x) →
    2 * (J : ℝ) * MG / eps ≤ (Nat.totient (X.l i ^ k0) : ℝ) →
    ((IsDiscreteValuationRing.addVal (X.O i) (X.l i : X.O i)).toNat : ℝ) * eps < k0 →
    ∃ k' : ℕ, k0 ≤ k' ∧ (k' : ℝ) ≤ ((k0 : ℝ) + J * MG + 1) * Real.exp (2 * (∑ x, v x) / eps) + 1 ∧
      ∃ ζ : X.Ok i k', IsPrimitiveRoot ζ (X.l i ^ k') ∧
      ∃ ep : Fin J → ℝ, (∀ x, 0 ≤ ep x) ∧ ∑ x, ep x ≤ eps ∧
        ∀ x, Polynomial.aeval (ζ - 1) (h x) ≠ 0 ∧
          nval (X.Ok i k') (X.l i) (Polynomial.aeval (ζ - 1) (h x)) ≤ v x + ep x

def PqTw (i : X.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ) (P : PlE D.host)
    (γ : DelQM D.host (X.l i) Q M) : Module.End (X.O i) (Y.Fm i j b ⊗[X.O i] LamO X i Q M) :=
  1 + ∑ k ∈ Finset.Icc 1 D.R.r, ((-1 : X.O i) ^ k * ((normV P : ℕ) : X.O i) ^ (k * (k - 1) / 2)) •
    TensorProduct.map (hkO Y i j b k P) (LinearMap.mulLeft (X.O i) (grp i Q M (k • γ)))

open Classical in

def AugmentationCompatibility : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (M : ℕ),
    (∀ (Q' Q : Finset (PlE D.host)) (hs : Q' ⊆ Q), ConjCl Q → ConjCl Q' → DelOn Y i Q M → ∀ σ,
      resD (X.l i) hs M (Multiplicative.toAdd (Y.delU i Q M σ)) = Multiplicative.toAdd (Y.delU i Q' M σ)) ∧
    ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool),
      (∀ a : Y.Dat i j b, Y.thU i j b ∅ M a = Y.th i j b a ⊗ₜ[X.O i] (1 : LamO X i ∅ M)) ∧
      ∀ Q : Finset (PlE D.host), (∀ P ∈ Q, IsSplitPl D.host P) → Disjoint Q (X.S0 i) → ConjCl Q →
        DelOn Y i Q M → Formalism.MainNotions.IntegralHeckeForms.ClsQ (D := D) Q →
        ∀ P ∈ Q, ∀ Pb ∈ Q, P ≠ Pb → IsConjPl D.host P Pb →
        ∃ P0, (P0 = P ∨ P0 = Pb) ∧ ∃ sg : ℤ, (sg = 1 ∨ sg = -1) ∧
          ∀ a : Y.Dat i j b, Disjoint Q (Y.lev i j b a) →
          ∀ σ : G D.host.E N.Om, IsFrob (N.plOm.1 P0) (normV P0) σ →
            (projA i ((Finset.erase_subset Pb (Q.erase P)).trans (Finset.erase_subset P Q)) M).toLinearMap.lTensor
                (Y.Fm i j b) (Y.thU i j b Q M a) =
              PqTw Y i j b ((Q.erase P).erase Pb) M P0
                (sg • Multiplicative.toAdd (Y.delU i ((Q.erase P).erase Pb) M σ))
                (Y.thU i j b ((Q.erase P).erase Pb) M a)

def HeckeOperatorsCommute : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (j : ℕ) (b : Bool) (k k' : ℕ) (P P' : PlE D.host), HkIdx i k P → HkIdx i k' P' →
    Commute (Y.hkF i j b k P) (Y.hkF i j b k' P')

def aux₃ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → TwistTheoremAtIndex D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 i

def ArbitraryLatticeAtNonzeroIndexPlaces (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  ∀ i, D.ntw.NonzeroIndexPlace i → ArbitraryLatticeAtSetting D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 i

def AbstractTwistPinned (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  Formalism.MainNotions.IntegralHeckeForms.TwistingCharacterExistence D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0

def adm1 (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.aux₃ D bkP N0

def adm2 (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  SelmerSeriesChoice D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := PowerSeriesPrimePowerSubstNeZero

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := PowerSeriesProductNotMemPowerIdeal

def adm5 (D : Formalism.BasicNotions.D7) : Prop := PolynomialValuationAtRootOfUnity D.ntw

def adm6 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.ExistsIdealDenominator.aux₃ D

def adm7 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.ArithmeticCylinders.PointsLemma D

def adm8 (D : Formalism.BasicNotions.D7) (N0 : D.ntw.Tw → ℕ) : Prop := Formalism.MainNotions.BlochKatoReduction.adm9 D N0

def adm9 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.BlochKatoReduction.adm10 D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.BlochKatoReduction.adm8 D

def adm11 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.IntegralHeckeForms.adm10 D

def adm12 (D : Formalism.BasicNotions.D7) : Prop := AugmentationCompatibility D.nexp

def adm13 (D : Formalism.BasicNotions.D7) : Prop := HeckeOperatorsCommute D.nexp

def admitted (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (N0 : D.ntw.Tw → ℕ) : Prop :=
  adm1 D bkP N0 ∧ adm2 D bkP N0 ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D N0 ∧ adm9 D ∧
    adm10 D ∧ adm11 D ∧ adm12 D ∧ adm13 D

def Stmt (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, admitted D bkP N0 → aux₃ D bkP N0

def ArbitraryLatticeOfAdmissible (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, admitted D bkP N0 → ArbitraryLatticeAtNonzeroIndexPlaces D bkP N0

def AbstractTwistOfAdmissible (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) : Prop :=
  ∀ N0 : D.ntw.Tw → ℕ, admitted D bkP N0 → AbstractTwistPinned D bkP N0

end Formalism.MainNotions.LatticeVariant

end
