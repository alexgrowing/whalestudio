import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Embedding
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Residue
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Coefficients

noncomputable section

open Ideal

namespace Reformulated.AutPerF

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

abbrev ResK : Type u := IsLocalRing.ResidueField (unitBall K)

abbrev KZero [CharP (ResK K) p] [PerfectRing (ResK K) p] : Type u :=
  FractionRing (WittVector p (ResK K))

variable [CompleteSpace K] [CharZero K] [Fact (‖(p : K)‖ < 1)]
  [IsDiscreteValuationRing (unitBall K)] [CharP (ResK K) p] [PerfectRing (ResK K) p]

def wittToInteger : WittVector p (ResK K) →+* unitBall K := wittResidueToRing p (unitBall K)

instance : Algebra (KZero p K) K :=
  (fracWittLift p ((unitBall K).subtype.comp (wittToInteger p K))
    (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))).toAlgebra

theorem KZero.algebraMap_algebraMap (a : WittVector p (ResK K)) :
    algebraMap (KZero p K) K (algebraMap _ _ a) = wittToInteger p K a :=
  fracWittLift_algebraMap p _ _ a

instance : Module.Finite (KZero p K) K := by
  classical
  letI := (wittToInteger p K).toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Submodule (WittVector p (ResK K)) (unitBall K)).FG :=
    Module.Finite.fg_top (self := wittResidueToRing_finite p (unitBall K))
  refine ⟨⟨s.image (fun x : unitBall K => (x : K)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  have key (a : unitBall K) : (a : K) ∈ Submodule.span (KZero p K)
      (↑(s.image (fun x : unitBall K => (x : K))) : Set K) := by
    have ha : a ∈ Submodule.span (WittVector p (ResK K)) (s : Set (unitBall K)) := by
      rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by simpa using hy)
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      have : ((c • y : unitBall K) : K) = (algebraMap _ (KZero p K) c) • (y : K) := by
        rw [Algebra.smul_def, Algebra.smul_def, KZero.algebraMap_algebraMap]
        rfl
      rw [this]
      exact Submodule.smul_mem _ _ hy
  obtain ⟨⟨a, _, n, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (p : unitBall K)) x
  simp only [map_pow, map_natCast] at h
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have : x = ((p : KZero p K) ^ n)⁻¹ • (a : K) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hp),
      mul_comm]
    exact h
  rw [this]
  exact Submodule.smul_mem _ _ (key a)

instance : Algebra (KZero p K) (AlgCl K) :=
  ((algebraMap K (AlgCl K)).comp (algebraMap (KZero p K) K)).toAlgebra

instance : IsScalarTower (KZero p K) K (AlgCl K) := IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : Algebra.IsAlgebraic (KZero p K) (AlgCl K) := Algebra.IsAlgebraic.trans _ K _

def wittToOCK : WittVector p (ResK K) →+* OCK K := (OCK.ofInteger K).comp (wittToInteger p K)

theorem smul_wittToOCK (g : GalK K) (a : WittVector p (ResK K)) :
    g • wittToOCK p K a = wittToOCK p K a := OCK.smul_ofInteger K g _

theorem toRingHom_comp_wittToOCK (g : GalK K) :
    (MulSemiringAction.toRingHom (GalK K) (OCK K) g).comp (wittToOCK p K) = wittToOCK p K :=
  RingHom.ext (smul_wittToOCK p K g)

def wittToAinf : WittVector p (ResK K) →+* Ainf p (OCK K) := Ainf.liftWitt p (wittToOCK p K)

def kZeroToBcrisPlus : KZero p K →+* BcrisPlus p (OCK K) :=
  BcrisPlus.liftFracWitt p (wittToOCK p K)

def kZeroToBcris : KZero p K →+* Bcris p (OCK K) :=
  (algebraMap (BcrisPlus p (OCK K)) _).comp (kZeroToBcrisPlus p K)

def kZeroToBst : KZero p K →+* Bst p (OCK K) :=
  (algebraMap (Bcris p (OCK K)) _).comp (kZeroToBcris p K)

theorem frob_kZeroToBcris (x : KZero p K) : Bcris.frob p _ (kZeroToBcris p K x) =
    kZeroToBcris p K (WittVector.FractionRing.frobenius p (ResK K) x) := by
  simp [kZeroToBcris, kZeroToBcrisPlus, BcrisPlus.frob_liftFracWitt]

theorem frob_kZeroToBst (x : KZero p K) : Bst.frob p _ (kZeroToBst p K x) =
    kZeroToBst p K (WittVector.FractionRing.frobenius p (ResK K) x) := by
  simp [kZeroToBst, frob_kZeroToBcris]

theorem algebraMap_wittVector_eq (a : WittVector p (ResK K)) :
    algebraMap (AlgCl K) (CK K) (algebraMap (KZero p K) (AlgCl K) (algebraMap _ _ a)) =
      wittToOCK p K a := by
  rw [IsScalarTower.algebraMap_apply (KZero p K) K (AlgCl K), KZero.algebraMap_algebraMap]
  rfl

def algClToBdRPlus : AlgCl K →+* BdRPlus p (OCK K) :=
  BdRPlus.wittSection (wittToOCK p K) (algebraMap (AlgCl K) (CK K)) (algebraMap_wittVector_eq p K)

@[simp] theorem thetaC_algClToBdRPlus (x : AlgCl K) :
    BdRPlus.thetaC p (OCK K) (algClToBdRPlus p K x) = (x : CK K) :=
  BdRPlus.thetaC_wittSection _ _ _ x

theorem algClToBdRPlus_algebraMap (a : KZero p K) :
    algClToBdRPlus p K (algebraMap _ _ a) =
      algebraMap _ _ (AinfInv.liftFracWitt p (wittToOCK p K) a) :=
  BdRPlus.wittSection_algebraMap _ _ _ a

theorem eq_algClToBdRPlus (s : AlgCl K →+* BdRPlus p (OCK K))
    (h₁ : ∀ x, BdRPlus.thetaC p (OCK K) (s x) = (x : CK K))
    (h₂ : ∀ a : KZero p K, s (algebraMap _ _ a) =
      algebraMap _ _ (AinfInv.liftFracWitt p (wittToOCK p K) a)) : s = algClToBdRPlus p K :=
  BdRPlus.hom_ext_thetaC (F := KZero p K) (fun a => by rw [h₂, algClToBdRPlus_algebraMap])
    (fun x => by rw [h₁, thetaC_algClToBdRPlus])

end Reformulated.AutPerF
