import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEndOfEighthPowerOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisationModelFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithBaseFiniteContainingRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem realPt_comp_pow {S : Scheme.{0}} {A T T₀ : Over S} [GrpObj A] (u : T₀ ⟶ T) (x : T ⟶ A) (n : ℕ) :
    u ≫ x ^ n = (u ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem realPt_inj_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  intro o₂ Ω₂ _ _ _ S₂ ρ₂ T G _ f φ hφ x y hxy
  have hpt : ρ₂.pt x = ρ₂.pt y := by
    ext
    exact hφ.1.hom_ext hxy (by simp only [Category.assoc, Over.w])
  have hzero : ρ₂.pt 0 = 1 := by
    have h := ρ₂.pt_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  have hsmul : ∀ (a : S₂.Gam) (n : ℕ), ρ₂.pt (n • a) = ρ₂.pt a ^ n := by
    intro a n
    induction n with
    | zero => rw [zero_smul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, ρ₂.pt_add, ih, pow_succ]
  have hkill : ∀ a : S₂.Gam, ρ₂.pt a ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [← hsmul]
    have : (S₂.r * S₂.N) • a = 0 := by
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    rw [this, hzero]
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap ((algebraMap Ω₂ K).comp (S₂.R.val : S₂.R →+* Ω₂))
  let u : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  have hz : (u ≫ ρ₂.pt x) ^ (S₂.r * S₂.N) = 1 := by
    rw [← realPt_comp_pow, hkill, MonObj.comp_one]
  obtain ⟨a, _, huniq⟩ := ρ₂.pt_bij K x₀ (u ≫ ρ₂.pt x) hz
  have h1 := huniq x rfl
  have h2 := huniq y (by rw [hpt])
  exact h1.trans h2.symm

end GlobalTheory.Poinc.Sep
