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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLabelCommonGenericFibrePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsOfGeometric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.PullLab

open GlobalTheory.Poinc.DeepLab

theorem exists_lab_of_isGrpPullback : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left) (d : ℕ), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → S₂.r * S₂.N = S₁.r * S₁.N * d → ∃ lam : S₁.Gam →+ S₂.Gam, (∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left) ∧ ∀ a', ∃ a, lam a = d • a' := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ S₁ S₂ ρ₁ ρ₂ om φ d hpb hd
  let K := AlgebraicClosure Ω₂
  let x₀ : Sp K ⟶ Sp S₂.R := spMap (algebraMap Ω₂ K) ≫ spMap S₂.R.val.toRingHom
  let U : Over.mk ((baseOver (Sp S₂.R)).hom ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (spMap om) (by simp)
  let V₂ : Over.mk x₀ ⟶ baseOver (Sp S₂.R) := Over.homMk x₀ (by simp)
  let p₁ : Multiplicative S₁.Gam →* (baseOver (Sp S₁.R) ⟶ ρ₁.P.A) :=
    MonoidHom.mk' (fun a => ρ₁.pt (Multiplicative.toAdd a)) fun a b => ρ₁.pt_add _ _
  let p₂ : Multiplicative S₂.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) :=
    MonoidHom.mk' (fun a => ρ₂.pt (Multiplicative.toAdd a)) fun a b => ρ₂.pt_add _ _
  have hbij : Function.Bijective (pushHom hpb (baseOver (Sp S₂.R))) :=
    ⟨pushHom_injective hpb _, pushHom_surjective hpb _⟩
  let e := MulEquiv.ofBijective (pushHom hpb (baseOver (Sp S₂.R))) hbij
  let σ : Multiplicative S₁.Gam →* (baseOver (Sp S₂.R) ⟶ ρ₂.P.A) := e.symm.toMonoidHom.comp ((preHom U).comp p₁)
  have hσ : ∀ a, pushHom hpb _ (σ a) = U ≫ ρ₁.pt (Multiplicative.toAdd a) := fun a =>
    e.apply_symm_apply (U ≫ ρ₁.pt (Multiplicative.toAdd a))
  have hσl : ∀ a, (σ a).left ≫ φ = spMap om ≫ (ρ₁.pt (Multiplicative.toAdd a)).left := fun a =>
    congrArg (fun q => q.left) (hσ a)
  have hσL : ∀ a : S₁.Gam, σ (Multiplicative.ofAdd a) ^ (S₂.r * S₂.N) = 1 := by
    intro a
    rw [hd, pow_mul, map_pow_self, one_pow]
  have uniq : ∀ z : baseOver (Sp S₂.R) ⟶ ρ₂.P.A, z ^ (S₂.r * S₂.N) = 1 →
      ∃! b : S₂.Gam, p₂ (Multiplicative.ofAdd b) = z := by
    intro z hz
    obtain ⟨b, hb⟩ := GlobalTheory.torsionSection_eq_labelled_of_isDomain S₂.R ρ₂.P (S₂.r * S₂.N) S₂.Gam ρ₂.pt
      (fun K _ _ x z hz => (ρ₂.pt_bij K x z hz).exists) z hz
    refine ⟨b, hb, fun b' hb' => ?_⟩
    have h2 : (V₂ ≫ z) ^ (S₂.r * S₂.N) = 1 := by
      have h3 := congrArg (preHom V₂) hz
      rwa [map_pow, map_one] at h3
    exact (ρ₂.pt_bij K x₀ (V₂ ≫ z) h2).unique (congrArg (V₂ ≫ ·) hb') (congrArg (V₂ ≫ ·) hb)
  obtain ⟨lam, hlam⟩ := exists_lab _ p₂ σ uniq hσL
  have hpt : ∀ a, (ρ₂.pt (lam a)).left ≫ φ = spMap om ≫ (ρ₁.pt a).left := fun a => by
    have h4 := hσl (Multiplicative.ofAdd a)
    rw [← hlam a] at h4
    exact h4
  refine ⟨lam, hpt, fun a' => ?_⟩
  set y := d • a' with hy
  have hyL : p₂ (Multiplicative.ofAdd y) ^ (S₁.r * S₁.N) = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, hy, smul_smul, ← hd, nsmul_self_eq_zero, ofAdd_zero, map_one]
  let T₀ : Over (Sp S₂.R) := Over.mk x₀
  let V₁ : Over.mk (x₀ ≫ spMap om) ⟶ baseOver (Sp S₁.R) := Over.homMk (x₀ ≫ spMap om) (by simp)
  let z₁ : Over.mk (x₀ ≫ spMap om) ⟶ ρ₁.P.A := pushHom hpb T₀ (V₂ ≫ ρ₂.pt y)
  have hz₁ : z₁ ^ (S₁.r * S₁.N) = 1 := by
    have h0 : (V₂ ≫ ρ₂.pt y) ^ (S₁.r * S₁.N) = 1 := by
      have h3 := congrArg (preHom V₂) hyL
      rwa [map_pow, map_one] at h3
    show (pushHom hpb T₀) _ ^ _ = 1
    rw [← map_pow, h0, map_one]
  obtain ⟨a, ha, -⟩ := ρ₁.pt_bij K (x₀ ≫ spMap om) z₁ hz₁
  refine ⟨a, ?_⟩
  have hpush : pushHom hpb T₀ (V₂ ≫ ρ₂.pt (lam a)) = V₁ ≫ ρ₁.pt a := by
    apply Over.OverMorphism.ext
    show (V₂ ≫ ρ₂.pt (lam a)).left ≫ φ = (V₁ ≫ ρ₁.pt a).left
    simp only [Over.comp_left, Category.assoc, V₂, V₁, Over.homMk_left]
    rw [hpt]
  have h1 : V₂ ≫ ρ₂.pt (lam a) = V₂ ≫ ρ₂.pt y := pushHom_injective hpb T₀ (hpush.trans ha)
  have h2 : (V₂ ≫ ρ₂.pt y) ^ (S₂.r * S₂.N) = 1 := by
    have h3 := congrArg (preHom V₂) (map_pow_self _ p₂ y)
    rwa [map_pow, map_one] at h3
  exact (ρ₂.pt_bij K x₀ _ h2).unique h1 rfl

end GlobalTheory.Poinc.PullLab
