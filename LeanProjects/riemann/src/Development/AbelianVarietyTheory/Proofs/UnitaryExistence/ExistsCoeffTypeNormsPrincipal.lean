import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegralRatZetaOfCoeff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare in

theorem exists_coeff_typeNorms_principal :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l), ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → KPsiIn (Dw := Dw) c'' := by
  intro E _ _ _ H Dw l c
  classical
  have key : ∀ x : ClassGroup (𝓞 E), ∃ (I : (Ideal (𝓞 E))⁰) (h : ℕ) (γ : 𝓞 E) (ψ : ℂ),
      ClassGroup.mk0 I = x ∧ 0 < h ∧ (I : Ideal (𝓞 E)) ^ h = Ideal.span {γ} ∧
        ψ ^ h = ∏ σ : E →+* ℂ, σ (γ : E) ^ Dw.mult σ := by
    intro x
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
    obtain ⟨h, hh, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I)).exists_pow_eq_one
    rw [← map_pow] at e
    obtain ⟨γ, hγ⟩ : ((I : Ideal (𝓞 E)) ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I ^ h).2).1 e
    obtain ⟨ψ, hψ⟩ := IsAlgClosed.exists_pow_nat_eq (∏ σ : E →+* ℂ, σ (γ : E) ^ Dw.mult σ) hh
    exact ⟨I, h, γ, ψ, rfl, hh, hγ, hψ⟩
  choose I h γ ψ hI hh hγ hψ using key
  haveI := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l
    (Finset.univ.image ψ ∪ Finset.univ.image fun i => (b i : ℂ)) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
      rcases hz with ⟨x, rfl⟩ | ⟨i, rfl⟩
      · refine (IsIntegral.of_pow (hh x) ?_).isAlgebraic
        rw [hψ]
        exact IsIntegral.prod _ fun σ _ =>
          ((Algebra.IsIntegral.isIntegral (R := ℚ) (γ x : E)).map σ.toRatAlgHom).pow _
      · exact ((Algebra.IsIntegral.isIntegral (R := ℚ) (b i)).map c.F.val).isAlgebraic)
  refine ⟨c', ?_, fun c'' hle => ?_⟩
  · intro z hz
    have e : z = ∑ i, b.repr ⟨z, hz⟩ i • (b i : ℂ) := by
      have := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
      simp only [map_sum, map_smul] at this
      exact this.symm
    rw [e]
    exact sum_mem fun i _ => IntermediateField.smul_mem _ (hc' _ (by simp))
  · rw [kPsiIn_iff]
    intro 𝔞 h0
    let x := ClassGroup.mk0 (⟨𝔞, mem_nonZeroDivisors_of_ne_zero h0⟩ : (Ideal (𝓞 E))⁰)
    have hm : ψ x ∈ c''.F := hle (hc' _ (by simp))
    have h1 : IsBe Dw c'' (I x) ⟨ψ x, hm⟩ := isBe_of_pow (hh x) (by
      have e : (⟨ψ x, hm⟩ : c''.F) ^ h x = reflexNorm Dw c'' (γ x : E) := by
        apply c''.F.val.toRingHom.injective
        rw [map_pow, reflexNorm, map_prod]
        simp only [map_pow]
        exact hψ x
      rw [hγ, e]; exact isBe_principal Dw c'' _)
    obtain ⟨u, v, hu0, -, huv⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hI x).symm
    have h2 := isBe_mul (isBe_principal Dw c'' v) h1
    rw [← huv] at h2
    exact ⟨_, isBe_div (by simpa using hu0) (isBe_principal Dw c'' u) h2⟩

end GlobalTheory
