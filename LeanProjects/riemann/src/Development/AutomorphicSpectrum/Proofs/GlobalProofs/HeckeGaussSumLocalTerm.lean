import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

namespace GlobalTheory.CompanionTheory.HeckeBridge.GaussSum

variable {E : Type} [Field E] [NumberField E]

theorem dvd_conductor (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0)
    (h : ExpAt χ v m) : v.asIdeal ∣ (toHecke χ hu).conductor := by
  by_contra hv
  refine h.not_unrAt hm fun x hx => ?_
  have hx' : Valued.v (x : v.adicCompletion E) = 1 := hx
  have hmem : x ∈ (Submonoid.ofClass (v.adicCompletionIntegers E)).units := by
    refine Submonoid.mem_units_iff _ _ |>.2 ⟨(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx'.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_⟩
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx', inv_one]
  have h1 := (toHecke χ hu).localComponent_eq_one_of_not_dvd hv hmem
  have h2 := coe_localComponent χ hu v x
  rw [h1] at h2
  exact Units.ext (by simpa using h2.symm)

theorem hval (v : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_eq_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) = 1 := by
  exact (hval v _).trans ((v.valuation_eq_one_iff_notMem (K := E)).2 hy)

theorem valued_ne_one {v : HeightOneSpectrum (𝓞 E)} {y : 𝓞 E} (hy : y ∈ v.asIdeal) :
    Valued.v (algebraMap E (v.adicCompletion E) (y : E)) ≠ 1 := by
  exact fun h => (v.valuation_eq_one_iff_notMem (K := E)).1 ((hval v _).symm.trans h) hy

theorem term_of_notMem (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal ∣ (toHecke χ hu).conductor) (c : Eˣ) {y : 𝓞 E} (hy : y ∉ v.asIdeal) :
    (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) (y : E)) *
        psiAt v (((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) (y : E)) =
      gaussTerm χ v c (y : E) := by
  have hy0 : (y : E) ≠ 0 := by
    intro h0
    have : y = 0 := by exact_mod_cast h0
    exact hy (this ▸ v.asIdeal.zero_mem)
  have h1 := (toHecke χ hu).finiteTest_of_dvd hv (atFin v (Units.mk0 (y : E) hy0)) (valued_eq_one hy)
  have h2 : ((atFin v (Units.mk0 (y : E) hy0) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  rw [h2] at h1
  rw [h1, coe_localComponent, gaussTerm, dif_neg hy0, Units.val_inv_eq_inv_val]
  have h3 : ((atFin v c : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (c : E) := rfl
  rw [h3, map_div₀, div_eq_mul_inv, mul_comm (algebraMap E _ _)]
  rfl

theorem finiteTest_sum_eq_gaussSumAt (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ)
    (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (hm : m ≠ 0) (hE : ExpAt χ v m) :
    ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) =
      gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  have hv := dvd_conductor χ hu v hm hE
  rw [gaussSumAt]
  have hG : ∀ y : (𝓞 E ⧸ v.asIdeal ^ m)ˣ, gaussTerm χ v (unif v ^ (m + diffExp v)) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E) =
      (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out (y : 𝓞 E ⧸ v.asIdeal ^ m) : 𝓞 E) : E)) :=
    fun y => (term_of_notMem χ hu v hv _ (out_notMem v hm y)).symm
  rw [finsum_congr hG, ← finsum_mem_range (g := ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)) Units.val_injective
    (f := fun r : 𝓞 E ⧸ v.asIdeal ^ m => (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) *
      psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ *
        algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E))), finsum_mem_def]
  refine finsum_congr fun r => ?_
  by_cases hr : r ∈ Set.range ((↑) : (𝓞 E ⧸ v.asIdeal ^ m)ˣ → 𝓞 E ⧸ v.asIdeal ^ m)
  · rw [Set.indicator_of_mem hr]
  · rw [Set.indicator_of_notMem hr]
    have hmem : (Quotient.out r : 𝓞 E) ∈ v.asIdeal := by
      by_contra hn
      have h1 := Ideal.Quotient.isUnit_mk_pow_of_notMem v.asIdeal (n := m) hn
      rw [Ideal.Quotient.mk_out] at h1
      exact hr ⟨h1.unit, rfl⟩
    rw [(toHecke χ hu).finiteTest_eq_zero_of_dvd hv (valued_ne_one hmem), zero_mul]

end GlobalTheory.CompanionTheory.HeckeBridge.GaussSum
