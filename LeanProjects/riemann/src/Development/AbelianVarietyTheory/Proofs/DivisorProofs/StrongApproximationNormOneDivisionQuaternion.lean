import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FujisakiDivisionQuaternionAlgebraModCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseConjMemClosureOfIsCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneQuaternionNearConjRationalTimesSupportedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionAlgebraTopologicalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlacesIdempotentNearOneAdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalNormOneOfIdempotentConjStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.DivAssembly

section Ring

variable {R : Type*} [CommRing R] {a b : R}

theorem nrm_one' : nrm (1 : ℍ[R, a, b]) = 1 := by simp [nrm]

theorem nrm_star' (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by simp [nrm]

theorem star_mul_eq' (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  have h := mul_star_eq (star x)
  rwa [star_star, nrm_star'] at h

theorem nrm_trunc (e : R) (he : e * e = e) (g : ℍ[R, a, b]) :
    nrm (e • (g - 1) + 1) = e * nrm g + (1 - e) := by
  simp only [nrm, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add, QuaternionAlgebra.imJ_add,
    QuaternionAlgebra.imK_add, QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, QuaternionAlgebra.re_sub, QuaternionAlgebra.imI_sub, QuaternionAlgebra.imJ_sub,
    QuaternionAlgebra.imK_sub, QuaternionAlgebra.re_one, QuaternionAlgebra.imI_one, QuaternionAlgebra.imJ_one,
    QuaternionAlgebra.imK_one, smul_eq_mul]
  linear_combination ((g.re - 1) ^ 2 - a * g.imI ^ 2 - b * g.imJ ^ 2 + a * b * g.imK ^ 2) * he

end Ring

section Alg

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem prod_decomp (e : R) (he : e * e = e) (g : A) :
    ((1 - e) • (g - 1) + 1) * (e • (g - 1) + 1) = g := by
  have h0 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, h0, zero_smul, zero_add]
  rw [← add_assoc, ← add_smul, show e + (1 - e) = 1 by ring, one_smul, sub_add_cancel]

end Alg

variable {F : Type} [Field F] [NumberField F]

theorem isPlacesIdem_idem {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {ε : AF F}
    (h : IsPlacesIdem S₁ S₂ ε) : ε * ε = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    change fstA F ε w * fstA F ε w = fstA F ε w
    by_cases hw : w ∈ S₁
    · rw [h.1 w hw, one_mul]
    · rw [h.2.1 w hw, zero_mul]
  · refine RestrictedProduct.ext _ _ fun u => ?_
    change evalV F u (sndA F (ε * ε)) = evalV F u (sndA F ε)
    rw [map_mul, map_mul]
    by_cases hu : u ∈ S₂
    · rw [h.2.2.1 u hu, one_mul]
    · rw [h.2.2.2 u hu, zero_mul]

theorem rat_mul' {a b : F} (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_one' {a b : F} : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem continuous_smul_const {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {a b : R}
    (x : ℍ[R, a, b]) : Continuous fun t : R => t • x := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.DivAssembly

namespace GlobalTheory.QSA.DivAssembly

variable {F : Type} [Field F] [NumberField F]

theorem conj_mem_normOneIdempotentSubgroup_of_rational_relation {a b : F} (ε : AF F) (w c c' : DA F a b) (l : AF F) (hl : IsUnit l) (δ γ : ℍ[F, a, b])
    (hδ : nrm δ ≠ 0) (hγ : nrm γ = 1) (h : DA F a b) (hh : nrm h = 1) (hhε : ε • (h - 1) = h - 1)
    (hcc' : c * c' = 1)
    (hyw : l • (rat δ * c) * w = rat γ * l • (rat δ * c) * h) : c * w * c' ∈ H0 ε := by
  set δ' : ℍ[F, a, b] := (nrm δ)⁻¹ • star δ with hδ'
  have hδδ : δ' * δ = 1 := by
    rw [hδ', smul_mul_assoc, star_mul_eq', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hδ, map_one]
  have E1 : rat δ * c * w = rat γ * rat δ * c * h := by
    have h2 : l • (rat δ * c * w) = l • (rat γ * rat δ * c * h) := by
      rw [← smul_mul_assoc, hyw, mul_smul_comm, smul_mul_assoc, mul_assoc (rat γ), mul_assoc (rat γ)]
      simp only [mul_assoc]
    exact hl.smul_left_cancel.1 h2
  refine ⟨δ' * γ * δ, ?_, c * h * c', ?_, ?_, ?_⟩
  · rw [nrm_mul, nrm_mul, hγ, mul_one, ← nrm_mul, hδδ, nrm_one']
  · rw [nrm_mul, nrm_mul, hh, mul_one, ← nrm_mul, hcc', nrm_one']
  · have e1 : c * h * c' - 1 = c * (h - 1) * c' := by
      rw [mul_sub, sub_mul, mul_one, hcc']
    rw [e1, ← smul_mul_assoc, ← mul_smul_comm, hhε]
  · calc c * w * c' = (rat δ' * rat δ) * c * w * c' := by rw [← rat_mul', hδδ, rat_one', one_mul]
      _ = rat δ' * (rat δ * c * w) * c' := by simp only [mul_assoc]
      _ = rat δ' * (rat γ * rat δ * c * h) * c' := by rw [E1]
      _ = rat (δ' * γ * δ) * (c * h * c') := by simp only [rat_mul', mul_assoc]

theorem strongApproximation_normOne_divisionQuaternion : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → (∀ t : AF F, ∃ h : DA F a b, nrm h = 1 ∧ ε * h.re = ε * t) → ∀ g : DA F a b, nrm g = 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
  intro F _ _ a b ha hb hdiv S₁ S₂ ε hε hS hsurj g hg
  have hee : ε * ε = ε := isPlacesIdem_idem hε
  obtain ⟨hmul, -, -, -⟩ := GlobalTheory.T.closure_normOneProducts_h0_properties F a b ε hee
  obtain ⟨htr, -, -, hT2⟩ := GlobalTheory.T.quaternion_algebra_topological_ring (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b)
  haveI : IsTopologicalRing (DA F a b) := htr
  haveI : T2Space (AF F) := by
    haveI : T2Space (InfiniteAdeleRing F) := inferInstanceAs (T2Space (∀ w : InfinitePlace F, w.Completion))
    haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := inferInstanceAs (T2Space (RestrictedProduct
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
    exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  haveI : T2Space (DA F a b) := hT2 inferInstance
  obtain ⟨C, hC, hfuj⟩ := GlobalTheory.T.fujisaki_divisionQuaternionAlgebra_mod_centre F a b ha hb hdiv

  have key : ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F),
      IsPlacesIdem T₁ T₂ η → ∀ g : DA F a b, nrm g = 1 → η • (g - 1) = g - 1 → g ∈ closure (H0 (a := a) (b := b) ε) := by
    intro T₁ T₂ η hη g hg hgη
    have hee' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hee
    set gS : DA F a b := ε • (g - 1) + 1 with hgSdef
    set gN : DA F a b := (1 - ε) • (g - 1) + 1 with hgNdef
    have hprod : gN * gS = g := prod_decomp ε hee g
    have hgS : gS ∈ H0 (a := a) (b := b) ε := by
      refine ⟨1, nrm_one', gS, ?_, ?_, by rw [rat_one', one_mul]⟩
      · rw [hgSdef, nrm_trunc ε hee, hg]; ring
      · rw [hgSdef, add_sub_cancel_right, smul_smul, hee]
    have hgN1 : nrm gN = 1 := by rw [hgNdef, nrm_trunc (1 - ε) hee', hg]; ring
    have hgNε : ε • (gN - 1) = 0 := by
      rw [hgNdef, add_sub_cancel_right, smul_smul, show ε * (1 - ε) = 0 by linear_combination -hee, zero_smul]
    have hgNη : η • (gN - 1) = gN - 1 := by
      rw [hgNdef, add_sub_cancel_right, smul_comm, hgη]
    have hW : ∀ W ∈ 𝓝 gN, ∃ c ∈ C, ∃ c' ∈ C, c * c' = 1 ∧ c' * c = 1 ∧ ∃ w ∈ W, c * w * c' ∈ H0 (a := a) (b := b) ε := by
      intro W hW
      obtain ⟨w, hwW, y, hy, γ, hγ, h, hh, hhε, hyw⟩ :=
        GlobalTheory.T.normOneQuaternion_near_conj_rational_times_supported F a b ha hb S₁ S₂ ε hε hS hsurj gN hgN1 hgNε W hW
      obtain ⟨δ, l, c, c', hδ, hl, hc, hc', hcc', hc'c, rfl⟩ := hfuj y hy
      exact ⟨c, hc, c', hc', hcc', hc'c, w, hwW, conj_mem_normOneIdempotentSubgroup_of_rational_relation ε w c c' l hl δ γ hδ hγ h hh hhε hcc' hyw⟩
    obtain ⟨c, -, c', -, hcc', hc'c, hmem⟩ := GlobalTheory.T.exists_conj_mem_closure_of_isCompact (DA F a b) (H0 (a := a) (b := b) ε) C hC gN hW
    have hgN := GlobalTheory.T.mem_closure_rationalNormOne_of_idempotent_conj F a b ha hb T₁ T₂ η hη ε hee gN hgN1 hgNη c c' hcc' hc'c hmem
    rw [← hprod]
    exact hmul _ hgN _ (subset_closure hgS)

  suffices g ∈ closure (closure (H0 (a := a) (b := b) ε)) by rwa [closure_closure] at this
  have hφ : Continuous fun η : AF F => η • (g - 1) + 1 := (continuous_smul_const (g - 1)).add continuous_const
  rw [mem_closure_iff_nhds]
  intro V hV
  have hpre : (fun η : AF F => η • (g - 1) + 1) ⁻¹' V ∈ 𝓝 (1 : AF F) :=
    hφ.continuousAt.preimage_mem_nhds (by rwa [one_smul, sub_add_cancel])
  obtain ⟨T₁, T₂, η, hη, hηV⟩ := GlobalTheory.T.exists_placesIdempotent_near_one_adeles F _ hpre
  have hηη : η * η = η := isPlacesIdem_idem hη
  refine ⟨η • (g - 1) + 1, hηV, key T₁ T₂ η hη _ ?_ ?_⟩
  · rw [nrm_trunc η hηη, hg]; ring
  · rw [add_sub_cancel_right, smul_smul, hηη]

end GlobalTheory.QSA.DivAssembly
