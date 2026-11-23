import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import ReciprocityTheory.GaloisValuations.GlobalB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem eq_of_perturbed_pow_sub_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (y z u : R) (m : ℕ) (h : Polynomial ℤ)
    (hy : y ^ m - 1 = u * Polynomial.aeval y h) (hz : z ^ m - 1 = u * Polynomial.aeval z h)
    (hu : u ∈ IsLocalRing.maximalIdeal R) (hzy : z - y ∈ IsLocalRing.maximalIdeal R)
    (hm : (m : R) ∉ IsLocalRing.maximalIdeal R) : z = y := by
  by_contra hne
  have hne' : z - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, hk⟩ : z - y ∣ Polynomial.aeval z h - Polynomial.aeval y h := by
    have := Polynomial.sub_dvd_eval_sub z y (h.map (algebraMap ℤ R))
    simpa only [Polynomial.eval_map_algebraMap] using this
  have hS := Commute.geom_sum₂_mul (Commute.all z y) m
  have hS' : (∑ i ∈ Finset.range m, z ^ i * y ^ (m - 1 - i)) = u * k := by
    apply mul_right_cancel₀ hne'
    rw [hS]
    linear_combination hz - hy + u * hk
  have hu0 : IsLocalRing.residue R u = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hu
  have hzy0 : IsLocalRing.residue R z = IsLocalRing.residue R y := by
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hzy
    rwa [map_sub, sub_eq_zero] at this
  have hm0 : (m : IsLocalRing.ResidueField R) ≠ 0 := by
    intro h0
    apply hm
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, h0]
  have hmpos : m ≠ 0 := by
    rintro rfl
    simp at hm0
  have hy1 : (IsLocalRing.residue R y) ^ m = 1 := by
    have := congrArg (IsLocalRing.residue R) hy
    rwa [map_sub, map_mul, hu0, zero_mul, map_pow, map_one, sub_eq_zero] at this
  have hy0 : IsLocalRing.residue R y ≠ 0 := by
    intro h0
    rw [h0, zero_pow hmpos] at hy1
    exact zero_ne_one hy1
  have := congrArg (IsLocalRing.residue R) hS'
  simp only [map_sum, map_mul, map_pow, hu0, zero_mul, hzy0] at this
  rw [geom_sum₂_self] at this
  exact mul_ne_zero hm0 (pow_ne_zero _ hy0) this

theorem exists_roots_fixed_of_mem_Ine (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A' : ValuationSubring Ω) (σ : G E Ω)
    (hσ : σ ∈ Ine (F := E) A') (b e : Ω) (m : ℕ) (f : Polynomial ℤ) (he : IsIntegral ℤ e)
    (hσe : σ e = e) (hv : A'.valuation (1 - e) < 1) (hm : A'.valuation (m : Ω) = 1)
    (hf : f.Monic) (hfm : f.natDegree = m) (hb : Polynomial.aeval b f = 0) :
    ∃ ys : Multiset Ω, Multiset.card ys = m ∧ (∀ y ∈ ys, IsIntegral ℤ y ∧ σ y = y) ∧
      e * (b ^ m - 1) = (ys.map (fun y => b - y)).prod := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  set h : Polynomial ℤ := X ^ m - C 1 - f with hh
  have hdeg : h.degree < (m : WithBot ℕ) := by
    have h1 : (X ^ m - C 1 : Polynomial ℤ).Monic := Polynomial.monic_X_pow_sub_C 1 hm0
    have h2 : (X ^ m - C 1 : Polynomial ℤ).degree = m :=
      Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hm0) 1
    have h3 : f.degree = m := by rw [Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
    rw [← h2]
    exact Polynomial.degree_sub_lt (h2.trans h3.symm) h1.ne_zero
      (by rw [h1.leadingCoeff, hf.leadingCoeff])
  let R := integralClosure ℤ Ω
  let e0 : R := ⟨e, he⟩
  let g0 : Polynomial R := f.map (algebraMap ℤ R) + C e0 * h.map (algebraMap ℤ R)
  have hf0 : (f.map (algebraMap ℤ R)).Monic := hf.map _
  have hf0d : (f.map (algebraMap ℤ R)).degree = m := by
    rw [hf.degree_map, Polynomial.degree_eq_natDegree hf.ne_zero, hfm]
  have hlt : (C e0 * h.map (algebraMap ℤ R)).degree < (f.map (algebraMap ℤ R)).degree := by
    rw [hf0d, ← Polynomial.smul_eq_C_mul]
    exact lt_of_le_of_lt ((Polynomial.degree_smul_le _ _).trans Polynomial.degree_map_le) hdeg
  have hg0 : g0.Monic := hf0.add_of_left hlt
  have hg0d : g0.degree = m := by
    rw [← hf0d]; exact Polynomial.degree_add_eq_left_of_degree_lt hlt
  have hev : ∀ y : Ω, Polynomial.aeval y g0 = Polynomial.aeval y f + e * Polynomial.aeval y h := by
    intro y
    simp only [g0, map_add, map_mul, Polynomial.aeval_map_algebraMap, Polynomial.aeval_C]
    rfl
  have hhev : ∀ y : Ω, Polynomial.aeval y h = y ^ m - 1 - Polynomial.aeval y f := by
    intro y
    simp [hh]
  let g : Polynomial Ω := g0.map (algebraMap R Ω)
  have hg : g.Monic := hg0.map _
  have hgd : g.natDegree = m := by
    rw [hg0.natDegree_map, Polynomial.natDegree_eq_of_degree_eq_some hg0d]
  have hcard : Multiset.card g.roots = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨g.roots, hcard.trans hgd, ?_, ?_⟩
  · intro y hy
    have hy0 : Polynomial.aeval y g0 = 0 := by
      have := (Polynomial.mem_roots hg.ne_zero).mp hy
      rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at this
    have hyint : IsIntegral ℤ y := by
      have : IsIntegral R y := ⟨g0, hg0, hy0⟩
      exact isIntegral_trans y this
    refine ⟨hyint, ?_⟩
    have hyA : y ∈ A' := mem_of_isIntegral_int A' hyint
    have hσ' := mem_Ine.mp hσ
    have hzA : σ y ∈ A' := (apply_mem_iff_of_mem_Dec hσ'.1 y).mpr hyA
    have huA : 1 - e ∈ A' := (A'.valuation_le_one_iff _).mp hv.le
    have e1 : y ^ m - 1 = (1 - e) * Polynomial.aeval y h := by
      rw [hev] at hy0
      linear_combination hy0 - hhev y
    have e2 : (σ y) ^ m - 1 = (1 - e) * Polynomial.aeval (σ y) h := by
      have := congrArg σ e1
      rw [map_sub, map_pow, map_one, map_mul, map_sub, map_one, hσe] at this
      rw [this]
      congr 1
      exact (Polynomial.aeval_algHom_apply (σ : Ω →+* Ω).toIntAlgHom y h).symm
    have hae : ∀ x : A', ((Polynomial.aeval x h : A') : Ω) = Polynomial.aeval (x : Ω) h :=
      fun x => (Polynomial.aeval_algHom_apply A'.subtype.toIntAlgHom x h).symm
    have := eq_of_perturbed_pow_sub_one (R := A') ⟨y, hyA⟩ ⟨σ y, hzA⟩ ⟨1 - e, huA⟩ m h
      (Subtype.ext (by simpa [hae] using e1)) (Subtype.ext (by simpa [hae] using e2))
      ((A'.valuation_lt_one_iff _).mpr hv)
      ((A'.valuation_lt_one_iff _).mpr (hσ'.2 y ((A'.valuation_le_one_iff _).mpr hyA)))
      (fun hh' => by
        have := (A'.valuation_lt_one_iff _).mp hh'
        rw [show ((m : A') : Ω) = m from by simp, hm] at this
        exact lt_irrefl _ this)
    exact congrArg Subtype.val this
  · have := congrArg (Polynomial.eval b)
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hg hcard)
    rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map_algebraMap, hev,
      hhev, hb] at this
    simp only [Function.comp_def, eval_sub, eval_X, eval_C] at this
    rw [this]; ring

end GlobalTheory
