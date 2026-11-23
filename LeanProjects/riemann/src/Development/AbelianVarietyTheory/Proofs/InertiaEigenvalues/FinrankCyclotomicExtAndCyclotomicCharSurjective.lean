import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfieldStatement

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem aeval_ne_zero_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : aeval π p ≠ 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have hπ0 : π ≠ 0 := by
    rw [← norm_pos_iff, hπ]; positivity
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  intro h
  rw [aeval_eq_sum_range' (Nat.lt_succ_self _)] at h
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = 0 := by
    rw [← h]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs, nnnorm_zero] at h6
  have hm : p.natDegree ∈ p.support := natDegree_mem_support_of_nonzero hp
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hm
  rw [← h6] at h7
  obtain ⟨n, hn⟩ := key _ hm
  have h8 : ‖p.coeff p.natDegree • π ^ p.natDegree‖ ≤ 0 := h7
  rw [hn] at h8
  exact absurd h8 (not_le.2 (by positivity))

theorem minpoly_unramifiedSubfield_eq_cyclotomic (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by
  have hlp : l.Prime := Fact.out
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (l ^ j) ↥(K0 K)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    (minpoly.dvd _ _ hroot)
  rw [natDegree_cyclotomic]
  by_contra hlt
  push_neg at hlt
  refine aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 (minpoly ↥(K0 K) ζ)) ?_ ?_ ?_
  · intro h
    exact minpoly.ne_zero hint (taylor_injective 1 (by rw [h, map_zero]))
  · rwa [natDegree_taylor]
  · rw [taylor_apply, aeval_comp]
    simp

theorem exists_primitiveRoot_Om (j : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ j) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  haveI : CharZero (Om l) := algebraRat.charZero _
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ j)

theorem Ks_eq_restrictScalars (K : FinExt l) (j : ℕ) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    Ks K j = ((↥(K0 K))⟮ζ⟯).restrictScalars ℚ_[l] := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, Ks]
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

theorem finrank_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ]
  have h1 : Module.finrank ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯) = (l - 1) * l ^ (j - 1) := by
    rw [IntermediateField.adjoin.finrank hint, minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ,
      natDegree_cyclotomic, Nat.totient_prime_pow hlp hj, mul_comm]
  rw [← h1]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯)).symm

theorem exists_chi_approx (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j) :
    ∃ g ∈ (K0 K).fixingSubgroup, ‖(χ g : ℚ_[l]) - u‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  let z : ℤ_[l] := ⟨u, hu.le⟩
  set a := z.appr j with ha
  have hza : ‖u - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).2 (PadicInt.appr_spec j z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have hlt : (l : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hl1 (by omega)
  have hna : ‖(a : ℚ_[l])‖ = 1 := by
    have h1 : (a : ℚ_[l]) = u + -(u - a) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hu, norm_neg,
      max_eq_left (hza.trans hlt.le)]
    rw [hu, norm_neg]
    exact (hza.trans_lt hlt).ne'
  have hcop : a.Coprime (l ^ j) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hlp.coprime_iff_not_dvd]
    intro hd
    have : ‖((a : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
    rw [Int.cast_natCast, hna] at this
    exact lt_irrefl _ this
  have hζa := hζ.pow_of_coprime a hcop
  have hconj : IsConjRoot ↥(K0 K) (ζ ^ a) ζ := by
    unfold IsConjRoot
    rw [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, minpoly_unramifiedSubfield_eq_cyclotomic K j hj _ hζa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ.restrictScalars ℚ_[l], fun x => σ.commutes x, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hχ (σ.restrictScalars ℚ_[l]) j ζ hζ.pow_eq_one
  have hab : ζ ^ a = ζ ^ b := hσ.symm.trans hb'
  have hmod : a ≡ b [MOD l ^ j] := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hpos.ne').pow_eq_pow_iff_modEq.1 hab
  have hba : ‖(b : ℚ_[l]) - a‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd ((b : ℤ) - a) j (p := l)).2
      (by exact_mod_cast hmod.dvd)
    simpa using this
  have h1 : (χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - u =
      ((χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - b) + (((b : ℚ_[l]) - a) + -(u - a)) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba ?_)
  rwa [norm_neg]

theorem exists_chi_eq (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hcont := (cyc_basic l χ hχ).2.1
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  have hcl : IsClosed ((K0 K).fixingSubgroup : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hc := (hcl.isCompact.image hcont).isClosed
  have hmem : u ∈ (fun g => (χ g : ℚ_[l])) '' ((K0 K).fixingSubgroup : Set (GQ l)) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
    obtain ⟨g, hg, hg'⟩ := exists_chi_approx K χ hχ u hu (n + 1) (by omega)
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine hg'.trans_lt (lt_of_le_of_lt ?_ hn)
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hl1.le (by push_cast; omega)
  exact hmem

theorem finrank_Ks_and_chi_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧
    ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 →
      ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u :=
  fun _ _ K => ⟨finrank_Ks K, exists_chi_eq K⟩

end GlobalTheory.Cyc
