import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LiftPfA

noncomputable section

namespace Formalism.MainNotions.N.Ln34.CyclotomicLifting

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

variable {l : ℕ} [Fact l.Prime]

theorem fix_of_mem_GK {K : FinExt l} {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ K.1) :
    σ x = x :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx

theorem Ks_stable (K : FinExt l) {σ : GQ l} (hσ : σ ∈ GK K) {x : Om l} (hx : x ∈ Ks K 1) :
    σ x ∈ Ks K 1 := by
  have hle : Ks K 1 ≤ (Ks K 1).map (σ.symm : Om l ≃ₐ[ℚ_[l]] Om l).toAlgHom := by
    unfold Ks
    refine sup_le ?_ ?_
    · intro y hy
      refine (IntermediateField.mem_map _).2 ⟨y, (le_sup_left : K0 K ≤ _) hy, ?_⟩
      have h1 : σ y = y := fix_of_mem_GK hσ (inf_le_left (a := K.1) (b := MaximalUnramifiedExtension l) hy)
      show σ.symm y = y
      rw [AlgEquiv.symm_apply_eq]
      exact h1.symm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      refine (IntermediateField.mem_map _).2 ⟨σ y, ?_, by simp⟩
      apply (le_sup_right : _ ≤ K0 K ⊔ _)
      apply IntermediateField.subset_adjoin
      show (σ y) ^ (l ^ 1) = 1
      rw [← map_pow, show y ^ (l ^ 1) = 1 from hy, map_one]
  obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 (hle hx)
  have hyx' : σ.symm y = x := hyx
  rw [← hyx', AlgEquiv.apply_symm_apply]
  exact hy

theorem GKin_normal (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) : (GKin hKK).Normal := by
  constructor
  intro n hn g
  rw [GKin, Subgroup.mem_subgroupOf] at hn ⊢
  rw [GK, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
  intro x hx
  have h1 : ((g : GQ l)⁻¹) x ∈ Ks K 1 := Ks_stable K (inv_mem g.2) hx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
  rw [hn _ h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

theorem range_inclusion_eq (K : FinExt l) (hKK : K.1 ≤ (cycL K).1) (hle : GK (cycL K) ≤ GK K) :
    (Subgroup.inclusion hle).range = GKin hKK := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Subgroup.mem_subgroupOf.2 y.2
  · intro hx
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩

theorem chi_cong (P : LocPrime l) (K : FinExt l) (g : GQ l) (hg : g ∈ GK (cycL K)) :
    ‖(P.χQ g : ℚ_[l]) - 1‖ ≤ (l : ℝ)⁻¹ := by
  have hp : l.Prime := Fact.out
  have hζl : P.ζQ 1 ^ (l ^ 1) = 1 := by
    have := P.ζQ_succ 0
    rw [P.ζQ_zero] at this
    simpa using this
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 (P.ζQ 1) hζl
  have hζK : P.ζQ 1 ∈ (cycL K).1 :=
    (le_sup_right : _ ≤ K0 K ⊔ _) (IntermediateField.subset_adjoin _ _ hζl)
  have hfix : g (P.ζQ 1) = P.ζQ 1 := fix_of_mem_GK hg hζK
  have hord : orderOf (P.ζQ 1) = l := orderOf_eq_prime (by simpa using hζl) P.ζQ_one
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      apply P.ζQ_one
      have h2 : P.ζQ 1 ^ 0 = P.ζQ 1 ^ 1 := by rw [pow_one, ← hga, hfix]
      rw [pow_zero, pow_one] at h2
      exact h2.symm
    · exact h
  have hζ0 : P.ζQ 1 ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_pos hp.pos 1).ne'] at hζl
    exact zero_ne_one hζl
  have h3 : P.ζQ 1 ^ (a - 1) = 1 := by
    have h4 : P.ζQ 1 ^ (a - 1) * P.ζQ 1 = 1 * P.ζQ 1 := by
      rw [← pow_succ, Nat.sub_add_cancel ha1, one_mul, ← hga, hfix]
    exact mul_right_cancel₀ hζ0 h4
  have hdvdN : l ∣ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  have hdvdN1 : l ^ 1 ∣ a - 1 := by rw [pow_one]; exact hdvdN
  have hcast : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by omega
  have h1 := (Padic.norm_int_le_pow_iff_dvd (p := l) ((a : ℤ) - 1) 1).2
    (by rw [hcast]; exact_mod_cast hdvdN1)
  have e : (P.χQ g : ℚ_[l]) - 1 = ((P.χQ g : ℚ_[l]) - (a : ℚ_[l])) + (((a : ℤ) - 1 : ℤ) : ℚ_[l]) := by
    push_cast; ring
  rw [e]
  refine ((Padic.nonarchimedean _ _).trans (max_le ha h1)).trans (le_of_eq ?_)
  simp

theorem v_ge_one (P : LocPrime l) (LL : FinExt l) (x : ℚ_[l]) (hx : ‖x‖ ≤ (l : ℝ)⁻¹) :
    (1 : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hy : ‖x / l‖ ≤ 1 := by
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos))]
    exact hx
  have hxy : x = (l : ℚ_[l]) * (x / l) := by field_simp
  have hyO : algebraMap ℚ_[l] ↥LL.1 (x / l) ∈ OL LL := by
    obtain ⟨y, hy'⟩ : ∃ y : ℤ_[l], (y : ℚ_[l]) = x / l := ⟨⟨x / l, hy⟩, rfl⟩
    rw [← hy', show (y : ℚ_[l]) = algebraMap ℤ_[l] ℚ_[l] y from rfl,
      ← IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap
  rw [hxy, map_mul, map_natCast, AddValuation.map_mul, P.v_l LL]
  exact le_add_of_nonneg_right ((P.v_O LL _).2 hyO)

theorem FildR_succ_le (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    FildR (P.PD K) T.ρ τ (a + 1) ≤ FildR (P.PD K) T.ρ τ a := by
  unfold FildR FilV
  refine inf_le_inf_left _ ?_
  have hle : ((P.PD K).Fil (a + 1)).restrictScalars ℚ_[l] ≤ ((P.PD K).Fil a).restrictScalars ℚ_[l] :=
    fun x hx => (P.PD K).Fil_anti a hx
  rintro x ⟨y, rfl⟩
  exact ⟨TensorProduct.AlgebraTensorModule.map LinearMap.id (Submodule.inclusion hle) y, by
    rw [← LinearMap.comp_apply, ← TensorProduct.AlgebraTensorModule.map_comp]
    rfl⟩

theorem multV_ne_zero (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (hfd : FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ)) (hj : IsJumpV (P.PD K) T.ρ τ a) :
    multV (P.PD K) T.ρ τ a ≠ 0 := by
  unfold multV
  have hle := FildR_succ_le P K LL T τ a
  have hlt : FildR (P.PD K) T.ρ τ (a + 1) < FildR (P.PD K) T.ρ τ a := lt_of_le_of_ne hle hj
  haveI := hfd
  haveI : FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T.ρ τ a) := Submodule.finiteDimensional_of_le inf_le_left
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

theorem isJump_of_multV (P : LocPrime l) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ)
    (h : multV (P.PD K) T.ρ τ a ≠ 0) : IsJumpV (P.PD K) T.ρ τ a := by
  intro he
  apply h
  unfold multV
  rw [he]
  simp

end Formalism.MainNotions.N.Ln34.CyclotomicLifting

end
