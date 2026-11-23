import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

open Matrix Filter Topology GlobalTheory.WeilM
open scoped Pointwise

noncomputable section
namespace PositivityTheory.ThKEst.W

section Rank
variable {k : Type} [Field k] {n d : ℕ}

theorem rank_iff_right (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, Y * C = 1 := by
  constructor
  · intro h
    have hr : LinearMap.range Y.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [Module.finrank_fin_fun]
      exact h
    have hsurj : Function.Surjective Y.mulVecLin := LinearMap.range_eq_top.mp hr
    choose c hc using fun j : Fin n => hsurj (Pi.single j 1)
    refine ⟨Matrix.of fun a j => c j a, ?_⟩
    ext i j
    have h3 := congrFun (hc j) i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct] at h3
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [h3, Pi.single_apply]
  · rintro ⟨C, hC⟩
    apply le_antisymm (Matrix.rank_le_height Y)
    calc n = (1 : Matrix (Fin n) (Fin n) k).rank := by rw [Matrix.rank_one, Fintype.card_fin]
      _ = (Y * C).rank := by rw [hC]
      _ ≤ Y.rank := Matrix.rank_mul_le_left Y C

theorem rank_iff_det (Y : Matrix (Fin n) (Fin d) k) : Y.rank = n ↔ ∃ C : Matrix (Fin d) (Fin n) k, (Y * C).det ≠ 0 := by
  rw [rank_iff_right]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, by rw [hC, det_one]; exact one_ne_zero⟩
  · rintro ⟨C, hC⟩
    refine ⟨C * (Y * C)⁻¹, ?_⟩
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC)]

theorem rank_of_mul (A : Matrix (Fin n) (Fin n) k) (Y : Matrix (Fin n) (Fin d) k) (B : Matrix (Fin d) (Fin d) k)
    (h : (A * Y * B).rank = n) : Y.rank = n := by
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (A * Y * B).rank := h.symm
    _ ≤ (A * Y).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Y.rank := Matrix.rank_mul_le_right _ _

theorem rank_neg_full {Y : Matrix (Fin n) (Fin d) k} (h : (-Y).rank = n) : Y.rank = n := by
  apply rank_of_mul (-1) Y 1
  simpa using h

theorem rank_of_map {E : Type} [Field E] (t : E →+* k) (x : Matrix (Fin n) (Fin d) E) (h : (x.map t).rank = n) :
    x.rank = n := by
  rw [← Matrix.rank_transpose] at h ⊢
  have hinj : Function.Injective ((x.map t)ᵀ.mulVecLin) := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker ((x.map t)ᵀ.mulVecLin)
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank k (LinearMap.range ((x.map t)ᵀ.mulVecLin)) = n := h
    omega
  have hinj2 : Function.Injective (xᵀ.mulVecLin) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h3 : (x.map t)ᵀ.mulVecLin (⇑t ∘ c) = 0 := by
      funext j
      have h4 := congrFun hc j
      simp only [Matrix.mulVecLin_apply, Pi.zero_apply] at h4 ⊢
      rw [← Matrix.transpose_map, ← RingHom.map_mulVec, h4, map_zero]
    have h5 := hinj (h3.trans (map_zero _).symm)
    funext i
    have h6 := congrFun h5 i
    exact (map_eq_zero t).mp h6
  show Module.finrank E (LinearMap.range xᵀ.mulVecLin) = n
  rw [LinearMap.finrank_range_of_inj hinj2, Module.finrank_fin_fun]

theorem isOpen_rank [TopologicalSpace k] [IsTopologicalRing k] [T1Space k] :
    IsOpen {Y : Matrix (Fin n) (Fin d) k | Y.rank = n} := by
  have hset : {Y : Matrix (Fin n) (Fin d) k | Y.rank = n} =
      ⋃ C : Matrix (Fin d) (Fin n) k, {Y | (Y * C).det ≠ 0} := by
    ext Y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, rank_iff_det]
  rw [hset]
  refine isOpen_iUnion fun C => ?_
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det (continuous_id.matrix_mul continuous_const))

end Rank

section Cut
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {n d : ℕ}

theorem exists_dual (O : ValuationSubring k) (hO : IsCompact (O : Set k)) (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U)
    (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1) {V : Set (Matrix (Fin n) (Fin d) k)}
    (hV : V ∈ 𝓝 0) : ∃ (K : Set (Matrix (Fin n) (Fin d) k)) (Λ : OpenAddSubgroup (Matrix (Fin n) (Fin d) k)),
      (∀ Y, Y ∈ Λ ↔ ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1) ∧ (Λ : Set _) ⊆ V := by
  classical
  have hM : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ O} := by
    have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin d => hO
    simp only [Set.pi, Set.mem_univ, true_imp_iff, Set.mem_setOf_eq] at this
    exact this
  have h1 : ∀ᶠ a in 𝓝 (0 : k), ∀ Y ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ O}, a • Y ∈ V :=
    hM.eventually_forall_of_forall_eventually fun Y _ =>
      (continuous_smul (M := k) (X := Matrix (Fin n) (Fin d) k)).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨a, ha0, ha⟩ := hne _ h1
  let K := (fun Y : Matrix (Fin n) (Fin d) k => (b / a) • Y) '' {Y | ∀ i j, Y i j ∈ O}
  have hK : IsCompact K := hM.image (continuous_const_smul _)
  let Λ : AddSubgroup (Matrix (Fin n) (Fin d) k) :=
    { carrier := {Y | ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1}
      add_mem' := fun h h' U hU => by rw [Matrix.add_mul, trace_add, AddChar.map_add_eq_mul, h U hU, h' U hU, one_mul]
      zero_mem' := fun U _ => by simp
      neg_mem' := fun h U hU => by rw [Matrix.neg_mul, trace_neg, AddChar.map_neg_eq_inv, h U hU, inv_one] }
  have h2 : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) k), ∀ U ∈ K, ψ (trace (Y * Uᵀ)) = 1 :=
    hK.eventually_forall_of_forall_eventually fun U _ => by
      have hc : Continuous fun z : Matrix (Fin n) (Fin d) k × Matrix (Fin n) (Fin d) k => trace (z.1 * z.2ᵀ) :=
        (continuous_fst.matrix_mul continuous_snd.matrix_transpose).matrix_trace
      simpa using (hψ.comp_continuous hc).eventually_eq (0, U)
  refine ⟨K, ⟨Λ, Λ.isOpen_of_mem_nhds h2⟩, fun _ => Iff.rfl, fun Y hY => ?_⟩
  have : ∀ i j, (a⁻¹ • Y) i j ∈ O := fun i j => by
    by_contra hn
    have h3 := (O.mem_or_inv_mem _).resolve_left hn
    have hy : Y i j ≠ 0 := fun h => hn (by simp [h])
    have h4 := hY _ ⟨Matrix.single i j ((a⁻¹ • Y) i j)⁻¹, fun i' j' => by
      rw [Matrix.single_apply]; split_ifs
      · exact h3
      · exact zero_mem _, rfl⟩
    apply hb
    rw [← h4]
    congr 1
    simp only [transpose_smul, Matrix.mul_smul, transpose_single, trace_smul, trace_mul_single, smul_eq_mul,
      Matrix.smul_apply, op_smul_eq_mul]
    field_simp
  have := ha _ this
  rwa [smul_smul, mul_inv_cancel₀ ha0, one_smul] at this

theorem exists_cut [CharZero k] (O : ValuationSubring k) (hO : IsCompact (O : Set k))
    (hne : ∀ U ∈ 𝓝 (0 : k), ∃ a ≠ 0, a ∈ U) (ψ : AddChar k ℂ) (hψ : IsLocallyConstant ψ) {b : k} (hb : ψ b ≠ 1)
    {f : Matrix (Fin n) (Fin d) k → ℂ} (hf : f ∈ SB _) (h0 : ∀ Y, Y.rank ≠ n → f Y = 0) :
    ∃ (m : ℕ) (g : Fin m → Matrix (Fin n) (Fin d) k → ℂ), f = ∑ i, g i ∧ ∀ i, g i ∈ SB _ ∧ (∀ Y, f Y = 0 → g i Y = 0) ∧
      ∃ Y₀, ∀ Z : Matrix (Fin n) (Fin d) k, Z.rank ≠ n → ∃ U : Matrix (Fin n) (Fin d) k,
        (∀ Y, g i Y ≠ 0 → ψ (trace (Y * Uᵀ)) = ψ (trace (Y₀ * Uᵀ))) ∧ ψ (trace ((Z - (Y₀ + Y₀)) * Uᵀ)) ≠ 1 := by
  classical
  have hS : IsCompact {Y | f Y ≠ 0} :=
    hf.2.isCompact.of_isClosed_subset (hf.1.isClopen_fiber 0).isOpen.isClosed_compl (subset_tsupport _)
  obtain ⟨V, hV, hVS⟩ := compact_open_separated_add_right (hS.image (f := fun Y => Y + Y) (by fun_prop))
    (isOpen_rank (k := k) (n := n) (d := d)) (by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨C, hC⟩ := (rank_iff_right Y).1 (by by_contra h; exact hY (h0 Y h))
      refine (rank_iff_right _).2 ⟨(2⁻¹ : k) • C, ?_⟩
      rw [Matrix.mul_smul, Matrix.add_mul, hC, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul])
  obtain ⟨K, Λ, hΛ, hΛV⟩ := exists_dual O hO hne ψ hψ hb hV
  let Q := Matrix (Fin n) (Fin d) k ⧸ Λ.toAddSubgroup
  haveI : DiscreteTopology Q := QuotientAddGroup.discreteTopology Λ.isOpen
  let p : Matrix (Fin n) (Fin d) k → Q := QuotientAddGroup.mk
  have hp : Continuous p := QuotientAddGroup.continuous_mk
  have hT : (p '' {Y | f Y ≠ 0}).Finite := (hS.image hp).finite_of_discrete
  let T := hT.toFinset
  let q : Fin T.card → Q := fun i => (T.equivFin.symm i).1
  refine ⟨T.card, fun i Y => if p Y = q i then f Y else 0, ?_, fun i => ⟨⟨?_, ?_⟩, fun Y hY => by simp [hY], ?_⟩⟩
  · funext Y
    rw [Finset.sum_apply, T.equivFin.symm.sum_comp (fun s => if p Y = s.1 then f Y else 0),
      Finset.sum_coe_sort T (fun s => if p Y = s then f Y else 0), Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra h'
      exact h (hT.mem_toFinset.2 ⟨Y, h', rfl⟩)
  · exact (((IsLocallyConstant.iff_continuous p).2 hp).prodMk hf.1).comp fun z => if z.1 = q i then z.2 else 0
  · exact HasCompactSupport.intro hS fun Y hY => by simp [not_not.1 hY]
  · obtain ⟨Y₀, hY₀, e⟩ := hT.mem_toFinset.1 (T.equivFin.symm i).2
    refine ⟨Y₀, fun Z hZ => ?_⟩
    have : Z - (Y₀ + Y₀) ∉ Λ := fun h => hZ (hVS ⟨Y₀ + Y₀, ⟨Y₀, hY₀, rfl⟩, _, hΛV h, add_sub_cancel _ _⟩)
    rw [hΛ] at this
    push Not at this
    obtain ⟨U, hU, h⟩ := this
    refine ⟨U, fun Y hY => ?_, h⟩
    have h1 : p Y₀ = p Y := by
      by_contra h'
      exact hY (if_neg fun h'' => h' (e.trans h''.symm))
    have h2 := (hΛ _).1 (QuotientAddGroup.eq.1 h1) U hU
    rw [show Y = Y₀ + (-Y₀ + Y) by abel, Matrix.add_mul, trace_add, AddChar.map_add_eq_mul, h2, mul_one]

end Cut

end PositivityTheory.ThKEst.W
end
