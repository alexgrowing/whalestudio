import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.propCker_avg {H k M : Type} [Group H] [Field k] [CharZero k] [AddCommGroup M] [Module k M]
    (ρ : Representation k H M) (hs : ∀ m, ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ x ∈ K, ρ x m = m) {w : M}
    (hw : w ∈ Submodule.span k {w | ∃ x m, w = ρ x m - m}) (hfix : ∀ x, ρ x w = w) : w = 0 := by
  have key : ∃ K0 : Subgroup H, K0.FiniteIndex ∧ ∀ (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)], K ≤ K0 →
      ∑ q : H ⧸ K, ρ q.out w = 0 := by
    clear hfix
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨x, m, rfl⟩ := h
      obtain ⟨K0, h0, h1⟩ := hs m
      refine ⟨K0, h0, fun K _ _ hK => ?_⟩
      simp only [map_sub]
      rw [Finset.sum_sub_distrib, sub_eq_zero,
        ← Equiv.sum_comp (Equiv.mulRight (x : H ⧸ K)) (fun q : H ⧸ K => ρ q.out m)]
      refine Finset.sum_congr rfl fun q _ => ?_
      have h2 : ((q * x).out)⁻¹ * (q.out * x) ∈ K := by
        rw [← QuotientGroup.eq]
        simp
      have h3 := h1 _ (hK h2)
      have h4 : q.out * x = (q * x).out * (((q * x).out)⁻¹ * (q.out * x)) := by group
      rw [Equiv.coe_mulRight, ← Module.End.mul_apply, ← map_mul, h4, map_mul, Module.End.mul_apply, h3]
    | zero => exact ⟨⊤, inferInstance, fun K _ _ _ => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨K1, h1, h1'⟩ := ha
      obtain ⟨K2, h2, h2'⟩ := hb
      refine ⟨K1 ⊓ K2, inferInstance, fun K _ _ hK => ?_⟩
      simp only [map_add]
      rw [Finset.sum_add_distrib, h1' K (hK.trans inf_le_left), h2' K (hK.trans inf_le_right), add_zero]
    | smul c a _ ha =>
      obtain ⟨K1, h1, h1'⟩ := ha
      refine ⟨K1, h1, fun K _ _ hK => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, h1' K hK, smul_zero]
  obtain ⟨K0, h0, h1⟩ := key
  haveI : Fintype (H ⧸ K0.normalCore) := Fintype.ofFinite _
  have h2 := h1 K0.normalCore K0.normalCore_le
  simp only [hfix, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_zero] at h2
  exact h2.resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

theorem UpperTheory.V.Hi.propCker :
    ∀ (G : Type) [Group G] (I : Iwa G) (k M : Type) [Field k] [CharZero k] [AddCommGroup M] [Module k M] (π : Representation k G M), I.Smooth π → ∀ v ∈ fixd π I.N, v ∈ I.jacKer π ↔ ∃ j : ℕ, (I.uOp π I.z ^ j) v = 0 := by
  intro G _ I k M _ _ _ _ π hsm v hv
  have mul : ∀ (g h : G) (w : M), π g (π h w) = π (g * h) w := fun g h w => by
    rw [map_mul π g h, Module.End.mul_apply]
  have hz : ∀ j : ℕ, I.z ^ j ∈ I.P := fun j => pow_mem I.z_mem j
  have hpow : ∀ j : ℕ, (I.uOp π I.z ^ j) v = I.uOp π (I.z ^ j) v := by
    intro j
    induction j with
    | zero => simpa using (uOpMul G I k M π 1 1 (one_mem _) (one_mem _) v hv).2.2.1.symm
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ',
        (uOpMul G I k M π _ _ I.z_mem (hz j) v hv).2.1]
  simp only [hpow]
  constructor
  · intro h
    let ρ : Representation k I.N M := π.comp I.N.subtype
    let J : Submodule k M := Submodule.span k {w | ∃ x m, w = ρ x m - m}
    have key : ∃ j0 : ℕ, ∀ j ≥ j0, π (I.z ^ j) v ∈ J := by
      clear hv hpow
      induction h using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        obtain ⟨j0, h0⟩ := I.exh x hx
        refine ⟨j0, fun j hj => ?_⟩
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hj
        have h1 := I.P_N _ (hz d) _ h0
        refine Submodule.subset_span ⟨⟨_, h1⟩, π (I.z ^ (d + j0)) m, ?_⟩
        show _ = π _ _ - _
        rw [map_sub, mul, mul]
        congr 3
        simp only [Subgroup.subtype_apply]
        group
      | zero => exact ⟨0, fun j _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨j1, h1⟩ := ha
        obtain ⟨j2, h2⟩ := hb
        refine ⟨max j1 j2, fun j hj => ?_⟩
        rw [map_add]
        exact add_mem (h1 j (le_of_max_le_left hj)) (h2 j (le_of_max_le_right hj))
      | smul c a _ ha =>
        obtain ⟨j1, h1⟩ := ha
        refine ⟨j1, fun j hj => ?_⟩
        rw [map_smul]
        exact Submodule.smul_mem _ _ (h1 j hj)
    obtain ⟨j, hj⟩ := key
    have hj := hj j le_rfl
    refine ⟨j, propCker_avg ρ ?_ ?_ ?_⟩
    · intro m
      obtain ⟨c, hc, -⟩ := hsm m
      exact ⟨(I.Nconj (I.z ^ c)).subgroupOf I.N, ⟨I.fin_N _ (hz c)⟩, fun x hx => hc x hx⟩
    · have hfin : ((I.Nconj (I.z ^ j)).subgroupOf I.N).FiniteIndex := ⟨I.fin_N _ (hz j)⟩
      haveI : Fintype (I.N ⧸ (I.Nconj (I.z ^ j)).subgroupOf I.N) := Fintype.ofFinite _
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun q _ => ?_
      have h1 : ρ q.out (π (I.z ^ j) v) - π (I.z ^ j) v ∈ J := Submodule.subset_span ⟨_, _, rfl⟩
      have h2 := add_mem h1 hj
      rw [sub_add_cancel] at h2
      rw [← mul]
      exact h2
    · intro x
      exact (uOpMul G I k M π _ 1 (hz j) (one_mem _) v hv).1 x x.2
  · rintro ⟨j, hj⟩
    have h1 := propCp G I k M π _ (hz j) v hv
    rw [hj, zero_sub, neg_mem_iff, Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 (I.fin_N _ (hz j)))] at h1
    have stab : ∀ t ∈ I.Tf, ∀ w ∈ I.jacKer π, π t w ∈ I.jacKer π := by
      intro t ht w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨x, hx, m, rfl⟩ := h
        refine Submodule.subset_span ⟨_, I.Tf_Nf t ht x hx, π t m, ?_⟩
        rw [map_sub, mul, mul]
        congr 3
        group
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    have h2 := stab _ (inv_mem (I.P_le _ (hz j))) _ h1
    rwa [mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
