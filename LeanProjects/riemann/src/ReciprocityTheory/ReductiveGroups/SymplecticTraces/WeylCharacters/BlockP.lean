import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.BlockCombStatement

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem bp_filter_eq_map {n : ℕ} (ε : Fin n → Bool) (b : Bool) :
    (univ.filter fun i : Fin n => ε i = b) =
      univ.map ((univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl).toEmbedding := by
  exact (Finset.map_orderEmbOfFin_univ _ rfl).symm

theorem bp_prod_blk {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (b : Bool)
    (g : Fin n → M) :
    ∏ i ∈ univ.filter (fun i : Fin n => ε i = b), g i = ∏ r, g (blk ε b r) := by
  rw [bp_filter_eq_map, Finset.prod_map]
  rfl

theorem bp_split {M : Type*} [CommMonoid M] {n : ℕ} (ε : Fin n → Bool) (F : Fin n → M) :
    ∏ i, F i = (∏ r, F (blk ε true r)) * ∏ r, F (blk ε false r) := by
  rw [← bp_prod_blk ε true F, ← bp_prod_blk ε false F,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => ε i = true)]
  congr 2
  ext i
  simp

theorem bp_blk_surj {n : ℕ} (ε : Fin n → Bool) (b : Bool) (i : Fin n) (h : ε i = b) :
    ∃ r, blk ε b r = i := by
  have hi : i ∈ univ.filter fun i : Fin n => ε i = b := by simp [h]
  rw [bp_filter_eq_map] at hi
  obtain ⟨r, _, hr⟩ := Finset.mem_map.mp hi
  exact ⟨r, hr⟩

theorem bp_blk_disj {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) (s : Fin (cnt ε false)) :
    blk ε true r ≠ blk ε false s := by
  intro h
  have h1 : ε (blk ε true r) = true := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = true) rfl r
    simpa [blk] using this
  have h2 : ε (blk ε false s) = false := by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = false) rfl s
    simpa [blk] using this
  rw [h, h2] at h1
  exact Bool.false_ne_true h1

theorem bp_wden {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) :
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) := by
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  have hsame : ∀ (b : Bool) (r r' : Fin (cnt ε b)),
      (if blk ε b r < blk ε b r' ∧ ε (blk ε b r) = ε (blk ε b r') then t (blk ε b r) - t (blk ε b r') else 1) =
        (if r < r' then (t ∘ blk ε b) r - (t ∘ blk ε b) r' else 1) := by
    intro b r r'
    rw [hmem b r, hmem b r']
    simp only [and_true, Function.comp_apply, (blk_strictMono ε b).lt_iff_lt]
  have hother : ∀ (b b' : Bool), b ≠ b' → ∀ (r : Fin (cnt ε b)) (s : Fin (cnt ε b')),
      (if blk ε b r < blk ε b' s ∧ ε (blk ε b r) = ε (blk ε b' s) then t (blk ε b r) - t (blk ε b' s) else 1) = 1 := by
    intro b b' hbb r s
    rw [if_neg]
    rintro ⟨_, h⟩
    rw [hmem b r, hmem b' s] at h
    exact hbb h
  unfold wdenK wden
  rw [bp_split ε]
  congr 1
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother true false (by decide) r s), mul_one]
    exact Finset.prod_congr rfl fun r' _ => hsame true r r'
  · refine Finset.prod_congr rfl fun r _ => ?_
    rw [bp_split ε]
    rw [Finset.prod_eq_one (fun s _ => hother false true (by decide) r s), one_mul]
    exact Finset.prod_congr rfl fun r' _ => hsame false r r'

theorem bp_rho {n : ℕ} (ε : Fin n → Bool) (b : Bool) : rhoK ε ∘ blk ε b = delta (cnt ε b) := by
  have hmem : ∀ s : Fin (cnt ε b), ε (blk ε b s) = b := fun s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  funext r
  simp only [Function.comp_apply, rhoK, delta, hmem r]
  have hset : (univ.filter fun j : Fin n => blk ε b r < j ∧ ε j = b) =
      (Finset.Ioi r).map ⟨blk ε b, (blk_strictMono ε b).injective⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_Ioi,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hlt, hj⟩
      obtain ⟨s, hs⟩ := bp_blk_surj ε b j hj
      rw [← hs] at hlt
      exact ⟨s, (blk_strictMono ε b).lt_iff_lt.mp hlt, hs⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(blk_strictMono ε b) hs, hmem s⟩
  rw [hset, Finset.card_map, Fin.card_Ioi]
  have := r.isLt
  omega

theorem bp_alt_eq_sum {K : Type*} [Field K] (n : ℕ) (a : Fin n → ℤ) (t : Fin n → K) :
    alt n a t = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i := by
  unfold alt
  rw [Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [Matrix.of_apply]

def bp_e {n : ℕ} (ε : Fin n → Bool) : Fin (cnt ε true) ⊕ Fin (cnt ε false) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (blk ε true) (blk ε false)) (by
    constructor
    · rintro (r | r) (s | s) h
      · exact congrArg Sum.inl ((blk_strictMono ε true).injective h)
      · exact absurd h (bp_blk_disj ε r s)
      · exact absurd h.symm (bp_blk_disj ε s r)
      · exact congrArg Sum.inr ((blk_strictMono ε false).injective h)
    · intro i
      cases hb : ε i
      · obtain ⟨r, hr⟩ := bp_blk_surj ε false i hb
        exact ⟨Sum.inr r, hr⟩
      · obtain ⟨r, hr⟩ := bp_blk_surj ε true i hb
        exact ⟨Sum.inl r, hr⟩)

theorem bp_e_inl {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε true)) :
    bp_e ε (Sum.inl r) = blk ε true r := rfl

theorem bp_e_inr {n : ℕ} (ε : Fin n → Bool) (r : Fin (cnt ε false)) :
    bp_e ε (Sum.inr r) = blk ε false r := rfl

theorem bp_phi_inl {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε true)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε true r) = blk ε true (α r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inl ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inl, bp_e_inl]

theorem bp_phi_inr {n : ℕ} (ε : Fin n → Bool) (α : Equiv.Perm (Fin (cnt ε true)))
    (β : Equiv.Perm (Fin (cnt ε false))) (r : Fin (cnt ε false)) :
    (bp_e ε).permCongr (Equiv.Perm.sumCongr α β) (blk ε false r) = blk ε false (β r) := by
  rw [Equiv.permCongr_apply, ← bp_e_inr ε r, Equiv.symm_apply_apply, Equiv.Perm.sumCongr_apply,
    Sum.map_inr, bp_e_inr]

theorem bp_num {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) :
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) := by
  classical
  have hmem : ∀ (b : Bool) (s : Fin (cnt ε b)), ε (blk ε b s) = b := fun b s => by
    have := Finset.orderEmbOfFin_mem (univ.filter fun i : Fin n => ε i = b) rfl s
    simpa [blk] using this
  rw [bp_alt_eq_sum, bp_alt_eq_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  unfold numK
  symm
  refine Finset.sum_bij (fun p _ => (bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    obtain ⟨x, rfl⟩ := (bp_e ε).surjective i
    rcases x with r | r
    · rw [bp_e_inl, bp_phi_inl, hmem, hmem]
    · rw [bp_e_inr, bp_phi_inr, hmem, hmem]
  · intro p _ q _ h
    exact Equiv.Perm.sumCongrHom_injective ((Equiv.permCongr (bp_e ε)).injective h)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hmaps : Set.MapsTo ((bp_e ε).symm.permCongr σ) (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨r, rfl⟩
      obtain ⟨r', hr'⟩ := bp_blk_surj ε true (σ (blk ε true r)) (by rw [hσ, hmem])
      refine ⟨r', ?_⟩
      rw [Equiv.permCongr_apply, Equiv.symm_symm, bp_e_inl, ← hr', ← bp_e_inl, Equiv.symm_apply_apply]
    obtain ⟨q, hq⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hmaps
    refine ⟨q, Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    have hq' : Equiv.Perm.sumCongr q.1 q.2 = (bp_e ε).symm.permCongr σ := hq
    rw [hq']
    ext i
    simp [Equiv.permCongr_apply]
  · intro p _
    rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
      bp_split ε (fun i => t (((bp_e ε).permCongr (Equiv.Perm.sumCongr p.1 p.2)) i) ^ a i)]
    simp only [bp_phi_inl, bp_phi_inr, Function.comp_apply, Units.val_mul, Int.cast_mul]
    ring

theorem blockComb : BlockCombStatement := by
  intro K _ n ε a t
  exact ⟨bp_wden ε t, bp_num ε a t, bp_rho ε⟩

end ReciprocityTheory.ChartRestriction.TR.Weyl
