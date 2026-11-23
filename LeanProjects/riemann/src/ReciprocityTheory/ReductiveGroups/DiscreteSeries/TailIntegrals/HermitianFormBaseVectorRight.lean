import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem hpk_out' {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mid' {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec' (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [hpk_out' k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [hpk_mid' k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem hpk_conjT' : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [conjTranspose_apply, Hpk, Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp

theorem herm_bvec (v : Fin (2 * r + k + 1) → ℂ) (q : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec q) v = star ((Hpk k r *ᵥ v) q) := by
  have hc : ∀ p, star (Hpk k r q p) = Hpk k r p q := fun p => by
    have := congrFun (congrFun (hpk_conjT' k r) p) q
    rwa [conjTranspose_apply] at this
  unfold herm bvec
  rw [mulVec_single_one]
  simp only [dotProduct, mulVec, star_sum, star_mul', hc, Pi.star_apply]
  exact Finset.sum_congr rfl fun p _ => mul_comm _ _

end hpk

section vec
variable (k r' : ℕ)

theorem goodRowsProjector_apply_eq_sum (p : Fin (2 * (1 + r') + k + 1)) : e0 k r' p = if p.val = 0 then 1 else 0 := by
  unfold e0 bvec
  rw [Pi.single_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff]
  simp [eI, a0]

theorem last_basis_apply (p : Fin (2 * (1 + r') + k + 1)) :
    es0 k r' p = if p.val = 2 * (1 + r') + k then 1 else 0 := by
  unfold es0 bvec
  rw [Pi.single_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff]
  simp [esI, a0]

theorem liftVec_apply (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    liftVec k 1 r' z p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then z ⟨p.val - 1, by omega⟩ else 0 :=
  rfl

theorem liftVec_lev (z : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' z (levPos k 1 r' i) = z i := by
  rw [liftVec_apply, dif_pos (by simp [levPos]; omega)]
  congr 1

theorem liftVec_out (z : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (h : p.val = 0 ∨ p.val = 2 * (1 + r') + k) : liftVec k 1 r' z p = 0 := by
  rw [liftVec_apply, dif_neg (by omega)]

theorem bvec_lev (j : Fin (2 * r' + k + 1)) : bvec (levPos k 1 r' j) = liftVec k 1 r' (bvec j) := by
  ext p
  rw [liftVec_apply]
  simp only [bvec, Pi.single_apply, Fin.ext_iff, levPos]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hermitian_form_base_vector_right (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u ⟨2 * (1 + r') + k, by omega⟩ := by
  unfold herm
  simp only [dotProduct, Pi.star_apply, goodRowsProjector_apply_eq_sum]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [hpk_mulVec']; simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
  · simp

theorem hermitianForm_mulVec_basisSum : Hpk k (1 + r') *ᵥ es0 k r' = e0 k r' := by
  ext p
  rw [hpk_mulVec', goodRowsProjector_apply_eq_sum, last_basis_apply, last_basis_apply]
  split_ifs <;> (try simp only at *) <;> first | rfl | (exfalso; omega) | simp

theorem hermitian_dual_base_vector_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (es0 k r') v = star (v ⟨0, by omega⟩) := by
  unfold herm
  rw [hermitianForm_mulVec_basisSum]
  simp only [dotProduct, Pi.star_apply, goodRowsProjector_apply_eq_sum]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
  · simp

end vec

section lev
variable (k r' : ℕ)

theorem levPos_val (j : Fin (2 * r' + k + 1)) : (levPos k 1 r' j).val = j.val + 1 := rfl

theorem levPos_inj : Function.Injective (levPos k 1 r') := by
  intro a b h; ext; have := congrArg Fin.val h; simp only [levPos_val] at this; omega

theorem sum_lev {M : Type*} [AddCommMonoid M] (F : Fin (2 * (1 + r') + k + 1) → M)
    (hF : ∀ q : Fin (2 * (1 + r') + k + 1), ¬(1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → F q = 0) :
    ∑ q, F q = ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) := by
  symm
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro q _ hq
  apply hF
  rintro ⟨h1, h2⟩
  apply hq
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  exact ⟨⟨q.val - 1, by omega⟩, by ext; simp only [levPos_val]; omega⟩

theorem sum_lev_le (F : Fin (2 * (1 + r') + k + 1) → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ∑ j : Fin (2 * r' + k + 1), F (levPos k 1 r' j) ≤ ∑ q, F q := by
  have e := Finset.sum_map Finset.univ ⟨levPos k 1 r', levPos_inj k r'⟩ F
  simp only [Function.Embedding.coeFn_mk] at e
  rw [← e]
  exact Finset.sum_le_univ_sum_of_nonneg hF

theorem ιLev_mulVec (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1)) :
    (ιLev k 1 r' g *ᵥ u) p = if h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 then
      (g *ᵥ fun j => u (levPos k 1 r' j)) ⟨p.val - 1, by omega⟩ else u p := by
  simp only [mulVec, dotProduct]
  by_cases h : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, sum_lev k r']
    · apply Finset.sum_congr rfl
      intro j _
      have hj : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
        rw [levPos_val]; omega
      simp only [ιLev, dif_pos h, dif_pos hj]
      congr 2
    · intro q hq
      simp only [ιLev, dif_pos h, dif_neg hq, zero_mul]
  · rw [dif_neg h]
    simp only [ιLev, dif_neg h]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; rw [if_neg (fun e => hb e.symm)]; simp
    · simp

theorem ιLev_liftVec (g : Mat k r') (z : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' z = liftVec k 1 r' (g *ᵥ z) := by
  ext p
  rw [ιLev_mulVec, liftVec_apply]
  split_ifs with h
  · have e : (fun j => liftVec k 1 r' z (levPos k 1 r' j)) = z := funext (liftVec_lev k r' z)
    rw [e, liftVec_apply, dif_pos h]
  · rw [liftVec_apply, dif_neg h]

theorem ιLev_fix (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ)
    (hu : ∀ q : Fin (2 * (1 + r') + k + 1), (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) → u q = 0) :
    ιLev k 1 r' g *ᵥ u = u := by
  ext p
  rw [ιLev_mulVec]
  split_ifs with h
  · have : (fun j => u (levPos k 1 r' j)) = 0 := by
      ext j; apply hu; rw [levPos_val]; omega
    rw [this, mulVec_zero, hu p h]; rfl
  · rfl

theorem levi_embedding_mulVec_e0 (g : Mat k r') : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' :=
  ιLev_fix k r' g _ fun q hq => by rw [goodRowsProjector_apply_eq_sum, if_neg (by omega)]

theorem levelEmbedding_mulVec_es0 (g : Mat k r') : ιLev k 1 r' g *ᵥ es0 k r' = es0 k r' :=
  ιLev_fix k r' g _ fun q hq => by rw [last_basis_apply, if_neg (by omega)]

theorem reflection_apply_entries (c : ℂ) (p q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c p q = if p.val = 0 ∧ q.val = 2 * (1 + r') + k then (star c)⁻¹
      else if p.val = 2 * (1 + r') + k ∧ q.val = 0 then c
      else if p = q ∧ 0 < p.val ∧ p.val < 2 * (1 + r') + k then 1 else 0 := rfl

theorem reflection_mulVec_levelPos (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    (w0 k r' c *ᵥ u) (levPos k 1 r' i) = u (levPos k 1 r' i) := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single (levPos k 1 r' i)]
  · rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_pos ⟨rfl, by rw [levPos_val]; omega, by rw [levPos_val]; omega⟩, one_mul]
  · intro b _ hb
    rw [reflection_apply_entries, if_neg (by rw [levPos_val]; omega), if_neg (by rw [levPos_val]; omega),
      if_neg (fun h => hb h.1.symm), zero_mul]
  · simp

theorem rankOneMatrix_last_coord (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (w0 k r' c *ᵥ u) ⟨2 * (1 + r') + k, by omega⟩ = c * u ⟨0, by omega⟩ := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · rw [reflection_apply_entries, if_neg (by simp only; omega), if_pos ⟨rfl, rfl⟩]
  · intro b _ hb
    have hb' : b.val ≠ 0 := fun h => hb (Fin.ext h)
    rw [reflection_apply_entries, if_neg (by simp only; omega), if_neg (by simp only; omega),
      if_neg (fun h => absurd h.2.2 (lt_irrefl _)), zero_mul]
  · simp

end lev

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
