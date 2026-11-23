import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace YoungTableau

section Gen

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {X : Type} [Fintype X] [DecidableEq X]
  {C : Type} [DecidableEq C]

def ColInj (col : X → C) (J : X → Fin n) : Prop := ∀ p q, col p = col q → J p = J q → p = q

theorem mem_colG (col : X → C) (π : Equiv.Perm X) : π ∈ colG col ↔ ∀ p, col (π p) = col p := by
  simp [colG]

theorem alt_perm (col : X → C) (ξ : TV n M X) (J : X → Fin n) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    alt (colG col) ξ (J ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℂ) • alt (colG col) ξ J := by
  have hπ' := (mem_colG col π).1 hπ
  rw [alt_apply, alt_apply, Finset.smul_sum]
  refine Finset.sum_nbij' (fun σ => π * σ) (fun τ => π⁻¹ * τ) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [mem_colG] at hσ ⊢
    intro p
    simp only [Equiv.Perm.mul_apply]
    rw [hπ', hσ]
  · intro τ hτ
    rw [mem_colG] at hτ ⊢
    intro p
    have h := hπ' (π⁻¹ (τ p))
    rw [Equiv.Perm.mul_apply, ← h]
    simp [hτ]
  · intro σ _
    simp
  · intro τ _
    simp
  · intro σ _
    simp only [Equiv.Perm.coe_mul, Function.comp_assoc, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul, smul_smul]
    congr 1
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]

theorem alt_dup (col : X → C) (ξ : TV n M X) (J : X → Fin n) (p q : X) (hpq : p ≠ q) (hc : col p = col q)
    (hJ : J p = J q) : alt (colG col) ξ J = 0 := by
  have ht : Equiv.swap p q ∈ colG col := by
    rw [mem_colG]
    intro r
    rcases eq_or_ne r p with rfl | hrp
    · simp [hc]
    rcases eq_or_ne r q with rfl | hrq
    · simp [hc]
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]
  have hJt : J ∘ Equiv.swap p q = J := by
    funext r
    simp only [Function.comp_apply]
    rcases eq_or_ne r p with rfl | hrp
    · simp [hJ]
    rcases eq_or_ne r q with rfl | hrq
    · simp [hJ]
    · rw [Equiv.swap_apply_of_ne_of_ne hrp hrq]
  have h := alt_perm col ξ J _ ht
  rw [hJt, Equiv.Perm.sign_swap hpq] at h
  have h2 : (2 : ℂ) • alt (colG col) ξ J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

private theorem injOn_col_fiber_of_isTab (col : X → C) (b : X → Fin n) (hT : IsTab col b) (c : C) :
    Set.InjOn b ↑(Finset.univ.filter (fun x => col x = c)) := by
  unfold IsTab at hT
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact hT.1 x y (hx.trans hy.symm) hxy

private theorem card_col_fiber_sub_le_of_isTab (col : X → C) (b : X → Fin n) (hT : IsTab col b) (x : X) :
    n - (Finset.univ.filter (fun y => col y = col x)).card ≤ (b x : ℕ) := by
  have hinj := injOn_col_fiber_of_isTab col b hT (col x)
  unfold IsTab at hT
  have hsub : Finset.Ici (b x) ⊆ (Finset.univ.filter (fun y => col y = col x)).image b := by
    intro i hi
    rw [Finset.mem_Ici] at hi
    rcases hi.lt_or_eq with hlt | heq
    · obtain ⟨q, hq, hbq⟩ := hT.2 x i hlt
      exact Finset.mem_image.mpr ⟨q, by simp [hq], hbq⟩
    · exact Finset.mem_image.mpr ⟨x, by simp, heq⟩
  have h := Finset.card_le_card hsub
  rw [Fin.card_Ici, Finset.card_image_of_injOn hinj] at h
  omega

private theorem exists_mem_col_fiber_eq_of_isTab_of_le (col : X → C) (b : X → Fin n) (hT : IsTab col b) (c : C) (j : Fin n)
    (hj : n - (Finset.univ.filter (fun y => col y = c)).card ≤ (j : ℕ)) :
    ∃ x, col x = c ∧ b x = j := by
  have hinj := injOn_col_fiber_of_isTab col b hT c
  unfold IsTab at hT
  by_contra hne
  push_neg at hne
  have hsub : (Finset.univ.filter (fun y => col y = c)).image b ⊆ Finset.Ioi j := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Finset.mem_Ioi]
    rcases lt_trichotomy (b x) j with hlt | heq | hgt
    · obtain ⟨q, hq, hbq⟩ := hT.2 x j hlt
      exact absurd hbq (hne q (hq.trans hx))
    · exact absurd heq (hne x hx)
    · exact hgt
  have h := Finset.card_le_card hsub
  rw [Fin.card_Ioi, Finset.card_image_of_injOn hinj] at h
  have := j.isLt
  omega

theorem exists_perm (col : X → C) (b : X → Fin n) (hT : IsTab col b) (ζ : Equiv.Perm X)
    (hJ : ColInj col (b ∘ ζ)) : ∃ π ∈ colG col, b ∘ π = b ∘ ζ := by
  unfold ColInj at hJ
  have key : ∀ p, ∃ q, col q = col p ∧ b q = b (ζ p) := by
    by_contra hne
    push_neg at hne
    obtain ⟨p0, hp0⟩ := hne
    have hsmall : (Finset.univ.filter (fun y => col y = col p0)).card < n - (b (ζ p0) : ℕ) := by
      by_contra h
      push_neg at h
      obtain ⟨q, hq, hbq⟩ := exists_mem_col_fiber_eq_of_isTab_of_le col b hT (col p0) (b (ζ p0)) (by omega)
      exact hp0 q hq hbq
    have hfib : ∀ s : Finset X,
        s.card = ∑ c ∈ Finset.univ.image col, (s.filter (fun a => col a = c)).card := by
      intro s
      apply Finset.card_eq_sum_card_fiberwise
      intro x _
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem col (Finset.mem_univ x))
    have heq : (Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).card =
        (Finset.univ.filter (fun x => b (ζ p0) < b x)).card := by
      apply Finset.card_nbij' ζ ζ.symm
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] at hx ⊢
        exact hx
      · intro x _
        simp
      · intro x _
        simp
    have hsubR : ∀ c, (Finset.univ.filter (fun y => col y = c)).card < n - (b (ζ p0) : ℕ) →
        (Finset.univ.filter (fun y => col y = c)).card ≤
          ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).card := by
      intro c hA
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨?_, hx⟩
      have h2 := card_col_fiber_sub_le_of_isTab col b hT x
      rw [hx] at h2
      show (b (ζ p0) : ℕ) < b x
      omega
    have hle : ∀ c ∈ Finset.univ.image col,
        ((Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).filter (fun a => col a = c)).card ≤
        ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).card := by
      intro c _
      by_cases hA : (Finset.univ.filter (fun y => col y = c)).card < n - (b (ζ p0) : ℕ)
      · calc _ ≤ (Finset.univ.filter (fun y => col y = c)).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              exact hx.2
          _ ≤ _ := hsubR c hA
      · push_neg at hA
        calc _ ≤ (Finset.Ioi (b (ζ p0))).card := by
              apply Finset.card_le_card_of_injOn (fun x => b (ζ x))
              · intro x hx
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi] at hx ⊢
                exact hx.1
              · intro x hx y hy hxy
                simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
                exact hJ x y (hx.2.trans hy.2.symm) hxy
          _ ≤ (((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = c)).image b).card := by
              apply Finset.card_le_card
              intro j hj
              rw [Finset.mem_Ioi] at hj
              have hj' : (b (ζ p0) : ℕ) < j := hj
              obtain ⟨x, hx, hbx⟩ := exists_mem_col_fiber_eq_of_isTab_of_le col b hT c j (by omega)
              refine Finset.mem_image.mpr ⟨x, ?_, hbx⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨?_, hx⟩
              rw [hbx]
              exact hj
          _ ≤ _ := Finset.card_image_le
    have hlt : ((Finset.univ.filter (fun x => b (ζ p0) < b (ζ x))).filter (fun a => col a = col p0)).card <
        ((Finset.univ.filter (fun x => b (ζ p0) < b x)).filter (fun a => col a = col p0)).card := by
      calc _ ≤ ((Finset.univ.filter (fun y => col y = col p0)).erase p0).card := by
              apply Finset.card_le_card
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
              refine ⟨?_, hx.2⟩
              rintro rfl
              exact lt_irrefl _ hx.1
          _ < (Finset.univ.filter (fun y => col y = col p0)).card :=
              Finset.card_erase_lt_of_mem (by simp)
          _ ≤ _ := hsubR (col p0) hsmall
    have hsum := Finset.sum_lt_sum hle ⟨col p0, Finset.mem_image_of_mem col (Finset.mem_univ p0), hlt⟩
    rw [← hfib, ← hfib, heq] at hsum
    exact lt_irrefl _ hsum
  choose f hf1 hf2 using key
  have hinj : Function.Injective f := by
    intro p p' h
    apply hJ p p'
    · rw [← hf1 p, ← hf1 p', h]
    · show b (ζ p) = b (ζ p')
      rw [← hf2 p, ← hf2 p', h]
  refine ⟨Equiv.ofBijective f hinj.bijective_of_finite, ?_, ?_⟩
  · rw [mem_colG]
    intro p
    exact hf1 p
  · funext p
    exact hf2 p

def sg (col : X → C) (b : X → Fin n) (v : X → Fin n) : ℤ :=
  ∑ π ∈ colG col, if b ∘ π = v then (Equiv.Perm.sign π : ℤ) else 0

theorem sg_perm (col : X → C) (b : X → Fin n) (hI : ColInj col b) (π : Equiv.Perm X) (hπ : π ∈ colG col) :
    sg col b (b ∘ π) = Equiv.Perm.sign π := by
  unfold sg
  rw [Finset.sum_eq_single π]
  · simp
  · intro σ hσ hne
    rw [if_neg]
    intro h
    apply hne
    ext p
    have hσ' := (mem_colG col σ).1 hσ p
    have hπ' := (mem_colG col π).1 hπ p
    exact hI _ _ (hσ'.trans hπ'.symm) (congrFun h p)
  · intro h
    exact absurd hπ h

theorem sg_zero (col : X → C) (b : X → Fin n) (v : X → Fin n) (h : ¬ ∃ π ∈ colG col, b ∘ π = v) :
    sg col b v = 0 := by
  unfold sg
  refine Finset.sum_eq_zero fun π hπ => ?_
  rw [if_neg]
  exact fun h' => h ⟨π, hπ, h'⟩

theorem isTab_comp {Y : Type} (col : X → C) (b : X → Fin n) (hT : IsTab col b) (e : Y → X)
    (he : Function.Injective e) (hcl : ∀ q y, col q = col (e y) → ∃ y', q = e y') : IsTab (col ∘ e) (b ∘ e) := by
  unfold IsTab at hT ⊢
  obtain ⟨h1, h2⟩ := hT
  refine ⟨fun p q hc hb => he (h1 _ _ hc hb), fun p i hi => ?_⟩
  obtain ⟨q, hq, hbq⟩ := h2 (e p) i hi
  obtain ⟨y', rfl⟩ := hcl q p hq
  exact ⟨y', hq, hbq⟩

end Gen

end YoungTableau

end PositivityTheory.Rg.Cz

end
