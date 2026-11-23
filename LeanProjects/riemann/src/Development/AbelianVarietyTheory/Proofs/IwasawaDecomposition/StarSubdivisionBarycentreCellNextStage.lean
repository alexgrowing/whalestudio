import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

section Enumerate

theorem exists_enum_fin {n : ℕ} (P : Fin n → Prop) :
    ∃ (p : ℕ) (e : Fin p ↪ Fin n), ∀ k, P k ↔ k ∈ Set.range e := by
  classical
  refine ⟨(Finset.univ.filter P).card, ((Finset.univ.filter P).orderEmbOfFin rfl).toEmbedding, fun k => ?_⟩
  have := (Finset.univ.filter P).range_orderEmbOfFin rfl
  change _ ↔ k ∈ Set.range ((Finset.univ.filter P).orderEmbOfFin rfl)
  rw [this]
  simp

theorem exists_append_emb {p r b a : ℕ} (eS : Fin p ↪ Fin b) (eT : Fin r ↪ Fin a) :
    ∃ s : Fin (p + r) ↪ Fin (b + a), (∀ k, s (Fin.castAdd r k) = Fin.castAdd a (eS k)) ∧
      ∀ j, s (Fin.natAdd p j) = Fin.natAdd b (eT j) := by
  refine ⟨(finSumFinEquiv.symm.toEmbedding.trans (Function.Embedding.sumMap eS eT)).trans finSumFinEquiv.toEmbedding,
    fun k => ?_, fun j => ?_⟩
  · simp
  · simp

theorem exists_extend_coeff {R : Type*} [Semiring R] {p n : ℕ} (e : Fin p ↪ Fin n) (d : Fin p → R) :
    ∃ r : Fin n → R, (∀ j, r (e j) = d j) ∧ (∀ x, x ∉ Set.range e → r x = 0) ∧
      ∀ {M : Type _} [AddCommMonoid M] [Module R M] (f : Fin n → M), ∑ x, r x • f x = ∑ j, d j • f (e j) := by
  classical
  have h1 : ∀ j, Function.extend e d 0 (e j) = d j := fun j => e.injective.extend_apply _ _ _
  have h2 : ∀ x, x ∉ Set.range e → Function.extend e d 0 x = 0 := fun x hx => by
    rw [Function.extend_apply' _ _ _ (by simpa using hx)]
    rfl
  refine ⟨Function.extend e d 0, h1, h2, fun f => ?_⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun x _ hx => ?_), Finset.sum_map]
  · simp only [Function.Embedding.coeFn_mk, h1]
  · rw [h2 x (fun ⟨j, hj⟩ => hx (by simp [← hj])), zero_smul]

theorem exists_perm_append_cons {α : Type*} {p q : ℕ} (x : α) (f : Fin p → α) (g : Fin q → α) :
    ∃ e : Fin (p + (q + 1)) ≃ Fin (p + q + 1), ∀ i,
      Fin.append f (Fin.cons x g : Fin (q + 1) → α) i = (Fin.cons x (Fin.append f g) : Fin (p + q + 1) → α) (e i) := by
  let F : Fin (p + (q + 1)) → Fin (p + q + 1) := fun i =>
    if h : (i : ℕ) < p then ⟨i + 1, by omega⟩ else if (i : ℕ) = p then ⟨0, by omega⟩ else ⟨i, by have := i.isLt; omega⟩
  let G : Fin (p + q + 1) → Fin (p + (q + 1)) := fun j =>
    if (j : ℕ) = 0 then ⟨p, by omega⟩ else if (j : ℕ) ≤ p then ⟨j - 1, by omega⟩ else ⟨j, by have := j.isLt; omega⟩
  have hF : ∀ i, (F i : ℕ) = if (i : ℕ) < p then (i : ℕ) + 1 else if (i : ℕ) = p then 0 else (i : ℕ) := fun i => by
    simp only [F]; split_ifs <;> rfl
  have hG : ∀ j, (G j : ℕ) = if (j : ℕ) = 0 then p else if (j : ℕ) ≤ p then (j : ℕ) - 1 else (j : ℕ) := fun j => by
    simp only [G]; split_ifs <;> rfl
  have hGF : ∀ i, G (F i) = i := fun i => by
    apply Fin.ext
    rw [hG, hF]
    split_ifs <;> first | contradiction | omega
  have hFG : ∀ j, F (G j) = j := fun j => by
    apply Fin.ext
    rw [hF, hG]
    split_ifs <;> first | contradiction | omega
  refine ⟨⟨F, G, hGF, hFG⟩, fun i => ?_⟩
  change _ = (Fin.cons x (Fin.append f g) : Fin (p + q + 1) → α) (F i)
  induction i using Fin.addCases with
  | left k =>
    have : F (Fin.castAdd (q + 1) k) = (Fin.castAdd q k).succ := Fin.ext (by simp [F])
    rw [this, Fin.cons_succ, Fin.append_left, Fin.append_left]
  | right l =>
    rw [Fin.append_right]
    induction l using Fin.cases with
    | zero =>
      have : F (Fin.natAdd p 0) = 0 := Fin.ext (by simp [F])
      rw [this, Fin.cons_zero, Fin.cons_zero]
    | succ j =>
      have : F (Fin.natAdd p j.succ) = (Fin.natAdd p j).succ := Fin.ext (by simp [F]; omega)
      rw [this, Fin.cons_succ, Fin.cons_succ, Fin.append_right]

end Enumerate

section Step

theorem star_cell_bary_step : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab φ' w : InvFun O) (i : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X), IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) → (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → ((i + 1 : ℕ) : ℝ) < lab.evalZ β) → (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n) → (∀ (m' : ℕ) (s : Fin m' ↪ Fin b) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j))) → (∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₁ ∈ balForms bar X, (∀ y, 0 ≤ β₁ y y) ∧ w.evalZ β₁ = 1 ∧ InRCone γ β₁) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone (Fin.append v u) β → InRCone (Fin.append v u) β' → β = β') → (∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β) → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) → InRCone (Fin.append v u) β₀ → (∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → IsCell bar φ' (Fin.cons β₀ fun j => Fin.append v u (s j))) → ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X), IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧ (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k)) ∧ Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β → (i : ℝ) < lab.evalZ β) ∧ ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
  classical
  intro O _ bar ψ lab φ' w i X _ _ _ b a v u hv hinj hlab hle hgt hind hnat hface hex huniq hmono β₀ hβ₀ hβ₀n hw hl0 hcone
    hstar m' s h hcut hpos
  set G := Fin.append v u with hGdef
  have hGv : ∀ k, G (Fin.castAdd a k) = v k := fun k => Fin.append_left v u k
  have hGu : ∀ j, G (Fin.natAdd b j) = u j := fun j => Fin.append_right v u j
  have hvG : ∀ k, InRCone G (v k) := fun k => hGv k ▸ inRCone_self G _
  have huG : ∀ j, InRCone G (u j) := fun j => hGu j ▸ inRCone_self G _

  have hv0 : InRCone v β₀ := by
    by_contra hn
    have := hgt β₀ hβ₀ hβ₀n hcone hn
    rw [hl0] at this
    exact lt_irrefl _ this

  obtain ⟨p, eS, heS⟩ := exists_enum_fin (fun k => h (v k) = 0)
  obtain ⟨r, eT, heT⟩ := exists_enum_fin (fun j => h (u j) = 0)
  obtain ⟨s', hs1, hs2⟩ := exists_append_emb eS eT
  set v' : Fin p → LinearMap.BilinForm ℤ X := fun k => v (eS k) with hv'def
  set uT : Fin r → LinearMap.BilinForm ℤ X := fun j => u (eT j) with huTdef
  set u' : Fin (r + 1) → LinearMap.BilinForm ℤ X := Fin.cons β₀ uT with hu'def
  have hvS0 : ∀ k, h (v' k) = 0 := fun k => (heS _).2 ⟨k, rfl⟩
  have huT0 : ∀ j, h (uT j) = 0 := fun j => (heT _).2 ⟨j, rfl⟩
  have hcomp : (fun j => G (s' j)) = Fin.append v' uT := funext fun j => by
    induction j using Fin.addCases with
    | left k => simp only [hs1, hGv, Fin.append_left, hv'def]
    | right l => simp only [hs2, hGu, Fin.append_right, huTdef]
  have hz : ∀ x, h (Fin.append v' uT x) = 0 := fun x => by
    induction x using Fin.addCases with
    | left k => rw [Fin.append_left]; exact hvS0 k
    | right l => rw [Fin.append_right]; exact huT0 l
  have hcut' : IsFaceCut G s' h := by
    refine ⟨hcut.1, fun j => ⟨fun h0 => ?_, ?_⟩⟩
    · induction j using Fin.addCases with
      | left k =>
        rw [hGv] at h0
        obtain ⟨k', rfl⟩ := (heS k).1 h0
        exact ⟨_, hs1 k'⟩
      | right l =>
        rw [hGu] at h0
        obtain ⟨l', rfl⟩ := (heT l).1 h0
        exact ⟨_, hs2 l'⟩
    · rintro ⟨x, rfl⟩
      rw [show G (s' x) = Fin.append v' uT x from congrFun hcomp x]
      exact hz x

  have hc1 := hstar (p + r) s' h hcut' hpos
  rw [hcomp] at hc1
  obtain ⟨e, he⟩ := exists_perm_append_cons β₀ v' uT
  have hcell : IsCell bar φ' (Fin.append v' u') := by
    have := hc1.reindex e
    convert this using 1
    funext x
    exact he x

  have hcellv : IsCell bar ψ v' := hface p eS h ⟨fun k => by
    have := hcut.1 (Fin.castAdd a k); rwa [hGv] at this, fun k => (heS k)⟩

  have hm0 : InRCone (Fin.append v' u') β₀ := by
    have := inRCone_self (Fin.append v' u') (Fin.natAdd p 0)
    rwa [Fin.append_right, hu'def, Fin.cons_zero] at this
  have hmv : ∀ k, InRCone (Fin.append v' u') (v' k) := fun k => by
    have := inRCone_self (Fin.append v' u') (Fin.castAdd (r + 1) k)
    rwa [Fin.append_left] at this
  have hmu : ∀ j, InRCone (Fin.append v' u') (uT j) := fun j => by
    have := inRCone_self (Fin.append v' u') (Fin.natAdd p j.succ)
    rwa [Fin.append_right, hu'def, Fin.cons_succ] at this

  have hG' : ∀ x, InRCone G (Fin.append v' u' x) := fun x => by
    induction x using Fin.addCases with
    | left k => rw [Fin.append_left]; exact hvG _
    | right l =>
      rw [Fin.append_right]
      induction l using Fin.cases with
      | zero => rw [hu'def, Fin.cons_zero]; exact hcone
      | succ j => rw [hu'def, Fin.cons_succ]; exact huG _
  have hv'v : ∀ k, InRCone v (v' k) := fun k => inRCone_self v _
  refine ⟨p, r + 1, v', u', hcell, hcellv, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro k
    induction k using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hm0
    | succ j =>
      rw [Fin.cons_succ]
      have h0 : h (G (s j)) = 0 := (hcut.2 _).2 ⟨j, rfl⟩
      generalize s j = x at h0 ⊢
      induction x using Fin.addCases with
      | left k =>
        rw [hGv] at h0 ⊢
        obtain ⟨k', rfl⟩ := (heS k).1 h0
        exact hmv k'
      | right l =>
        rw [hGu] at h0 ⊢
        obtain ⟨l', rfl⟩ := (heT l).1 h0
        exact hmu l'

  · have hl0' : lab.evalZ (u' 0) = ((i + 1 : ℕ) : ℝ) := by rw [hu'def, Fin.cons_zero]; exact hl0
    have hls : ∀ j, lab.evalZ (u' j.succ) = lab.evalZ (u (eT j)) := fun j => by rw [hu'def, Fin.cons_succ]
    intro x y hxy
    simp only at hxy
    induction x using Fin.cases with
    | zero =>
      induction y using Fin.cases with
      | zero => rfl
      | succ j' =>
        rw [hl0', hls] at hxy
        exact absurd hxy (ne_of_lt (hlab _))
    | succ j =>
      induction y using Fin.cases with
      | zero =>
        rw [hl0', hls] at hxy
        exact absurd hxy.symm (ne_of_lt (hlab _))
      | succ j' =>
        rw [hls, hls] at hxy
        rw [eT.injective (hinj hxy)]

  · intro j
    induction j using Fin.cases with
    | zero => rw [hu'def, Fin.cons_zero, hl0]; push_cast; linarith
    | succ j =>
      rw [hu'def, Fin.cons_succ]
      have := hlab (eT j)
      push_cast at this
      linarith

  · intro β hβ hβn hin
    have hinv : InRCone v β := inRCone_trans hv'v hin
    have h1 := hle β hβ hβn hinv
    obtain ⟨n, hn⟩ := hnat β hβ hβn
    rw [hn] at h1 ⊢
    have h2 : n ≤ i + 1 := by exact_mod_cast h1
    rcases Nat.lt_or_ge n (i + 1) with h3 | h3
    · exact_mod_cast Nat.lt_succ_iff.1 h3
    · exfalso
      have h4 : n = i + 1 := le_antisymm h2 h3
      obtain ⟨β₁, hβ₁, hβ₁n, hw₁, hc₁⟩ := hex p v' hcellv β hβ hβn hin (by rw [hn, h4])
      have hβ₁G : InRCone G β₁ := inRCone_trans (fun k => inRCone_trans (fun k' => hvG k') (hv'v k)) hc₁
      have := huniq β₁ hβ₁ hβ₁n β₀ hβ₀ hβ₀n hw₁ hw hβ₁G hcone
      subst this
      obtain ⟨c, hc, ec⟩ := hc₁
      have h5 := apply_eq_of_toReal_eq ec h
      simp only [hvS0, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h5
      have : (0 : ℝ) < h β₁ := by exact_mod_cast hpos
      linarith

  · intro β hβ hβn hin hnot
    have hinG : InRCone G β := inRCone_trans hG' hin
    by_cases hbv : InRCone v β
    · obtain ⟨c, hc, ec⟩ := hin
      rw [Fin.sum_univ_add] at ec
      simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_succ, hu'def, Fin.cons_zero, Fin.cons_succ] at ec
      set c₀ := c (Fin.natAdd p 0)
      set cv : Fin p → ℝ := fun k => c (Fin.castAdd (r + 1) k) with hcv
      set d : Fin r → ℝ := fun j => c (Fin.natAdd p j.succ) with hd
      obtain ⟨ee, -, e1⟩ := id hbv
      obtain ⟨f, -, e2⟩ := id hv0
      obtain ⟨rd, -, -, hrd⟩ := exists_extend_coeff eT d
      obtain ⟨rc, hrc1, hrc2, hrc⟩ := exists_extend_coeff eS cv
      have hrel : ∑ j, rd j • toReal (u j) = ∑ k, (ee k - c₀ * f k - rc k) • toReal (v k) := by
        simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum]
        rw [hrd, hrc, ← e1, ← e2, ec]
        abel
      have hd0 : rd = 0 := eq_zero_of_toReal_rel hind hrel
      have hdz : ∑ j, d j • toReal (uT j) = 0 := by
        have := hrd (fun j => toReal (u j))
        simp only [hd0, Pi.zero_apply, zero_smul, Finset.sum_const_zero] at this
        exact this.symm
      have e' : toReal β = c₀ • toReal β₀ + ∑ k, rc k • toReal (v k) := by
        rw [hrc, ec, hdz, add_zero, add_comm]
      rcases (hc (Fin.natAdd p 0)).eq_or_lt with h0 | h0
      · exfalso
        apply hnot
        refine ⟨cv, fun k => hc _, ?_⟩
        have h0' : c₀ = 0 := h0.symm
        rw [ec, hdz, h0', zero_smul, add_zero, add_zero]
      · have hrcn : ∀ k, 0 ≤ rc k := fun k => by
          by_cases hk : k ∈ Set.range eS
          · obtain ⟨k', rfl⟩ := hk; rw [hrc1]; exact hc _
          · rw [hrc2 k hk]
        have := hmono β₀ hβ₀ hβ₀n β hβ hβn hv0 c₀ rc h0 hrcn e'
        rw [hl0] at this
        push_cast at this ⊢
        linarith
    · have := hgt β hβ hβn hinG hbv
      push_cast at this ⊢
      linarith

  · intro d c hrel
    rw [Fin.sum_univ_succ] at hrel
    simp only [hu'def, Fin.cons_zero, Fin.cons_succ] at hrel
    have h1 := congrArg h hrel
    simp only [map_add, map_sum, map_zsmul, hvS0, huT0, smul_zero, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero] at h1
    have hc0 : c 0 = 0 := (mul_eq_zero.1 h1).resolve_right hpos.ne'
    rw [hc0, zero_smul, zero_add] at hrel
    obtain ⟨rc, hrc1, -, hrc⟩ := exists_extend_coeff eT (fun j => c j.succ)
    obtain ⟨rd, -, -, hrd⟩ := exists_extend_coeff eS d
    have hz := hind rd rc (by rw [hrc, hrd]; exact hrel)
    funext x
    induction x using Fin.cases with
    | zero => exact hc0
    | succ j =>
      have := hrc1 j
      rw [hz] at this
      exact this.symm

end Step

end GlobalTheory.PolFan
