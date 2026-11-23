import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvAtParabNeZero

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim.IwahoriBruhat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem exists_unipLevel (A : Matrix (Fin n) (Fin n) k) (h1 : ∀ i j, valuation k (A i j) ≤ 1)
    (h2 : ∀ i j, j < i → valuation k (A i j) < 1) (h3 : ∀ i, A i i = 1) :
    ∃ u : unipLevel k n, (incl k n u).val = A := by
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨A i j, h1 i j⟩
  have hres0 : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hBd : ∀ i, B i i = 1 := fun i => Subtype.ext (h3 i)
  have hRtri : ((IsLocalRing.residue 𝒪[k]).mapMatrix B).BlockTriangular id := by
    intro i j hji
    exact (hres0 (B i j)).2 (h2 i j hji)
  have hdet : IsUnit B.det := by
    by_contra hnu
    have h0 : IsLocalRing.residue 𝒪[k] B.det = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hnu
    rw [RingHom.map_det, Matrix.det_of_isUpperTriangular hRtri] at h0
    simp [hBd, RingHom.mapMatrix_apply] at h0
  refine ⟨⟨Matrix.nonsingInvUnit B hdet, ?_⟩, ?_⟩
  · show red k n (Matrix.nonsingInvUnit B hdet) ∈ unipB 𝓀[k] (Fin n)
    rw [GlobalTheory.SmGL.mem_unipB]
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · change IsLocalRing.residue 𝒪[k] (B i j) = 0
      exact (hres0 (B i j)).2 (h2 i j hji)
    · change IsLocalRing.residue 𝒪[k] (B i i) = 1
      rw [hBd, map_one]
  · ext i j
    rfl

theorem exists_ne_zero (g : GL (Fin n) k) (i : Fin n) : ∃ j, g.val i j ≠ 0 := by
  by_contra h
  push Not at h
  exact (Matrix.isUnits_det_units g).ne_zero (Matrix.det_eq_zero_of_row_eq_zero i h)

def Clean (g : Matrix (Fin n) (Fin n) k) (i : Fin n) : Prop :=
  ∃ j, (∀ j', j' ≠ j → g i j' = 0) ∧ ∀ i', i' ≠ i → g i' j = 0

theorem monomial_of_clean (g : GL (Fin n) k) (h : ∀ i, Clean g.val i) :
    ∃ (w : Equiv.Perm (Fin n)) (c : Fin n → kˣ), g = GlobalTheory.Parabolic.permGL k w * diagT k (Fin n) c := by
  choose p hrow hcol using h
  have hp : ∀ i, g.val i (p i) ≠ 0 := by
    intro i hz
    obtain ⟨j, hj⟩ := exists_ne_zero g i
    by_cases hji : j = p i
    · rw [hji] at hj
      exact hj hz
    · exact hj (hrow i j hji)
  have hinj : Function.Injective p := by
    intro i i' hii'
    by_contra hne
    exact hp i' (by rw [← hii']; exact hcol i i' (Ne.symm hne))
  let e : Fin n ≃ Fin n := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have he : ∀ b, p (e.symm b) = b := fun b => e.apply_symm_apply b
  refine ⟨e.symm, fun b => Units.mk0 (g.val (e.symm b) b) (by
    have := hp (e.symm b)
    rwa [he b] at this), ?_⟩
  ext a b
  rw [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, GlobalTheory.Parabolic.permGL_apply]
  by_cases hab : a = e.symm b
  · rw [if_pos hab, one_mul, Units.val_mk0, hab]
  · rw [if_neg hab, zero_mul]
    apply hrow a b
    intro hb
    apply hab
    rw [hb]
    exact (e.symm_apply_apply a).symm

private lemma one_add_col_mul_apply (G : Matrix (Fin n) (Fin n) k) (x : Fin n → k) (i₀ a c : Fin n) :
    ((1 + Matrix.of fun a b => if b = i₀ then x a else 0) * G) a c = G a c + x a * G i₀ c := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single i₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

private lemma mul_one_add_row_apply (H : Matrix (Fin n) (Fin n) k) (y : Fin n → k) (j₀ a c : Fin n) :
    (H * (1 + Matrix.of fun a b => if a = j₀ then y b else 0)) a c = H a c + H a j₀ * y c := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  rw [Finset.sum_eq_single j₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ j₀) h

theorem step (g : GL (Fin n) k) (S : Finset (Fin n)) (hS : ∀ i ∈ S, Clean g.val i) (hne : (Sᶜ).Nonempty) :
    ∃ (u u' : unipLevel k n) (i₀ : Fin n), i₀ ∉ S ∧
      ∀ i ∈ insert i₀ S, Clean (incl k n u * g * incl k n u').val i := by
  classical
  set G : Matrix (Fin n) (Fin n) k := g.val with hG
  set D : Finset (Fin n) := Finset.univ.filter (fun j => ∀ i ∈ S, G i j = 0) with hD
  have memD : ∀ j, j ∈ D ↔ ∀ i ∈ S, G i j = 0 := by
    intro j
    simp only [hD, Finset.mem_filter, Finset.mem_univ, true_and]

  have hout : ∀ i, i ∉ S → ∀ j, j ∉ D → G i j = 0 := by
    intro i hi j hj
    rw [memD] at hj
    push Not at hj
    obtain ⟨i', hi', hne'⟩ := hj
    obtain ⟨c, hrow, hcol⟩ := hS i' hi'
    have hjc : j = c := by
      by_contra hh
      exact hne' (hrow j hh)
    rw [hjc]
    exact hcol i (fun h => hi (h ▸ hi'))
  obtain ⟨i1, hi1⟩ := hne
  rw [Finset.mem_compl] at hi1
  obtain ⟨j1, hj1⟩ := exists_ne_zero g i1
  have hj1D : j1 ∈ D := by
    by_contra hh
    exact hj1 (hout i1 hi1 j1 hh)
  have hT : (Sᶜ ×ˢ D).Nonempty := ⟨(i1, j1), Finset.mem_product.2 ⟨Finset.mem_compl.2 hi1, hj1D⟩⟩

  obtain ⟨q, hqT, hqmax⟩ := (Sᶜ ×ˢ D).exists_max_image (fun q => valuation k (G q.1 q.2)) hT
  set M := valuation k (G q.1 q.2) with hM
  have hmax : ∀ i, i ∉ S → ∀ j ∈ D, valuation k (G i j) ≤ M := fun i hi j hj =>
    hqmax (i, j) (Finset.mem_product.2 ⟨Finset.mem_compl.2 hi, hj⟩)
  have hM0 : M ≠ 0 := by
    intro h0
    have h1 := hmax i1 hi1 j1 hj1D
    rw [h0] at h1
    exact hj1 ((valuation k).zero_iff.1 (le_antisymm h1 zero_le))
  have hMpos : 0 < M := zero_lt_iff.2 hM0
  have hT' : ((Sᶜ ×ˢ D).filter (fun q => valuation k (G q.1 q.2) = M)).Nonempty :=
    ⟨q, Finset.mem_filter.2 ⟨hqT, rfl⟩⟩
  obtain ⟨⟨i₀, j'⟩, hq'T, hq'max⟩ :=
    ((Sᶜ ×ˢ D).filter (fun q => valuation k (G q.1 q.2) = M)).exists_max_image Prod.fst hT'
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at hq'T
  obtain ⟨⟨hi₀, hj'D⟩, hj'M⟩ := hq'T
  have hD' : (D.filter (fun j => valuation k (G i₀ j) = M)).Nonempty :=
    ⟨j', Finset.mem_filter.2 ⟨hj'D, hj'M⟩⟩
  obtain ⟨j₀, hj₀', hj₀min⟩ := (D.filter (fun j => valuation k (G i₀ j) = M)).exists_min_image id hD'
  rw [Finset.mem_filter] at hj₀'
  obtain ⟨hj₀, hpiv⟩ := hj₀'
  have hlow : ∀ i, i ∉ S → i₀ < i → valuation k (G i j₀) < M := by
    intro i hi hlt
    refine lt_of_le_of_ne (hmax i hi j₀ hj₀) (fun heq => ?_)
    have h1 := hq'max (i, j₀)
      (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_compl.2 hi, hj₀⟩, heq⟩)
    exact absurd hlt (not_lt.2 h1)
  have hleft : ∀ j ∈ D, j < j₀ → valuation k (G i₀ j) < M := by
    intro j hj hlt
    refine lt_of_le_of_ne (hmax i₀ hi₀ j hj) (fun heq => ?_)
    have h1 := hj₀min j (Finset.mem_filter.2 ⟨hj, heq⟩)
    exact absurd hlt (not_lt.2 h1)
  have hp0 : G i₀ j₀ ≠ 0 := by
    intro h0
    apply hM0
    rw [← hpiv, h0, Valuation.map_zero]
  have hq1 : ∀ a, valuation k a ≤ M → valuation k (-(a / G i₀ j₀)) ≤ 1 := by
    intro a ha
    rw [Valuation.map_neg, Valuation.map_div, hpiv]
    exact (div_le_one₀ hMpos).2 ha
  have hq2 : ∀ a, valuation k a < M → valuation k (-(a / G i₀ j₀)) < 1 := by
    intro a ha
    rw [Valuation.map_neg, Valuation.map_div, hpiv]
    exact (div_lt_one₀ hMpos).2 ha

  let x : Fin n → k := fun a => if a ∉ S ∧ a ≠ i₀ then -(G a j₀ / G i₀ j₀) else 0
  let y : Fin n → k := fun b => if b ∈ D ∧ b ≠ j₀ then -(G i₀ b / G i₀ j₀) else 0
  let U : Matrix (Fin n) (Fin n) k := 1 + Matrix.of (fun a b => if b = i₀ then x a else 0)
  let U' : Matrix (Fin n) (Fin n) k := 1 + Matrix.of (fun a b => if a = j₀ then y b else 0)
  have hx0 : ∀ a, a ∈ S ∨ a = i₀ → x a = 0 := by
    intro a h
    simp only [x]
    rw [if_neg]
    tauto
  have hy0 : ∀ b, b ∉ D ∨ b = j₀ → y b = 0 := by
    intro b h
    simp only [y]
    rw [if_neg]
    tauto
  have hx1 : ∀ a, valuation k (x a) ≤ 1 := by
    intro a
    by_cases h : a ∉ S ∧ a ≠ i₀
    · simp only [x, if_pos h]
      exact hq1 _ (hmax a h.1 j₀ hj₀)
    · simp only [x, if_neg h, Valuation.map_zero]
      exact zero_le
  have hx2 : ∀ a, i₀ < a → valuation k (x a) < 1 := by
    intro a hlt
    by_cases h : a ∉ S ∧ a ≠ i₀
    · simp only [x, if_pos h]
      exact hq2 _ (hlow a h.1 hlt)
    · simp only [x, if_neg h, Valuation.map_zero]
      exact zero_lt_one
  have hy1 : ∀ b, valuation k (y b) ≤ 1 := by
    intro b
    by_cases h : b ∈ D ∧ b ≠ j₀
    · simp only [y, if_pos h]
      exact hq1 _ (hmax i₀ hi₀ b h.1)
    · simp only [y, if_neg h, Valuation.map_zero]
      exact zero_le
  have hy2 : ∀ b, b < j₀ → valuation k (y b) < 1 := by
    intro b hlt
    by_cases h : b ∈ D ∧ b ≠ j₀
    · simp only [y, if_pos h]
      exact hq2 _ (hleft b h.1 hlt)
    · simp only [y, if_neg h, Valuation.map_zero]
      exact zero_lt_one
  have hU : ∀ a b, U a b = (if a = b then 1 else 0) + (if b = i₀ then x a else 0) := by
    intro a b
    simp only [U, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  have hU' : ∀ a b, U' a b = (if a = b then 1 else 0) + (if a = j₀ then y b else 0) := by
    intro a b
    simp only [U', Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
  have hUd : ∀ a, U a a = 1 := by
    intro a
    rw [hU, if_pos rfl]
    by_cases h : a = i₀
    · rw [if_pos h, hx0 a (Or.inr h), add_zero]
    · rw [if_neg h, add_zero]
  have hU'd : ∀ a, U' a a = 1 := by
    intro a
    rw [hU', if_pos rfl]
    by_cases h : a = j₀
    · rw [if_pos h, hy0 a (Or.inr h), add_zero]
    · rw [if_neg h, add_zero]
  have hU1 : ∀ a b, valuation k (U a b) ≤ 1 := by
    intro a b
    by_cases hab : a = b
    · rw [hab, hUd, Valuation.map_one]
    · rw [hU, if_neg hab, zero_add]
      split_ifs
      · exact hx1 a
      · rw [Valuation.map_zero]
        exact zero_le
  have hU'1 : ∀ a b, valuation k (U' a b) ≤ 1 := by
    intro a b
    by_cases hab : a = b
    · rw [hab, hU'd, Valuation.map_one]
    · rw [hU', if_neg hab, zero_add]
      split_ifs
      · exact hy1 b
      · rw [Valuation.map_zero]
        exact zero_le
  have hU2 : ∀ a b, b < a → valuation k (U a b) < 1 := by
    intro a b hlt
    rw [hU, if_neg hlt.ne', zero_add]
    by_cases hb : b = i₀
    · rw [if_pos hb]
      exact hx2 a (by rw [← hb]; exact hlt)
    · rw [if_neg hb, Valuation.map_zero]
      exact zero_lt_one
  have hU'2 : ∀ a b, b < a → valuation k (U' a b) < 1 := by
    intro a b hlt
    rw [hU', if_neg hlt.ne', zero_add]
    by_cases ha : a = j₀
    · rw [if_pos ha]
      exact hy2 b (by rw [← ha]; exact hlt)
    · rw [if_neg ha, Valuation.map_zero]
      exact zero_lt_one
  obtain ⟨u, hu⟩ := exists_unipLevel U hU1 hU2 hUd
  obtain ⟨u', hu'⟩ := exists_unipLevel U' hU'1 hU'2 hU'd
  refine ⟨u, u', i₀, hi₀, ?_⟩
  have hprod : (incl k n u * g * incl k n u').val = U * G * U' := by
    rw [Units.val_mul, Units.val_mul, hu, hu']
  have hH : ∀ a c, (U * G) a c = G a c + x a * G i₀ c := by
    intro a c
    exact one_add_col_mul_apply G x i₀ a c
  have hF : ∀ a c, (U * G * U') a c = (U * G) a c + (U * G) a j₀ * y c := by
    intro a c
    exact mul_one_add_row_apply (U * G) y j₀ a c
  have hHi₀ : ∀ c, (U * G) i₀ c = G i₀ c := by
    intro c
    rw [hH, hx0 i₀ (Or.inr rfl), zero_mul, add_zero]
  have hHj₀ : ∀ a, a ≠ i₀ → (U * G) a j₀ = 0 := by
    intro a ha
    rw [hH]
    by_cases haS : a ∈ S
    · rw [hx0 a (Or.inl haS), zero_mul, add_zero]
      exact (memD j₀).1 hj₀ a haS
    · simp only [x, if_pos (⟨haS, ha⟩ : a ∉ S ∧ a ≠ i₀)]
      field_simp
      try ring
  intro i hi
  rw [hprod]
  rcases Finset.mem_insert.1 hi with hii | hiS
  · rw [hii]
    refine ⟨j₀, fun c hc => ?_, fun i' hi' => ?_⟩
    · rw [hF, hHi₀, hHi₀]
      by_cases hcD : c ∈ D
      · simp only [y, if_pos (⟨hcD, hc⟩ : c ∈ D ∧ c ≠ j₀)]
        field_simp
        try ring
      · rw [hy0 c (Or.inl hcD), hout i₀ hi₀ c hcD, mul_zero, add_zero]
    · rw [hF, hHj₀ i' hi', zero_mul, add_zero]
  · obtain ⟨c, hrow, hcol⟩ := hS i hiS
    have hii₀ : i ≠ i₀ := fun h => hi₀ (h ▸ hiS)
    have hc0 : G i c ≠ 0 := by
      obtain ⟨j, hj⟩ := exists_ne_zero g i
      by_cases hjc : j = c
      · rw [hjc] at hj
        exact hj
      · exact absurd (hrow j hjc) hj
    have hcD : c ∉ D := fun h => hc0 ((memD c).1 h i hiS)
    refine ⟨c, fun c' hc' => ?_, fun i' hi' => ?_⟩
    · rw [hF, hHj₀ i hii₀, zero_mul, add_zero, hH, hx0 i (Or.inl hiS), zero_mul, add_zero]
      exact hrow c' hc'
    · rw [hF, hy0 c (Or.inl hcD), mul_zero, add_zero, hH, hcol i' hi', hcol i₀ (Ne.symm hii₀),
        mul_zero, add_zero]

theorem aux (m : ℕ) : ∀ (g : GL (Fin n) k) (S : Finset (Fin n)), (∀ i ∈ S, Clean g.val i) → (Sᶜ).card = m →
    ∃ (j j' : unipLevel k n) (w : Equiv.Perm (Fin n)) (c : Fin n → kˣ),
      g = incl k n j * (GlobalTheory.Parabolic.permGL k w * diagT k (Fin n) c) * incl k n j' := by
  induction m with
  | zero =>
    intro g S hS hc
    have hall : ∀ i, Clean g.val i := by
      intro i
      apply hS
      by_contra hi
      have hmem : i ∈ Sᶜ := Finset.mem_compl.2 hi
      rw [Finset.card_eq_zero] at hc
      rw [hc] at hmem
      exact Finset.notMem_empty i hmem
    obtain ⟨w, c, hwc⟩ := monomial_of_clean g hall
    exact ⟨1, 1, w, c, by simp [hwc]⟩
  | succ m ih =>
    intro g S hS hc
    have hne : (Sᶜ).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨u, u', i₀, hi₀, hcl⟩ := step g S hS hne
    have hc' : ((insert i₀ S)ᶜ).card = m := by
      rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.2 hi₀), hc]
      omega
    obtain ⟨j, j', w, c, h⟩ := ih _ _ hcl hc'
    refine ⟨u⁻¹ * j, j' * u'⁻¹, w, c, ?_⟩
    have hg : g = (incl k n u)⁻¹ * (incl k n u * g * incl k n u') * (incl k n u')⁻¹ := by group
    rw [hg, h]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    group

theorem iwahori_bruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (g : GL (Fin n) k), ∃ (j j' : unipLevel k n) (w : Equiv.Perm (Fin n)) (c : Fin n → kˣ),
      g = incl k n j * (GlobalTheory.Parabolic.permGL k w * diagT k (Fin n) c) * incl k n j' := by
  intro k _ _ _ _ n g
  exact aux n g ∅ (by simp) (by simp)

end GlobalTheory.TypeDim.IwahoriBruhat
