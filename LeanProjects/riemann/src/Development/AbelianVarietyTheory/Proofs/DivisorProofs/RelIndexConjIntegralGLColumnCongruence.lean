import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndexCol

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_maximalIdeal_iff (a : 𝒪[k]) :
    a ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (a : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]

theorem val_sum_mul_lt_one (a b : ι → k) (ha : ∀ s, a s ∈ 𝒪[k]) (hb : ∀ s, valuation k (b s) < 1) :
    valuation k (∑ s, a s * b s) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_mul_of_nonneg_right (ha s) zero_le').trans_lt (by rw [one_mul]; exact hb s)

theorem col_inv_mul_iff {x : GL ι k} (hx : x ∈ KO k ι) (y : GL ι k) (t : ι) :
    (∀ s, valuation k (((x⁻¹ * y).val - 1) s t) < 1) ↔ ∀ s, valuation k ((y.val - x.val) s t) < 1 := by
  obtain ⟨hx1, hx2⟩ := (mem_KO_iff x).1 hx
  have e1 : (x⁻¹ * y).val - 1 = (x⁻¹).val * (y.val - x.val) := by
    rw [Units.val_mul, mul_sub, Units.inv_mul]
  have e2 : y.val - x.val = x.val * ((x⁻¹ * y).val - 1) := by
    rw [Units.val_mul, mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
  constructor
  · intro h s
    rw [e2, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx1 s j) h
  · intro h s
    rw [e1, Matrix.mul_apply]
    exact val_sum_mul_lt_one _ _ (fun j => hx2 s j) h

theorem conj_apply (ϖ : kˣ) (t : ι) (z : Matrix ι ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s =
      ((Pi.mulSingle t ϖ : ι → kˣ) r : k) * z r s * ((((Pi.mulSingle t ϖ : ι → kˣ) s)⁻¹ : kˣ) : k) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [hi, diagGL_val, mul_diagonal, diagonal_mul]

theorem conj_integral_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : Matrix ι ι k) (hz : ∀ r s, z r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s ∈ 𝒪[k]) ↔
      ∀ r, r ≠ t → valuation k (z r t) < 1 := by
  have hv : valuation k (ϖ : k) ≠ 0 := by simp
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  simp only [conj_apply]
  constructor
  · intro h r hr
    have h1 := h r t
    simp only [Pi.mulSingle_apply, hr, if_false, if_true, Units.val_one, one_mul] at h1
    have h2 : valuation k (z r t * ((ϖ⁻¹ : kˣ) : k)) ≤ 1 := h1
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h2
    have h3 : valuation k (z r t) ≤ valuation k (ϖ : k) := by
      have := mul_le_mul_of_nonneg_right h2 (zero_le' (a := valuation k (ϖ : k)))
      rwa [mul_assoc, inv_mul_cancel₀ hv, mul_one, one_mul] at this
    exact h3.trans_lt hlt
  · intro h r s
    by_cases hr : r = t <;> by_cases hs : s = t
    · subst hr; subst hs
      simp only [Pi.mulSingle_eq_same]
      rw [mul_comm (ϖ : k), mul_assoc, Units.mul_inv, mul_one]; exact hz _ _
    · subst hr
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hs, if_false, inv_one, Units.val_one, mul_one]
      exact mul_mem hϖ.mem (hz _ _)
    · subst hs
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply, hr, if_false, Units.val_one, one_mul]
      show valuation k _ ≤ 1
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
      have h3 : valuation k (z r s) ≤ valuation k (ϖ : k) := by
        rw [hϖ, le_uniformizer_iff]; exact h r hr
      calc valuation k (z r s) * (valuation k (ϖ : k))⁻¹ ≤ valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 zero_le'
        _ = 1 := mul_inv_cancel₀ hv
    · simp only [Pi.mulSingle_apply, hr, hs, if_false, inv_one, Units.val_one, one_mul, mul_one]
      exact hz _ _

theorem mem_conj_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) {z : GL ι k} (hz : z ∈ KO k ι) :
    z ∈ (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom ↔
      (∀ r, r ≠ t → valuation k (z.val r t) < 1) ∧ ∀ r, r ≠ t → valuation k ((z⁻¹).val r t) < 1 := by
  set g := diagGL (Pi.mulSingle t ϖ : ι → kˣ) with hg
  have e : z ∈ (KO k ι).map (MulAut.conj g⁻¹).toMonoidHom ↔ g * z * g⁻¹ ∈ KO k ι := by
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  obtain ⟨h1, h2⟩ := (mem_KO_iff z).1 hz
  have ev : (g * z * g⁻¹).val = g.val * z.val * (g⁻¹).val := by simp only [Units.val_mul]
  have ei : ((g * z * g⁻¹)⁻¹).val = g.val * (z⁻¹).val * (g⁻¹).val := by
    rw [show (g * z * g⁻¹)⁻¹ = g * z⁻¹ * g⁻¹ by group]; simp only [Units.val_mul]
  rw [e, mem_KO_iff, ev, ei, hg, conj_integral_iff hϖ t _ h1, conj_integral_iff hϖ t _ h2]

theorem relIndex_conj_col : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ r, r ∉ S → x.val r t = (1 : Matrix ι ι k) r t) →
    (∀ y : ι → k, (∀ r, y r ∈ 𝒪[k]) → (∀ r, r ∉ S → y r = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0)) →
    ((KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ))⁻¹)).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S ht H hH hcol hel
  set A := (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom with hA

  have hQ0 : ∀ z ∈ H, (∀ r, r ≠ t → valuation k (z.val r t) < 1) ↔
      ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    constructor
    · intro h s
      by_cases hs : s = t
      · subst hs; rw [Matrix.sub_apply, hcol z hz s ht, sub_self, map_zero]; exact zero_lt_one
      · rw [Matrix.sub_apply, Matrix.one_apply_ne hs, sub_zero]; exact h s hs
    · intro h r hr
      simpa [Matrix.sub_apply, Matrix.one_apply_ne hr] using h r
  have hQ : ∀ z ∈ H, z ∈ A ↔ ∀ s, valuation k ((z.val - 1) s t) < 1 := by
    intro z hz
    have hzi : z⁻¹ ∈ H := H.inv_mem hz
    rw [hA, mem_conj_iff hϖ t (hH hz), hQ0 z hz, hQ0 _ hzi]
    have e := col_inv_mul_iff (hH hz) 1 t
    rw [mul_one] at e
    rw [e]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, fun s => ?_⟩
      have h1 := h s
      rw [Matrix.sub_apply] at h1 ⊢
      rw [← Valuation.map_neg, neg_sub, Units.val_one]; exact h1
  have hres : ∀ x y : 𝒪[k], IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔
      valuation k ((x : k) - y) < 1 := fun x y => by
    have h1 := mem_maximalIdeal_iff (x - y)
    push_cast at h1
    rw [← h1]; exact Ideal.Quotient.eq
  let φ : H → (S → 𝓀[k]) := fun x r =>
    IsLocalRing.residue 𝒪[k] ⟨x.1.val r t, ((mem_KO_iff _).1 (hH x.2)).1 r t⟩
  have hφ : ∀ a b : H, φ a = φ b ↔ a⁻¹ * b ∈ A.subgroupOf H := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hQ _ (H.mul_mem (H.inv_mem a.2) b.2), col_inv_mul_iff (hH a.2), funext_iff]
    simp only [φ, hres]
    constructor
    · intro h s
      by_cases hs : s ∈ S
      · rw [Matrix.sub_apply, ← Valuation.map_neg, neg_sub]; exact h ⟨s, hs⟩
      · rw [Matrix.sub_apply, hcol b b.2 s hs, hcol a a.2 s hs, sub_self, map_zero]; exact zero_lt_one
    · intro h r
      have := h r
      rwa [Matrix.sub_apply, ← Valuation.map_neg, neg_sub] at this
  let f : H ⧸ A.subgroupOf H → (S → 𝓀[k]) :=
    Quotient.lift φ (fun a b hab => (hφ a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Bijective f := by
    constructor
    · intro p q
      induction p using QuotientGroup.induction_on
      induction q using QuotientGroup.induction_on
      intro h
      exact QuotientGroup.eq.2 ((hφ _ _).1 h)
    · intro c
      choose u hu using fun r : S => IsLocalRing.residue_surjective (c r)
      let y : ι → k := fun r => if h : r ∈ S then (u ⟨r, h⟩ : k) else 0
      obtain ⟨x, hxH, hx⟩ := hel y (fun r => by
          by_cases h : r ∈ S
          · simp only [y, h, dif_pos]; exact (u _).2
          · simp only [y, h, dif_neg, not_false_eq_true]; exact zero_mem _)
        (fun r hr => by simp [y, hr])
      refine ⟨QuotientGroup.mk ⟨x, hxH⟩, ?_⟩
      funext r
      have hr : (r : ι) ≠ t := fun h => ht (h ▸ r.2)
      have e : x.val r t = u r := by
        rw [hx]; simp [y, hr, r.2]
      show IsLocalRing.residue 𝒪[k] ⟨x.val r t, _⟩ = c r
      rw [← hu r]; congr 1; exact Subtype.ext e
  rw [Subgroup.relIndex, Subgroup.index, Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun,
    Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
  rfl

end GlobalTheory.IndexCol
