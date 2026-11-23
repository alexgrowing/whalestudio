import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.Proof.TwistSupportPeriodicLevels

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_KO_of_latOf_eq {Y : Type} [Fintype Y] [DecidableEq Y] {g : GL Y k} (h : latOf g = latOf 1) :
    g ∈ KO k Y := by
  have h1 := latOf_le_iff.mp h.le
  have h2 := latOf_le_iff.mp h.ge
  simp only [inv_one, one_mul, mul_one] at h1 h2
  exact mem_KO.mpr ⟨h1, h2⟩

variable {r s s' : Type} [Fintype r] [DecidableEq r]

theorem intM_of_parPhi_ne_zero (δ : kˣ →* ℂˣ) {x : Matrix (r ⊕ s) (r ⊕ s') k} (hx : parPhi δ x ≠ 0) : IntM x := by
  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  rw [← Matrix.fromBlocks_toBlocks x, intM_fromBlocks]
  refine ⟨?_, h12, h21.intM, h22⟩
  rw [← e]
  exact intM_of_mem_KO hg

private theorem parPhi_add_eq_of_maxM {δ : kˣ →* ℂˣ} (hδ : IsTame δ) {x y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) (hx : parPhi δ x ≠ 0) : parPhi δ (x + y) = parPhi δ x := by

  obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).mp hx
  have hyb : MaxM (Matrix.fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ y.toBlocks₂₂) := by
    rwa [Matrix.fromBlocks_toBlocks]
  obtain ⟨hy11, hy12, hy21, hy22⟩ := maxM_fromBlocks.mp hyb
  have a11 : (x + y).toBlocks₁₁ = x.toBlocks₁₁ + y.toBlocks₁₁ := Matrix.ext fun _ _ => rfl
  have a12 : (x + y).toBlocks₁₂ = x.toBlocks₁₂ + y.toBlocks₁₂ := Matrix.ext fun _ _ => rfl
  have a21 : (x + y).toBlocks₂₁ = x.toBlocks₂₁ + y.toBlocks₂₁ := Matrix.ext fun _ _ => rfl
  have a22 : (x + y).toBlocks₂₂ = x.toBlocks₂₂ + y.toBlocks₂₂ := Matrix.ext fun _ _ => rfl
  have hM : MaxM ((x + y).toBlocks₁₁ - g.val) := by
    rw [a11, ← e]
    simpa using hy11
  obtain ⟨u, hu, hgu⟩ := exists_mul_KOne hg hM
  have k21 : MaxM (x + y).toBlocks₂₁ := by rw [a21]; exact h21.add hy21
  have k12 : IntM (x + y).toBlocks₁₂ := by rw [a12]; exact h12.add hy12.intM
  have k22 : IntM (x + y).toBlocks₂₂ := by rw [a22]; exact h22.add hy22.intM
  rw [parPhi_of_mem δ (mul_mem hg (KOne_le_KO hu)) hgu k21 k12 k22, parPhi_of_mem δ hg e h21 h12 h22]
  simp only [map_mul, tame_det_of_mem_KOne hδ hu, mul_one]

open Classical in

theorem parPhi_add {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (x : Matrix (r ⊕ s) (r ⊕ s') k) {y : Matrix (r ⊕ s) (r ⊕ s') k}
    (hy : MaxM y) : parPhi δ (x + y) = parPhi δ x := by
  by_cases hx : parPhi δ x = 0
  · by_contra hne
    have hxy : parPhi δ (x + y) ≠ 0 := fun h0 => hne (h0.trans hx.symm)
    have back := parPhi_add_eq_of_maxM hδ hy.neg hxy
    rw [add_neg_cancel_right] at back
    exact hxy (back.symm.trans hx)
  · exact parPhi_add_eq_of_maxM hδ hy hx

variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']

theorem intM_of_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {x : Matrix Y Y' k} (h : IntM (F.coords F' x)) : IntM x := by
  have hM : IntM ((F.bas⁻¹).val * x * F'.bas.val) := fun a b => by
    have := h (F.ord.symm a) (F'.ord.symm b)
    simp only [LatFrame.coords, Matrix.submatrix_apply, Equiv.apply_symm_apply] at this
    exact this
  have hx : F.bas.val * ((F.bas⁻¹).val * x * F'.bas.val) * (F'.bas⁻¹).val = x := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one]
  rw [← hx]
  exact ((intM_of_mem_KO hF).mul hM).mul (mem_KO.mp hF').2

theorem maxM_coords {F : LatFrame k ι Y} {F' : LatFrame k ι' Y'} (hF : F.bas ∈ KO k Y) (hF' : F'.bas ∈ KO k Y')
    {y : Matrix Y Y' k} (h : MaxM y) : MaxM (F.coords F' y) := by
  have hM : MaxM ((F.bas⁻¹).val * y * F'.bas.val) :=
    ((mem_KO.mp hF).2.mul_maxM h).mul_intM (intM_of_mem_KO hF')
  show MaxM (((F.bas⁻¹).val * y * F'.bas.val).submatrix F.ord F'.ord)
  exact fun i j => hM (F.ord i) (F'.ord j)

theorem coords_add (F : LatFrame k ι Y) (F' : LatFrame k ι' Y') (x y : Matrix Y Y' k) :
    F.coords F' (x + y) = F.coords F' x + F.coords F' y := by
  unfold LatFrame.coords
  rw [Matrix.mul_add, Matrix.add_mul]
  ext i j
  simp

theorem stabLat_le_KO {g : GL Y k} (hg : g ∈ KO k Y) : stabLat g ≤ KO k Y := by
  intro a ha
  have hc := mem_stabLat.mp ha
  have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hg hc) (inv_mem hg)

private theorem transport_parPhi_add_eq_of_maxM [Fintype s] [DecidableEq s] [Fintype s'] [DecidableEq s'] {δ : kˣ →* ℂˣ}
    (hδ : IsTame δ) {F : LatFrame k (r ⊕ s) Y} {F' : LatFrame k (r ⊕ s') Y'} (hF : F.bas ∈ KO k Y)
    (hF' : F'.bas ∈ KO k Y') (x : Matrix Y Y' k) {y : Matrix Y Y' k} (hy : MaxM y) :
    F.transport F' (parPhi δ) (x + y) = F.transport F' (parPhi δ) x := by
  show parPhi δ (F.coords F' (x + y)) = parPhi δ (F.coords F' x)
  rw [coords_add]
  exact parPhi_add hδ _ (maxM_coords hF hF' hy)

end

theorem ofTwist_support_periodic_levels : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z] (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ) (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z), (∀ j c h, latOf (F j c h).bas = latOf 1) → (∀ j c h x, (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x ≠ 0 → IntM x) ∧ (∀ j c h x y, MaxM y → (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h (x + y) = (Chain.ofTwist δ hδ μ₀ F Ftop).Phi j c h x) ∧ ∀ j c h, ((Chain.ofTwist δ hδ μ₀ F Ftop).lev j c h).J ≤ KO k (X j ⊕ Fin c) := by
  intro k _ _ _ _ s r t Z _ _ _ _ _ _ X _ _ δ hδ μ₀ F Ftop hF
  have hK : ∀ j c h, (F j c h).bas ∈ KO k (X j ⊕ Fin c) := fun j c h => mem_KO_of_latOf_eq (hF j c h)
  refine ⟨fun j c h x hx => ?_, fun j c h x y hy => ?_, fun j c h => ?_⟩
  · exact intM_of_coords (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) (intM_of_parPhi_ne_zero δ hx)
  · exact transport_parPhi_add_eq_of_maxM hδ (hK (j + 1) c (by omega)) (hK j (c + 1) (by omega)) x hy
  · exact ((TypeDatum.map_conj (parahoric r (Fin j × t) δ hδ) (F j c h)).2.2).trans (stabLat_le_KO (hK j c h))

end GlobalTheory.Proof.TwistSupportPeriodicLevels
