import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinPl.PutIn.Factor

variable {D : D7}

theorem half_nsmul {m n : ℕ} {e : AE D} {x : Mx D m n} (hx : IsHalf e x) (k : ℕ) : IsHalf e (k • x) := fun i j => by
  have h := hx i j
  simp only [Matrix.smul_apply, nsmul_eq_mul]
  linear_combination (k : AE D) * h

theorem isSBHalf_of_half_eq {S T : HSp D} {b : AE D} {Λ Λ' : AddSubgroup (WO S T)} {Ψ : WO S T → ℂ}
    (hΛ : ∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) (hΨ : IsSBHalf b Λ' Ψ) : IsSBHalf b Λ Ψ := by
  obtain ⟨hsupp, k, hk, hinv, hfin⟩ := hΨ
  refine ⟨hsupp, k, hk, fun u hu hub t => hinv u ((hΛ u hub).2 hu) hub t, fun t ht => ?_⟩
  exact (hΛ _ (half_nsmul (hsupp t ht) k)).1 (hfin t ht)

theorem half_smul_self {m n : ℕ} {b : AE D} {x : Mx D m n} (hx : IsHalf b x) : b • x = x := by
  ext i j; exact hx i j

theorem half_of_idem {m n : ℕ} {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem isSBHalf_tens {S T : HSp D} {a b : AE D} {Λ : AddSubgroup (WO S T)} {Φ Ψ : WO S T → ℂ}
    (hab : a * b = 0) (hb : b * b = b) (hbΛ : ∀ u ∈ Λ, b • u ∈ Λ) (hΦ : IsSBHalf a Λ Φ) (hΨ : IsSBHalf b Λ Ψ) :
    IsSBHalf (a + b) Λ (tens b Φ Ψ) := by
  obtain ⟨sΦ, kΦ, hkΦ, iΦ, fΦ⟩ := hΦ
  obtain ⟨sΨ, kΨ, hkΨ, iΨ, fΨ⟩ := hΨ
  have hne : ∀ t, tens b Φ Ψ t ≠ 0 → Φ (t - b • t) ≠ 0 ∧ Ψ (b • t) ≠ 0 := fun t ht => by
    rw [tens_apply] at ht
    exact ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * kΨ, Nat.mul_pos hkΦ hkΨ, fun u hu hua t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hne t ht
    intro i j
    have h := sΦ _ h1 i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    linear_combination h + (t i j) * hab
  · have hbu : b • u ∈ Λ := hbΛ u hu
    have hsub : u - b • u ∈ Λ := Λ.sub_mem hu hbu
    have hau : IsHalf a (u - b • u) := fun i j => by
      have e1 := hua i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      linear_combination e1 - (u i j) * hab - (u i j) * hb + (u i j) * hb
    have hA : (t + (kΦ * kΨ) • u) - b • (t + (kΦ * kΨ) • u) = (t - b • t) + kΦ • (kΨ • (u - b • u)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    have hB : b • (t + (kΦ * kΨ) • u) = b • t + kΨ • (kΦ • (b • u)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [tens_apply, tens_apply, hA, hB,
      iΦ _ (AddSubgroup.nsmul_mem Λ hsub kΨ) (half_nsmul hau kΨ),
      iΨ _ (AddSubgroup.nsmul_mem Λ hbu kΦ) (half_nsmul (half_of_idem hb u) kΦ)]
  · obtain ⟨h1, h2⟩ := hne t ht
    have hC : (kΦ * kΨ) • t = kΨ • (kΦ • (t - b • t)) + kΦ • (kΨ • (b • t)) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [hC]
    exact Λ.add_mem (AddSubgroup.nsmul_mem Λ (fΦ _ h1) kΨ) (AddSubgroup.nsmul_mem Λ (fΨ _ h2) kΦ)

open GlobalTheory.LocMod.TensorModel in

theorem isPlaceModel_tensR : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a b : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), a * b = 0 → b * b = b → (∀ u ∈ Λ, b • u ∈ Λ) → (∀ t, IsHalf b t → (t ∈ Λ' ↔ t ∈ Λ)) → IsSBHalf a Λ Φ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a + b) Λ 1 f₀ Tm → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b Λ' 1 (Tm (GlobalTheory.FinPl.PutIn.tens b Φ (halfInd b Λ))) (Tm ∘ₗ GlobalTheory.FinPl.PutIn.tensR b Φ) := by
  intro D ψ S T a b Λ Λ' Φ f₀ Tm hab hb hbΛ hΛ hΦ hP
  refine ⟨fun Ψ hΨ x hx => ?_, fun Ψ hΨ y hy => ?_, ?_⟩
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => Ψ (t + x)) = fun t => tens b Φ Ψ (t + x) := by
      funext t
      simp only [tens_apply]
      rw [smul_add, half_smul_self hx, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.trans _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') x (half_sum hab hx)
  · have hΨ' := isSBHalf_of_half_eq hΛ hΨ
    have key : tens b Φ (fun t => ψ (symplO S T t y) * Ψ t) = fun t => ψ (symplO S T t y) * tens b Φ Ψ t := by
      funext t
      simp only [tens_apply]
      by_cases h0 : Φ (t - b • t) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - b • t) y + symplO S T (b • t) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero hab (hΦ.1 _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, tensR_apply]
    rw [key]
    exact hP.modul _ (isSBHalf_tens hab hb hbΛ hΦ hΨ') y (half_sum_cA hab hy)
  · have hind : halfInd b Λ' = halfInd b Λ := by
      funext t
      unfold halfInd
      have hiff : (t ∈ Λ' ∧ IsHalf b t) ↔ (t ∈ Λ ∧ IsHalf b t) :=
        ⟨fun h => ⟨(hΛ t h.2).1 h.1, h.2⟩, fun h => ⟨(hΛ t h.2).2 h.1, h.2⟩⟩
      by_cases h : t ∈ Λ ∧ IsHalf b t
      · rw [if_pos (hiff.2 h), if_pos h]
      · rw [if_neg (mt hiff.1 h), if_neg h]
    rw [one_smul, hind]
    rfl

end GlobalTheory.FinPl.PutIn.Factor
end
