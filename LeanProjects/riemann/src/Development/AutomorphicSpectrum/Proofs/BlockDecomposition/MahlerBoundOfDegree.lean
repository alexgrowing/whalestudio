import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Cutoff

section Img

variable {K : Type} [Field K] {n : ℕ}

def imgEquiv (g : GL (Fin n) K) : (Fin n → K) ≃ₗ[K] (Fin n → K) :=
  LinearEquiv.ofLinear (Matrix.toLin' g.val) (Matrix.toLin' (g⁻¹ : GL (Fin n) K).val)
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem img_eq_map (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g W = W.map ((imgEquiv g : (Fin n → K) ≃ₗ[K] (Fin n → K)) : (Fin n → K) →ₗ[K] (Fin n → K)) := rfl

theorem finrank_img (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    Module.finrank K (img g W) = Module.finrank K W := by
  rw [img_eq_map]
  exact LinearEquiv.finrank_map_eq _ _

theorem img_top (g : GL (Fin n) K) : img g (⊤ : Submodule K (Fin n → K)) = ⊤ := by
  rw [img_eq_map, Submodule.map_top]
  exact LinearEquiv.range _

theorem img_img_inv (g : GL (Fin n) K) (W : Submodule K (Fin n → K)) :
    img g (img (g⁻¹ : GL (Fin n) K) W) = W := by
  unfold img
  rw [← Submodule.map_comp, ← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.toLin'_one, Submodule.map_id]

end Img

theorem mem_cutSet_of_mem (hR : DegRat) {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} {τ : ℝ}
    (g : GL (Fin n) E) {x : GA E n} (hx : x ∈ cutSet E n τ) : ratGL E n g * x ∈ cutSet E n τ := by
  have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
  show (∀ W : Submodule E (Fin n → E), deg (ratGL E n g * x) W ≤ prof n τ (Module.finrank E W)) ∧
    -τ ≤ deg (ratGL E n g * x) ⊤
  refine ⟨fun W => ?_, ?_⟩
  · have h := hR E n x g (img (g⁻¹ : GL (Fin n) E) W)
    rw [img_img_inv] at h
    rw [h, ← finrank_img (g⁻¹ : GL (Fin n) E) W]
    exact hx'.1 _
  · have h := hR E n x g ⊤
    rw [img_top] at h
    rw [h]
    exact hx'.2

theorem mahler_of : DegBdd → DegRat → MahlerC → Mahler := by
  intro hB hR hM E _ _ _ n τ
  refine ⟨?_, ?_, ?_⟩
  · have hset : cutSet E n τ = (⋂ W : Submodule E (Fin n → E), {x : GA E n | deg x W ≤ prof n τ (Module.finrank E W)}) ∩
        {x : GA E n | -τ ≤ deg x ⊤} := by
      ext x
      simp [cutSet]
    rw [hset]
    exact (isClosed_iInter fun W => isClosed_le ((hB E n).2 W) continuous_const).inter
      (isClosed_le continuous_const ((hB E n).2 ⊤))
  · intro g x
    constructor
    · intro h
      have h' := mem_cutSet_of_mem hR (g⁻¹) h
      rwa [map_inv, inv_mul_cancel_left] at h'
    · exact mem_cutSet_of_mem hR g
  · obtain ⟨C, hC, hsub⟩ := hM E n (|τ| * (2 * n + 1) ^ 2)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hx' : (∀ W : Submodule E (Fin n → E), deg x W ≤ prof n τ (Module.finrank E W)) ∧ -τ ≤ deg x ⊤ := hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hτ : τ ≤ |τ| := le_abs_self τ
    have hτ0 : 0 ≤ |τ| := abs_nonneg τ
    apply hsub x
    · intro W hW
      have h1 := hx'.1 W
      rw [hW] at h1
      simp only [prof] at h1
      push_cast at h1
      nlinarith [mul_nonneg hτ0 hn, mul_nonneg (sub_nonneg.2 hτ) hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
    · have h1 := hx'.1 ⊤
      rw [finrank_top, Module.finrank_fin_fun] at h1
      simp only [prof] at h1
      have h2 := hx'.2
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn)]
      · nlinarith [mul_nonneg hτ0 hn, mul_nonneg hτ0 (mul_nonneg hn hn),
          mul_nonneg (sub_nonneg.2 hτ) (mul_nonneg hn (by linarith : (0 : ℝ) ≤ n + 1))]

end GlobalTheory.CompanionTheory.Cutoff

end
