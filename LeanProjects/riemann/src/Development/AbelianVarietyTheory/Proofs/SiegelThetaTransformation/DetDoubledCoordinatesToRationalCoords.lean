import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblDet

noncomputable section

def shuffle {T : Type} {r g : ℕ} (p0 : ℕ) (idx : Fin g ≃ T × Fin r) :
    (Fin g ⊕ Fin g → ℂ) ≃ₗ[ℂ] (T → Fin r → ℂ) × (T → Fin r → ℂ) where
  toFun v := (fun τ a => if (a : ℕ) < p0 then v (Sum.inl (idx.symm (τ, a))) else
      v (Sum.inr (idx.symm (τ, a))),
    fun τ a => if (a : ℕ) < p0 then v (Sum.inr (idx.symm (τ, a))) else
      v (Sum.inl (idx.symm (τ, a))))
  invFun u := Sum.elim
    (fun i => if ((idx i).2 : ℕ) < p0 then u.1 (idx i).1 (idx i).2 else u.2 (idx i).1 (idx i).2)
    (fun i => if ((idx i).2 : ℕ) < p0 then u.2 (idx i).1 (idx i).2 else u.1 (idx i).1 (idx i).2)
  map_add' v w := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]
  map_smul' c v := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]
  left_inv v := by
    funext i
    rcases i with i | i <;> by_cases h : ((idx i).2 : ℕ) < p0 <;> simp [h]
  right_inv u := by
    ext τ a <;> by_cases h : (a : ℕ) < p0 <;> simp [h]

def blocks {T : Type} {r : ℕ} (A A' : T → Matrix (Fin r) (Fin r) ℂ) :
    ((T → Fin r → ℂ) × (T → Fin r → ℂ)) →ₗ[ℂ] ((T → Fin r → ℂ) × (T → Fin r → ℂ)) :=
  LinearMap.prodMap
    (LinearMap.pi fun τ => (Matrix.toLin' (A τ)).comp (LinearMap.proj τ))
    (LinearMap.pi fun τ => (Matrix.toLin' (A' τ)).comp (LinearMap.proj τ))

def coordMap {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) :
    ((X.Ψ → Fin r → ℂ) × (X.Ψ → Fin r → ℂ)) →ₗ[ℂ] (QI E r → ℂ) where
  toFun u p := ∑ τ : X.Ψ,
    (τ.1 (Module.finBasis ℚ E p.2) * ((-(τ.1 X.κ0 / 2)) • (X.Gm.map τ.1 *ᵥ u.1 τ)) p.1 +
      ((τ.1 X.κ0 / 2) • (u.2 τ ᵥ* X.Gm.map τ.1)) p.1 * conj (τ.1 (Module.finBasis ℚ E p.2)))
  map_add' u v := by
    funext p
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, Matrix.add_vecMul,
      ← Finset.sum_add_distrib, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun τ _ => by ring
  map_smul' c u := by
    funext p
    simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul,
      Matrix.smul_vecMul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring

end

end GlobalTheory.SW.DblDet

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
theorem _root_.GlobalTheory.SW.det_dbl_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (g : ℕ) (idx : Fin g ≃ X.Ψ × Fin r) (e : (Fin g ⊕ Fin g) ≃ _root_.GlobalTheory.SW.QI E r), ∃ c : ℂ, ∀ x₁ x₂ : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, ∃ L : Matrix (_root_.GlobalTheory.SW.QI E r) (Fin g ⊕ Fin g) ℂ, (L.submatrix e id).det = c * ∏ τ : X.Ψ, ((_root_.GlobalTheory.SW.aLin X x₁ x₂ τ).det * (_root_.GlobalTheory.SW.aAnti X x₁ x₂ τ).det)⁻¹ ∧ ∀ (n : ℕ) (z₁ w : Fin n → Fin g → ℂ) (k : Fin n), _root_.GlobalTheory.SW.zetaOf X.Ψ (_root_.GlobalTheory.SW.dblz X idx x₁ x₂ z₁ w) (_root_.GlobalTheory.SW.dblz' X idx x₁ x₂ z₁ w) k = L *ᵥ Sum.elim (z₁ k) (w k) := by
  intro E _ _ _ r X g idx e
  set S := _root_.GlobalTheory.SW.DblDet.shuffle X.p0 idx
  refine ⟨LinearMap.det (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ
    (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)), fun x₁ x₂ => ?_⟩
  set B := _root_.GlobalTheory.SW.DblDet.blocks (fun τ => (_root_.GlobalTheory.SW.aAnti X x₁ x₂ τ)⁻¹)
    (fun τ => (_root_.GlobalTheory.SW.aLin X x₁ x₂ τ)⁻¹)
  refine ⟨LinearMap.toMatrix' (_root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
    (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)), ?_, ?_⟩
  · have hsub : (LinearMap.toMatrix' (_root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
        (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _))).submatrix e id =
        LinearMap.toMatrix' (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
          (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) := by
      ext i j
      simp [LinearMap.toMatrix'_apply, LinearMap.funLeft_apply]
    have hsplit : LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ B ∘ₗ
        (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _) =
        (LinearMap.funLeft ℂ ℂ e ∘ₗ _root_.GlobalTheory.SW.DblDet.coordMap X ∘ₗ
          (S : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) ∘ₗ
        ((S.symm : _ →ₗ[ℂ] (Fin g ⊕ Fin g → ℂ)) ∘ₗ B ∘ₗ
          (S.symm.symm : (Fin g ⊕ Fin g → ℂ) →ₗ[ℂ] _)) := by
      refine LinearMap.ext fun v => ?_
      simp
    rw [hsub, LinearMap.det_toMatrix', hsplit, LinearMap.det_comp, LinearMap.det_conj]
    congr 1
    simp only [B, _root_.GlobalTheory.SW.DblDet.blocks, LinearMap.det_prodMap, LinearMap.det_pi,
      LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_inv, mul_comm]
  · intro n z₁ w k
    rw [LinearMap.toMatrix'_mulVec]
    funext p
    simp [_root_.GlobalTheory.SW.zetaOf, _root_.GlobalTheory.SW.dblz,
      _root_.GlobalTheory.SW.dblz', _root_.GlobalTheory.SW.DblDet.coordMap, B, _root_.GlobalTheory.SW.DblDet.blocks, S,
      _root_.GlobalTheory.SW.DblDet.shuffle]
