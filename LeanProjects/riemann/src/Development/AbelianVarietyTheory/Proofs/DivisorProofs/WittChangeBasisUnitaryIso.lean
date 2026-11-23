import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkChart

theorem exists_conj {Γ : Type} [Group Γ] (H K : Subgroup Γ) (t : Γ) (h : ∀ g, g ∈ H ↔ t⁻¹ * g * t ∈ K) :
    ∃ κ : H ≃* K, ∀ g, (κ g).1 = t⁻¹ * g.1 * t :=
  ⟨{ toFun := fun g => ⟨t⁻¹ * g.1 * t, (h _).1 g.2⟩
     invFun := fun k => ⟨t * k.1 * t⁻¹, (h _).2 (by simpa [mul_assoc] using k.2)⟩
     left_inv := fun g => Subtype.ext (by simp [mul_assoc])
     right_inv := fun g => Subtype.ext (by simp [mul_assoc])
     map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl⟩

theorem gram_iff {R : Type} [CommRing R] {k : ℕ} (g g' S S' C C' J : Matrix (Fin k) (Fin k) R)
    (h1 : S * S' = 1) (h2 : C * C' = 1) :
    gᵀ * J * g' = J ↔ (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * J * C := by
  have h3 : S'ᵀ * Sᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have e : (S' * g * S)ᵀ * (Sᵀ * J * C) * (C' * g' * C) = Sᵀ * (gᵀ * J * g') * C := by
    calc _ = Sᵀ * (gᵀ * (S'ᵀ * Sᵀ) * J * (C * C') * g') * C := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.mul_one]
  rw [e]
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  have f : ∀ X : Matrix (Fin k) (Fin k) R, S'ᵀ * (Sᵀ * X * C) * C' = X := fun X => by
    calc _ = (S'ᵀ * Sᵀ) * X * (C * C') := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, h3, Matrix.mul_one, Matrix.one_mul]
  rw [← f (gᵀ * J * g'), h, f]

theorem conj_iff {D : D7} {k : ℕ} (x W : Mx D k k) (hW : cj W = W) :
    xᵀ * W * cj x = W ↔ adj x * W * x = W := by
  constructor
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, cj_cj, hW, cj_transpose, ← adj_eq] at this
  · intro h
    have := congrArg cj h
    rwa [cj_mul, cj_mul, hW, adj_eq, cj_transpose, cj_cj] at this

theorem cj_Jst (D : D7) (n : ℕ) :
    cj (rat (StdUnn.Jst D n) : Mx D (n + n) (n + n)) = rat (StdUnn.Jst D n) := by
  rw [rat_Jst, cj, block_matrix_map]
  change StdUnn.blk4 (cj 0) (cj 1) (cj (-1)) (cj 0) = _
  rw [cj_neg, cj_zero, cj_one]

theorem mem_UG_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ (g.1 : Mx D k k)ᵀ * rat J * cj g.1 = rat J := by
  rw [← map_cAl, ← incM_eq]
  exact Iff.rfl

theorem mem_HR_iff {D : D7} {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (g : GL (Fin k) (AE D)) :
    g ∈ HR (AF D.host.F) D.sp.cm.sig J ↔ adj (g.1 : Mx D k k) * rat J * g.1 = rat J := Iff.rfl

theorem mat_iff {D : D7} {k : ℕ} (g S S' J W : Mx D k k) (h1 : S * S' = 1) (hG : Sᵀ * J * cj S = W) (hW : cj W = W) :
    gᵀ * J * cj g = J ↔ adj (S' * g * S) * W * (S' * g * S) = W := by
  have hc : cj S * cj S' = 1 := by rw [← cj_mul, h1, cj_one]
  rw [← conj_iff _ _ hW, cj_mul, cj_mul, ← hG]
  exact gram_iff g (cj g) S S' (cj S) (cj S') J h1 hc

theorem mem_iff {D : D7} {k : ℕ} (J W : Matrix (Fin k) (Fin k) D.host.E) (t : GL (Fin k) (AE D))
    (hG : (t.1 : Mx D k k)ᵀ * rat J * cj t.1 = rat W) (hW : cj (rat W : Mx D k k) = rat W) (g : GL (Fin k) (AE D)) :
    g ∈ UG (cAl D) (incM D.host.F J) ↔ t⁻¹ * g * t ∈ HR (AF D.host.F) D.sp.cm.sig W := by
  rw [mem_UG_iff, mem_HR_iff, Units.val_mul, Units.val_mul]
  exact mat_iff g.1 t.1 (t⁻¹).1 _ _ t.mul_inv hG hW

theorem exists_isChartW : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E), T.1ᵀ * J₂ * T.1.map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n → ∃ κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n, IsChartW T κ := by
  intro D n J₂ T hG
  have hW : (rat T.1 : Mx D (n + n) (n + n))ᵀ * rat J₂ * cj (rat T.1) = rat (StdUnn.Jst D n) := by
    rw [← hG, rat_mul, rat_mul, cj_rat]; rfl
  obtain ⟨κ, hκ⟩ := exists_conj _ _ _
    (mem_iff J₂ (StdUnn.Jst D n) ⟨rat T.1, rat (T⁻¹).1, rat_mul_inv T, rat_inv_mul T⟩ hW (cj_Jst D n))
  refine ⟨κ, fun g => ?_⟩
  exact congrArg Units.val (hκ g)

end GlobalTheory.SWLinkChart

end
