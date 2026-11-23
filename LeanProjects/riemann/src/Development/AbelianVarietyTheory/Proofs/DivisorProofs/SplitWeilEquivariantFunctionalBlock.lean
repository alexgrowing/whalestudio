import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt

noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.DetEqv.BlockForm

theorem blockIndex_zero (x m : ℕ) (j : Fin x) : GlobalTheory.ThK.MidJac.e2 x m ⟨0, j⟩ = Fin.castAdd m j := by
  ext; simp [GlobalTheory.ThK.MidJac.e2, finSigmaFinEquiv_apply]

theorem blockIndex_one (x m : ℕ) (j : Fin m) : GlobalTheory.ThK.MidJac.e2 x m ⟨1, j⟩ = Fin.natAdd x j := by
  ext; simp [GlobalTheory.ThK.MidJac.e2, finSigmaFinEquiv_apply]

variable {k : Type} [Field k] [TopologicalSpace k]

def splitCols (n x m : ℕ) : Matrix (Fin n) (Fin (x + m)) k ≃ₜ Matrix (Fin n) (Fin x) k × Matrix (Fin n) (Fin m) k where
  toFun X := (fun i j => X i (Fin.castAdd m j), fun i j => X i (Fin.natAdd x j))
  invFun p := fun i c => Fin.append (p.1 i) (p.2 i) c
  left_inv X := by
    funext i c
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c <;> simp
  right_inv p := by
    ext i j <;> simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_ <;>
      exact continuous_pi fun i => continuous_pi fun j => (continuous_apply _).comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun c => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · simp only [Fin.append_left]
      exact (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
    · simp only [Fin.append_right]
      exact (continuous_apply j).comp ((continuous_apply i).comp continuous_snd)

omit [TopologicalSpace k] in
theorem mul_apply_castAdd {n x m : ℕ} (X : Matrix (Fin n) (Fin (x + m)) k) (M : Matrix (Fin (x + m)) (Fin (x + m)) k)
    (i : Fin n) (j : Fin x) (h1 : ∀ l : Fin m, M (Fin.natAdd x l) (Fin.castAdd m j) = 0)
    (h0 : ∀ l : Fin x, M (Fin.castAdd m l) (Fin.castAdd m j) = (1 : Matrix (Fin x) (Fin x) k) l j) :
    (X * M) i (Fin.castAdd m j) = X i (Fin.castAdd m j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [h0, h1, Matrix.one_apply]

omit [TopologicalSpace k] in
theorem mul_apply_natAdd {n x m : ℕ} (X : Matrix (Fin n) (Fin (x + m)) k) (M : Matrix (Fin (x + m)) (Fin (x + m)) k)
    (g : Matrix (Fin m) (Fin m) k) (i : Fin n) (j : Fin m)
    (h0 : ∀ l : Fin x, M (Fin.castAdd m l) (Fin.natAdd x j) = 0)
    (h1 : ∀ l : Fin m, M (Fin.natAdd x l) (Fin.natAdd x j) = g l j) :
    (X * M) i (Fin.natAdd x j) = ∑ l : Fin m, X i (Fin.natAdd x l) * g l j := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [h0, h1]

omit [TopologicalSpace k] in
theorem mul_leviEmb_castAdd (n x m : ℕ) (X : Matrix (Fin n) (Fin (x + m)) k) (g : GL (Fin (![x, m] 1)) k)
    (i : Fin n) (j : Fin x) :
    (X * ((leviEmb k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g) : GL (Fin (x + m)) k) :
      Matrix (Fin (x + m)) (Fin (x + m)) k)) i (Fin.castAdd m j) = X i (Fin.castAdd m j) := by
  refine mul_apply_castAdd X _ i j (fun l => ?_) (fun l => ?_)
  · have h := leviEmb_apply_ne k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g)
      (by decide : (1 : Fin 2) ≠ 0) l j
    exact (congrArg₂ _ (blockIndex_one x m l).symm (blockIndex_zero x m j).symm).trans h
  · have h := leviEmb_apply_same k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g) 0 l j
    rw [Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h
    exact (congrArg₂ _ (blockIndex_zero x m l).symm (blockIndex_zero x m j).symm).trans h

omit [TopologicalSpace k] in
theorem mul_leviEmb_natAdd (n x m : ℕ) (X : Matrix (Fin n) (Fin (x + m)) k) (g : GL (Fin (![x, m] 1)) k)
    (i : Fin n) (j : Fin m) :
    (X * ((leviEmb k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g) :
      GL (Fin (x + m)) k) : Matrix (Fin (x + m)) (Fin (x + m)) k)) i (Fin.natAdd x j) =
      ∑ l : Fin m, X i (Fin.natAdd x l) * g.val l j := by
  refine mul_apply_natAdd X _ g.val i j (fun l => ?_) (fun l => ?_)
  · have h := leviEmb_apply_ne k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g)
      (by decide : (0 : Fin 2) ≠ 1) l j
    exact (congrArg₂ _ (blockIndex_zero x m l).symm (blockIndex_one x m j).symm).trans h
  · have h := leviEmb_apply_same k (GlobalTheory.ThK.MidJac.e2 x m) (Pi.mulSingle (1 : Fin 2) g) 1 l j
    rw [Pi.mulSingle_eq_same] at h
    exact (congrArg₂ _ (blockIndex_one x m l).symm (blockIndex_one x m j).symm).trans h

def pullSB {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) :
    GlobalTheory.SplitWeil.SB B →ₗ[ℂ] GlobalTheory.SplitWeil.SB A where
  toFun F := ⟨(F : B → ℂ) ∘ e, F.2.1.comp_continuous e.continuous, F.2.2.comp_homeomorph e⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullSB_apply {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B)
    (F : GlobalTheory.SplitWeil.SB B) (a : A) : (pullSB e F : A → ℂ) a = (F : B → ℂ) (e a) := rfl

theorem eq_zero_of_vanishAt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x m n : ℕ), GlobalTheory.DetEqv.VanishAt k n → n < m → ∀ μ : kˣ →* ℂˣ, (∀ t : ℝ, μ ≠ GlobalTheory.SmGL.absPow k (t : ℂ)) →
    ∀ L : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + m)) k) →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (![x, m] 1)) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin (x + m)) k)),
        (∀ X : Matrix (Fin n) (Fin (x + m)) k, (Φ' : Matrix (Fin n) (Fin (x + m)) k → ℂ) X =
          (Φ : Matrix (Fin n) (Fin (x + m)) k → ℂ) (X * ((GlobalTheory.SmGL.leviEmb k (GlobalTheory.ThK.MidJac.e2 x m)
            (Pi.mulSingle (1 : Fin 2) g) : GL (Fin (x + m)) k) : Matrix (Fin (x + m)) (Fin (x + m)) k))) →
        L Φ' = (μ (Matrix.GeneralLinearGroup.det g) : ℂ) * L Φ) →
      L = 0 := by
  intro k _ _ _ _ x m n hV hnm μ hμ L hL
  have key : L ∘ₗ pullSB (splitCols (k := k) n x m) = 0 := by
    refine hV (Matrix (Fin n) (Fin x) k) m hnm μ hμ _ fun g Φ Φ' h => ?_
    refine hL (show GL (Fin (![x, m] 1)) k from g) _ _ fun X => ?_
    rw [pullSB_apply, pullSB_apply]
    refine (h _ _).trans (congrArg _ (Prod.ext ?_ ?_))
    · funext i j
      exact (mul_leviEmb_castAdd n x m X _ i j).symm
    · funext i j
      exact (mul_leviEmb_natAdd n x m X g i j).symm
  ext Φ
  have hΦ : Φ = pullSB (splitCols (k := k) n x m) (pullSB (splitCols (k := k) n x m).symm Φ) := by
    ext X
    rw [pullSB_apply, pullSB_apply, Homeomorph.symm_apply_apply]
  rw [hΦ]
  exact LinearMap.congr_fun key _

end GlobalTheory.DetEqv.BlockForm
