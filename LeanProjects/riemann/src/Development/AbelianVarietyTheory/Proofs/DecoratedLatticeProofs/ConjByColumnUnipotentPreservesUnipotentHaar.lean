import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.CjVol

open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem colE_inv_val_eq_zero (ρ : ℕ) (β : n → k) (t s : n ⊕ Fin c) (h : lev (ρ + 1) t ≠ lev (ρ + 1) s) :
    (colE c (ρ + 1) β)⁻¹.val t s = 0 := by
  rcases t with t | t <;> rcases s with s | s
  · exact absurd rfl h
  · simp only [colE, upU, Units.inv_mk, fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
    rw [if_neg, neg_zero]
    intro hs; apply h; simp [lev, hs]
  · simp [colE, upU]
  · have : t ≠ s := by rintro rfl; exact h rfl
    simp [colE, upU, Matrix.one_apply, this]

theorem colE_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β).val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem colE_inv_uni (ρ : ℕ) (β : n → k) :
    ∀ r s, (Sum.elim (fun _ => 0) (fun _ => 1) : n ⊕ Fin c → ℕ) s ≤ Sum.elim (fun _ => 0) (fun _ => 1) r →
      (colE c (ρ + 1) β)⁻¹.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := by
  rintro (r | r) (s | s) h
  · simp [colE, upU, Matrix.one_apply]
  · simp at h
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem extendAboveDiagonalEntries_mul_blockRespecting (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (hh : ∀ t s, lev p t ≠ lev p s → h t s = 0) (e : Ix n c p → k) :
    ext0 (Up n c p) e * h = ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) := by
  ext r s
  by_cases hrs : lev p r < lev p s
  · rw [matrixExtendByZero_mul (Up n c p) h e ⟨(r, s), hrs⟩]
    simp [ext0, hrs]
  · have : ext0 (Up n c p) ((rm (Up n c p) h).mulVec e) r s = 0 := by
      simp only [ext0, Matrix.of_apply]; rw [dif_neg hrs]
    rw [this, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hts : lev p t = lev p s
    · have : ext0 (Up n c p) e r t = 0 := by
        simp only [ext0, Matrix.of_apply]; rw [dif_neg (show ¬ lev p r < lev p t by rw [hts]; exact hrs)]
      rw [this, zero_mul]
    · rw [hh t s hts, mul_zero]

theorem cjE_mkNel (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (e : Ix n c (ρ + 1) → k) :
    cjE ρ h1 h2 β (mkNel (ρ + 1) e) =
      mkNel (ρ + 1) ((lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val *
        rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).mulVec e) := by
  rw [← mkNel_co (ρ + 1) (cjE ρ h1 h2 β (mkNel (ρ + 1) e))]
  congr 1
  funext a
  have hne : a.1.1 ≠ a.1.2 := fun h => by have := a.2; rw [h] at this; exact lt_irrefl _ this
  rw [← Matrix.mulVec_mulVec, ← mul_matrixExtendSelectedEntriesByZero_apply, ← extendAboveDiagonalEntries_mul_blockRespecting (ρ + 1) _ (colE_inv_val_eq_zero ρ β)]
  simp only [co, cjE_coe, Units.val_mul, val_mkNel, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Units.mul_inv, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.mul_assoc]

theorem det_L (ρ : ℕ) (β : n → k) :
    (lm (Up n c (ρ + 1)) (colE c (ρ + 1) β).val * rm (Up n c (ρ + 1)) (colE c (ρ + 1) β)⁻¹.val).det = 1 := by
  rw [det_mul, det_lm, det_rm]
  rw [Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_uni ρ β) _,
    Finset.prod_eq_one fun s _ => det_block_unitri _ _ (colE_inv_uni ρ β) _, mul_one]

end GlobalTheory.HaarR.CjVol

open GlobalTheory.HaarR.CjVol GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model in
theorem GlobalTheory.HaarR.map_volN_cjE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (ν : Measure k), ν.IsAddHaarMeasure → ∀ β : n → k, (volN ν n c (ρ + 1)).map (cjE ρ h1 h2 β) = volN ν n c (ρ + 1) := by
  intro k _ _ _ _ _ _ n _ _ c ρ h1 h2 ν hν β
  exact map_volN_of_affine ν (ρ + 1) (cjE ρ h1 h2 β) _ (det_L ρ β) 0
    (fun e => by rw [add_zero]; exact cjE_mkNel ρ h1 h2 β e)
