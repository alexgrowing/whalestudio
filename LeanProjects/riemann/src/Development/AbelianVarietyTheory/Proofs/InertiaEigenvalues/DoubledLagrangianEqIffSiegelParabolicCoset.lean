import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SWLagSame

open GlobalTheory.RawLift GlobalTheory.SWLagTerms GlobalTheory.Doubling

variable {D : D7}

theorem gram_conjT (W : HSp D) : W.gramᴴ = W.gram :=
  Matrix.ext fun i j => W.herm.eq (W.frame j) (W.frame i)

theorem gram_det_unit (W : HSp D) : IsUnit W.gram.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ v : Fin W.rank → D.host.E, W.gram *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : ∑ j, v j • W.frame j = 0 := by
      apply W.nondeg.2
      intro x
      rw [← W.frame.sum_repr x]
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hi := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at hi
      calc _ = (starRingEnd D.host.E) (W.frame.repr x i) * ∑ j, W.hT (W.frame i) (W.frame j) * v j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = 0 := by rw [hi, mul_zero]
    funext j
    exact Fintype.linearIndependent_iff.1 W.frame.linearIndependent v h0 j
  intro a b hab
  exact sub_eq_zero.1 (key (a - b) (by rw [Matrix.mulVec_sub, hab, sub_self]))

theorem hAdj_eq (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W M = W.gram⁻¹ * Mᴴ * W.gram := rfl

theorem hAdj_mul (W : HSp D) (M N : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    hAdj W (M * N) = hAdj W N * hAdj W M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W.gram W.gram⁻¹, Matrix.mul_nonsing_inv _ (gram_det_unit W), Matrix.one_mul]

theorem hAdj_hAdj (W : HSp D) (M : Matrix (Fin W.rank) (Fin W.rank) D.host.E) : hAdj W (hAdj W M) = M := by
  simp only [hAdj_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjT,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (gram_det_unit W), Matrix.nonsing_inv_mul _ (gram_det_unit W),
    Matrix.mul_one]

def rowD₁ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₁ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₁

def rowD₂ (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  (GlobalTheory.SWLagTerms.blk W g).toBlocks₂₂ - (GlobalTheory.SWLagTerms.blk W g).toBlocks₁₂

theorem frameOf_eq (W : HSp D) (g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    frameOf W g = (hAdj W (rowD₂ W g), hAdj W (rowD₁ W g)) := rfl

theorem blk_mul (W : HSp D) (h g : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    GlobalTheory.SWLagTerms.blk W (h * g) = GlobalTheory.SWLagTerms.blk W h * GlobalTheory.SWLagTerms.blk W g := by
  simp only [GlobalTheory.SWLagTerms.blk, Matrix.submatrix_mul_equiv]

section Blocks

variable {K : Type} [Field K] {r : ℕ}

theorem toBlocks_mul_parts (X Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :
    (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ + X.toBlocks₁₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₁₂ = X.toBlocks₁₁ * Y.toBlocks₁₂ + X.toBlocks₁₂ * Y.toBlocks₂₂ ∧
    (X * Y).toBlocks₂₁ = X.toBlocks₂₁ * Y.toBlocks₁₁ + X.toBlocks₂₂ * Y.toBlocks₂₁ ∧
    (X * Y).toBlocks₂₂ = X.toBlocks₂₁ * Y.toBlocks₁₂ + X.toBlocks₂₂ * Y.toBlocks₂₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.mul_apply,
      Fintype.sum_sum_type]

theorem keeps_iff_common (H G : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (hG : IsUnit G.det) :
    H.toBlocks₂₁ + H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ ↔
      ∃ Q, (H * G).toBlocks₁₁ - (H * G).toBlocks₂₁ = Q * (G.toBlocks₁₁ - G.toBlocks₂₁) ∧
        (H * G).toBlocks₂₂ - (H * G).toBlocks₁₂ = Q * (G.toBlocks₂₂ - G.toBlocks₁₂) := by
  obtain ⟨e11, e12, e21, e22⟩ := toBlocks_mul_parts H G
  rw [e11, e12, e21, e22]
  constructor
  · intro kd
    have h22 : H.toBlocks₂₂ = H.toBlocks₁₁ + H.toBlocks₁₂ - H.toBlocks₂₁ := by rw [← kd]; abel
    refine ⟨H.toBlocks₁₁ - H.toBlocks₂₁, ?_, ?_⟩ <;> rw [h22] <;> noncomm_ring
  · rintro ⟨Q, h1, h2⟩
    set X := H.toBlocks₁₁ - H.toBlocks₂₁ - Q
    set Y := H.toBlocks₂₂ - H.toBlocks₁₂ - Q
    have hm : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 * G = 0 := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
      rw [Matrix.fromBlocks_multiply]
      have a1 : X * G.toBlocks₁₁ + -Y * G.toBlocks₂₁ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h1; rw [← h1]; noncomm_ring
      have a2 : X * G.toBlocks₁₂ + -Y * G.toBlocks₂₂ = 0 := by
        simp only [X, Y]; rw [← sub_eq_zero] at h2; rw [← neg_eq_zero, ← h2]; noncomm_ring
      rw [a1, a2]
      simp
    have h0 : Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0 = 0 := by
      have := Matrix.mul_nonsing_inv_cancel_right G (Matrix.fromBlocks X (-Y) (0 : Matrix (Fin r) (Fin r) K) 0) hG
      rw [hm, Matrix.zero_mul] at this
      exact this.symm
    rw [← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj] at h0
    have hX : X = 0 := h0.1
    have hY : Y = 0 := neg_eq_zero.1 h0.2.1
    have e1 : H.toBlocks₁₁ = H.toBlocks₂₁ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hX)
    have e2 : H.toBlocks₂₂ = H.toBlocks₁₂ + Q := sub_eq_zero.1 (by rw [← sub_sub]; exact hY)
    rw [e1, e2]; abel

end Blocks

theorem lag_eq_iff (W : HSp D) {Y Y' : Lag W}
    {C C' : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (hY : IsLagFrame W Y C) (hY' : IsLagFrame W Y' C') :
    Y = Y' ↔ ∃ B, C'.1 = C.1 * B ∧ C'.2 = C.2 * B := by
  have hcol : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E)
      (B : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (j : Fin W.rank),
      ((fun a => (C.1 * B) a j), (fun a => (C.2 * B) a j)) = ∑ k, B k j • ((fun a => C.1 a k), (fun a => C.2 a k)) := by
    intro C B j
    ext a <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, mul_comm]
  constructor
  · rintro rfl
    have hmem : ∀ j, ((fun a => C'.1 a j), (fun a => C'.2 a j)) ∈
        Submodule.span D.host.E (Set.range fun k => ((fun a => C.1 a k), (fun a => C.2 a k))) := by
      intro j
      rw [IsLagFrame] at hY hY'
      rw [hY, ← hY']
      exact Submodule.subset_span ⟨j, rfl⟩
    choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun D.host.E).1 (hmem j)
    refine ⟨Matrix.of fun k j => c j k, ?_, ?_⟩
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.1 a) (hc j)
      simp [Prod.fst_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
    · refine Matrix.ext fun a j => ?_
      have := congrArg (fun p => p.2 a) (hc j)
      simp [Prod.snd_sum, Finset.sum_apply] at this
      rw [Matrix.mul_apply]; simpa [mul_comm] using this.symm
  · rintro ⟨B, h1, h2⟩
    have hle : Y'.1 ≤ Y.1 := by
      rw [IsLagFrame] at hY hY'
      rw [← hY, ← hY', Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [h1, h2]
      rw [hcol]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq hle (Y'.2.1.trans Y.2.1.symm)).symm

theorem frame_iff (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) :
    (∃ B, (frameOf W g').1 = (frameOf W g).1 * B ∧ (frameOf W g').2 = (frameOf W g).2 * B) ↔
      ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  simp only [frameOf_eq]
  constructor
  · rintro ⟨B, h1, h2⟩
    refine ⟨hAdj W B, ?_, ?_⟩
    · rw [← hAdj_hAdj W (rowD₁ W g'), h2, hAdj_mul, hAdj_hAdj]
    · rw [← hAdj_hAdj W (rowD₂ W g'), h1, hAdj_mul, hAdj_hAdj]
  · rintro ⟨Q, h1, h2⟩
    exact ⟨hAdj W Q, by rw [h2, hAdj_mul], by rw [h1, hAdj_mul]⟩

theorem keeps_iff_rows (W : HSp D) (g g' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E)
    (hg : IsUnit g.det) :
    KeepsDiag finSumFinEquiv (g' * g⁻¹) ↔ ∃ Q, rowD₁ W g' = Q * rowD₁ W g ∧ rowD₂ W g' = Q * rowD₂ W g := by
  have hb : IsUnit (GlobalTheory.SWLagTerms.blk W g).det := by
    rw [GlobalTheory.SWLagTerms.blk, Matrix.det_submatrix_equiv_self]; exact hg
  have := keeps_iff_common (GlobalTheory.SWLagTerms.blk W (g' * g⁻¹)) (GlobalTheory.SWLagTerms.blk W g) hb
  rw [← blk_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hg] at this
  exact this

theorem keeps_map_iff {K A : Type} [CommRing K] [CommRing A] (f : K →+* A) (hf : Function.Injective f) {n ι : Type}
    (e : n ⊕ n ≃ ι) (M : Matrix ι ι K) : KeepsDiag e (M.map f) ↔ KeepsDiag e M := by
  rw [GlobalTheory.Doubling.keepsDiag_iff e, GlobalTheory.Doubling.keepsDiag_iff e]
  simp only [Matrix.map_apply, ← map_add, hf.eq_iff]

theorem sameClass : ∀ (D : D7) (W : HSp D) (γ γ' : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E) (g₀' : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ' = g₀'.map (incA D) → ∀ (Y Y' : Lag W), IsLagFrame W Y (frameOf W g₀) → IsLagFrame W Y' (frameOf W g₀') → (Y = Y' ↔ γ' * γ⁻¹ ∈ GlobalTheory.Doubling.siegel W) := by
  intro D W γ γ' g₀ g₀' hγ hγ' Y Y' hY hY'
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  haveI := hinj.nontrivial
  have hu : IsUnit (g₀.map (incA D)).det := by
    rw [← hγ, ← Matrix.isUnit_iff_isUnit_det]
    exact (matHom (GlobalTheory.Doubling.dblSp W) γ).isUnit
  have hg₀ : IsUnit g₀.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h := hu
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h
    exact not_isUnit_zero h
  have h1 : mt _ γ⁻¹ * mt _ γ = 1 := by
    show (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val * (matHom (GlobalTheory.Doubling.dblSp W) γ).val = 1
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have h2 : (g₀⁻¹).map (incA D) * g₀.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg₀, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hγ] at h1
  have hinv : mt _ γ⁻¹ = (g₀⁻¹).map (incA D) := by
    rw [← Matrix.mul_nonsing_inv_cancel_right _ (mt _ γ⁻¹) hu, h1, ← h2, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  have hmt : mt _ (γ' * γ⁻¹) = (g₀' * g₀⁻¹).map (incA D) := by
    rw [Matrix.map_mul, ← hγ', ← hinv]
    show (matHom (GlobalTheory.Doubling.dblSp W) (γ' * γ⁻¹)).val = (matHom (GlobalTheory.Doubling.dblSp W) γ').val * (matHom (GlobalTheory.Doubling.dblSp W) γ⁻¹).val
    rw [map_mul, Units.val_mul]
  rw [lag_eq_iff W hY hY', frame_iff, ← keeps_iff_rows W g₀ g₀' hg₀, ← keeps_map_iff (incA D) hinj, ← hmt]
  exact GlobalTheory.Doubling.mem_siegelOf.symm

end GlobalTheory.SWLagSame

end
