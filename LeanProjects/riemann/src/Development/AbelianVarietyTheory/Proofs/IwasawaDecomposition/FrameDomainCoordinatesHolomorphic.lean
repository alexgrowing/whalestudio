import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomain
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.SecFrame

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

def frameAt (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) : mat (frameAt X hj κ z) τ =
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) := rfl

theorem frameCo_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (frameAt X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  rw [frameCo, mat_frameAt, nonsing_inv_mul_cancel_left _ _ (det_x0F X _).isUnit, Equiv.apply_symm_apply]

theorem lminor_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin (m + 1)) : lminor Mᵀ i = lminor M i := by
  unfold lminor
  rw [← transpose_submatrix, det_transpose]

theorem frameAt_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    frameAt X hj κ z ∈ X.dom := by
  intro τ
  set Z := z (κ.symm τ) with hZ
  set B : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 Z 0 1 with hB
  set M := (reindex (idx hj) (idx hj)).symm B with hM
  have hRM : reindex (idx hj) (idx hj) M = B := Equiv.apply_symm_apply _ _
  have hdM : M.det = 1 := by
    rw [hM, reindex_symm, det_reindex_self, hB, det_fromBlocks_zero₂₁]; simp
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_frameAt, det_mul, ← hM, hdM, mul_one]; exact det_x0F X τ
  · set Dg : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) with hDg
    have h0 := congrArg transpose (isOrth_x0F X τ)
    rw [gram_eq_mul, diagonal_transpose, hp] at h0
    have hT : (gram τ.1 X.Gm (mat (frameAt X hj κ z) τ))ᵀ = Mᴴ * Dg * M := by
      rw [gram_eq_mul, mat_frameAt, ← hM, hDg, ← h0]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have hR : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
      have : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) =
          (reindex (idx hj) (idx hj) M)ᴴ * reindex (idx hj) (idx hj) Dg * reindex (idx hj) (idx hj) M := by
        simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
      rw [this, hRM, hDg, reindex_sgn hj, Formalism.UG.Jpq, hB, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
        fromBlocks_multiply]
      simp [hQ, sub_eq_neg_add]
    have hZd : (hQ Z).PosDef := hz (κ.symm τ)
    have h2 : (reindex (idx hj) (idx hj) (Mᴴ * Dg * M)).toBlocks₂₂.PosDef := by
      rw [hR, toBlocks_fromBlocks₂₂]; exact hZd
    have hs : (-schur (reindex (idx hj) (idx hj) (Mᴴ * Dg * M))).PosDef := by
      rw [hR, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      have e : -(-1 - -Z * (hQ Z)⁻¹ * -Zᴴ) = (1 : Matrix (Fin j) (Fin j) ℂ) + Z * (hQ Z)⁻¹ * Zᴴ := by
        simp [Matrix.neg_mul, Matrix.mul_neg]; exact add_comm _ _
      rw [e]
      exact PosDef.add_posSemidef PosDef.one (hZd.inv.posSemidef.mul_mul_conjTranspose_same Z)
    have key := signs_of_blocks (isBlockOrderedSumEquiv_trueIndex hj) (Mᴴ * Dg * M) h2 hs i
    rw [dmin, hp, ← lminor_transpose, hT]
    exact key

theorem domPt_frameAt (z : Pt Tau j (r - j)) : domPt X hj κ (frameAt X hj κ z) = z := by
  funext t
  simp only [domPt, frameCo_frameAt, Equiv.symm_apply_apply, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    inv_one, Matrix.mul_one]

theorem co_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    coW X hj (frameAt X hj κ z) τ = 1 ∧ coOm X hj (frameAt X hj κ z) τ = 1 := by
  simp [coW, coOm, frameCo_frameAt, toBlocks_fromBlocks₂₁]

theorem differentiable_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) := by
  have hM : ∀ c, Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact differentiable_const _ | exact differentiable_apply _
  simp only [mat_frameAt, mul_apply]
  exact Differentiable.fun_sum (u := Finset.univ) (A := fun c (v : Tau × Fin j × Fin (r - j) → ℂ) =>
    mat (x0F X) τ a c * ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b)
    fun c _ => (hM c).const_mul _

end GlobalTheory.ShFam.SecFrame

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

theorem exists_holo_frame : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp), ∃ f : Pt D.what₂.Tau j (N - j) → (s.fd k).dom, (∀ z ∈ DomI D.what₂.Tau j (N - j), s.zOf L k (f z) = z ∧ ∀ τ, coW (s.fd k) s.j_le (f z).1 τ = 1 ∧ coOm (s.fd k) s.j_le (f z).1 τ = 1) ∧ ∀ τ a b, DifferentiableOn ℂ (fun v => ReciprocityTheory.ChartRestriction.G.FD.mat (f (unflat v)).1 τ a b) (DomFlat D.what₂.Tau j (N - j)) := by
  intro D A N j S κ s L k
  classical
  let F : Pt D.what₂.Tau j (N - j) → (s.fd k).dom := fun z =>
    if hz : z ∈ DomI D.what₂.Tau j (N - j) then
      ⟨SecFrame.frameAt (s.fd k) s.j_le (s.lab L k) z, SecFrame.frameAt_mem _ _ _ (s.p0_eq k) hz⟩
    else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩
  have hF : ∀ z ∈ DomI D.what₂.Tau j (N - j), (F z).1 = SecFrame.frameAt (s.fd k) s.j_le (s.lab L k) z :=
    fun z hz => by simp only [F, dif_pos hz]
  refine ⟨F, fun z hz => ⟨?_, fun τ => ?_⟩, fun τ a b => ?_⟩
  · show domPt (s.fd k) s.j_le (s.lab L k) (F z).1 = z
    rw [hF z hz]; exact SecFrame.domPt_frameAt _ _ _ z
  · rw [hF z hz]; exact SecFrame.co_frameAt _ _ _ z τ
  · refine (SecFrame.differentiable_frameAt (s.fd k) s.j_le (s.lab L k) τ a b).differentiableOn.congr fun v hv => ?_
    exact congrArg (fun x => ReciprocityTheory.ChartRestriction.G.FD.mat x τ a b) (hF _ hv)

end GlobalTheory.ShFam
