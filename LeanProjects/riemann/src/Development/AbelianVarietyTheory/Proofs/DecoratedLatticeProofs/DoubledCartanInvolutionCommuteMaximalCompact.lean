import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan

noncomputable section

namespace GlobalTheory.Core.Rk.IP.Cartan

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

section Complex

variable {n : ℕ} {G s b c : Matrix (Fin n) (Fin n) ℂ}

theorem herm_of_isCartanInv (hs : IsCartanInv G s) : Gᴴ = G := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h4 : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul]; exact h3.1
  have h5 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← mul_assoc, h5, one_mul]
    _ = G := by rw [h4, ← mul_assoc, h2]

theorem frame_gram_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : bᴴ * G * b = c * s * b := by
  calc bᴴ * G * b = bᴴ * (G * (s * (b * c) * s)) * b := by rw [hbc, mul_one, hs, mul_one]
    _ = (bᴴ * (G * s) * b) * (c * s * b) := by simp only [mul_assoc]
    _ = _ := by rw [h, one_mul]

theorem frame_gram_sq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) :
    (bᴴ * G * b) * (bᴴ * G * b) = 1 := by
  rw [frame_gram_eq hbc hs h]
  calc c * s * b * (c * s * b) = c * (s * (b * c) * s) * b := by simp only [mul_assoc]
    _ = 1 := by rw [hbc, mul_one, hs, mul_one, mul_eq_one_comm.1 hbc]

theorem frame_inv_eq (hbc : b * c = 1) (hs : s * s = 1) (h : bᴴ * (G * s) * b = 1) : b * bᴴ * G = s := by
  rw [mul_conjTranspose_mul_eq hbc (frame_gram_eq hbc hs h)]
  calc b * (c * s * b) * c = (b * c) * s * (b * c) := by simp only [mul_assoc]
    _ = s := by rw [hbc, one_mul, mul_one]

theorem blkMat_conjTranspose (x y : Matrix (Fin n) (Fin n) ℂ) :
    (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := by
  simp [blkMat, Matrix.fromBlocks_conjTranspose]

end Complex

variable {D : D7} {θ : InfFam D}

theorem compAt_blkGL (τ : D.what₂.Tau) {n : ℕ} (a : GL (Fin n) (AE D)) :
    compAt θ τ (blkGL finSumFinEquiv (a, a)).1 = blkMat finSumFinEquiv (compAt θ τ a.1) (compAt θ τ a.1) :=
  blkMat_map finSumFinEquiv ((θ τ).comp (infPart D)) (map_zero _) _ _

theorem commute_of_mem_Kmax (hθ : IsInfFam θ) {V : HSp D} {a : GL (Fin V.rank) (AE D)} (τ : D.what₂.Tau)
    (hd : ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) * ((compAt θ τ a.1)ᴴ * gramAt D V τ * compAt θ τ a.1) = 1)
    {g : GA D V} (hg : g ∈ Kmax V a) :
    Commute (Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g) (frameInv θ V a τ) := by
  refine (unitary_iff_commute (compAt_mul_inv τ a) rfl hd (infMat_isometry hθ τ g)).1 ?_
  rw [compAt_eq_map hθ, compAt_eq_map hθ, eq_infProj hθ (embOverOf D τ) rfl]
  exact (mem_stabArch_iff_unitary (isCMExt_host D) (embOverOf D τ) V.gram a g).1
    (((mem_levelAll (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V) (a := a) (g := g)).1 hg).2 _)

theorem cartan_dbl : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  intro D θ A sA a hθ hs ha
  have hbc := fun τ => compAt_mul_inv (θ := θ) τ a
  have e : ∀ τ, frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ = blkMat finSumFinEquiv (sA τ) (-sA τ) := fun τ => by
    rw [frameInv_dblSp, show frameInv θ A a τ = sA τ from frame_inv_eq (hbc τ) (hs τ).1 (ha τ)]
  have hd : ∀ τ, (compAt θ τ (blkGL finSumFinEquiv (a, a)).1)ᴴ * blkMat finSumFinEquiv (gramAt D A τ) (-gramAt D A τ) *
      compAt θ τ (blkGL finSumFinEquiv (a, a)).1 =
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) := fun τ => by
    rw [compAt_blkGL, blkMat_conjTranspose, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  have hd2 : ∀ τ, blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) *
      blkMat finSumFinEquiv ((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)
        (-((compAt θ τ a.1)ᴴ * gramAt D A τ * compAt θ τ a.1)) = 1 := fun τ => by
    rw [blkMat_mul, neg_mul_neg, frame_gram_sq (hbc τ) (hs τ).1 (ha τ), blkMat_one]
  refine ⟨fun τ => ?_, fun k hk τ => ?_⟩
  · have h := isCartanInv_of_frame (compAt_mul_inv (θ := θ) τ (blkGL finSumFinEquiv (a, a))) (hd τ) (hd2 τ) (by
      rw [blkMat_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, herm_of_isCartanInv (hs τ), ← mul_assoc])
    rw [← gramAt_dblSp] at h
    have h' : IsCartanInv (gramAt D (dblSp A) τ) (frameInv θ (dblSp A) (blkGL finSumFinEquiv (a, a)) τ) := h
    rw [e] at h'
    exact h'
  · rw [Khat_eq] at hk
    have h := commute_of_mem_Kmax hθ (V := dblSp A) (a := blkGL finSumFinEquiv (a, a)) τ (by
      rw [gramAt_dblSp]
      exact (congrArg₂ (· * ·) (hd τ) (hd τ)).trans (hd2 τ)) hk
    rw [e] at h
    exact h

end GlobalTheory.Core.Rk.IP.Cartan

end
