import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MapInv

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Gp_mem (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1)
    (hs : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹) (hxs : ∀ b, xs b ∈ aaLb X b) :
    ∀ b a, Gp D X0 xs b a ∈ aaD D b * aaD D a := by
  have hY := LatA.shape_mul X0⁻¹ (Gq D xs) (inv_up X0 hup hd) (inv_diag X0 hup hd) (LatA.shape_inv X0 hup hd hs)
    (gram_mem X xs hxs)
  intro b a
  unfold Gp
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Matrix.conjTranspose_apply]
  rcases lt_trichotomy e a with h | h | h
  · rw [inv_up X0 hup hd a e h, star_zero, mul_zero]; exact Submodule.zero_mem _
  · subst h; rw [inv_diag X0 hup hd, star_one, mul_one]; exact hY b e
  · have hz : star (X0⁻¹ a e) ∈ aaD D a * (aaD D e)⁻¹ :=
      star_mem_iQ (show X0⁻¹ a e ∈ iQ D a e from LatA.shape_inv X0 hup hd hs a e h)
    have hYe : (X0⁻¹ * Gq D xs) b e ∈ aaD D e * aaD D b := by rw [mul_comm]; exact hY b e
    have key : star (X0⁻¹ a e) * (X0⁻¹ * Gq D xs) b e ∈ aaD D a * aaD D b := by
      rw [← LatA.aa_cancel2 e a b]; exact FractionalIdeal.mul_mem_mul hz hYe
    rw [mul_comm (aaD D b) (aaD D a), mul_comm ((X0⁻¹ * Gq D xs) b e)]
    exact key

theorem Gp_herm (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    (Gp D X0 xs)ᴴ = Gp D X0 xs := by
  have hG : (Gq D xs)ᴴ = Gq D xs := by
    refine Matrix.ext fun b c => ?_
    rw [Matrix.conjTranspose_apply]
    show star ((VS D).hT (xs c) (xs b)) = (VS D).hT (xs b) (xs c)
    rw [Alg.hsw, star_star]
  unfold Gp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem Xc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (v : InfinitePlace X.B.I.F) :
    Xc X (blkQ X u X0 xs M) v = X0.map (embS D (X.pl v)) := by
  ext b a
  simp only [Xc, Matrix.map_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2; rw [hd, map_one]
  · have : a < b := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    rw [hup b a this, map_zero]

theorem Gc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hW : ∀ b, InW X (xs b)) (v : InfinitePlace X.B.I.F) :
    Gc X u (blkQ X u X0 xs M) v = (Gq D xs).map (embS D (X.pl v)) := by
  ext b c
  simp only [Gc, Matrix.map_apply]
  rw [show Gq D xs b c = (VS D).hT (xs b) (xs c) from rfl, rowV_gram X u v (xs b) (xs c) (hW c)]
  rfl

theorem Hc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (hW : ∀ b, InW X (xs b))
    (v : InfinitePlace X.B.I.F) :
    Hc X u (blkQ X u X0 xs M) v = (Gp D X0 xs).map (embS D (X.pl v)) := by
  unfold Hc
  rw [Xc_blkQ X u X0 xs M hup hd v, Gc_blkQ X u X0 xs M hW v, map_inv' X0 hup hd]
  have hc : ((X0⁻¹).map (embS D (X.pl v)))ᴴ = ((X0⁻¹)ᴴ).map (embS D (X.pl v)) :=
    (Matrix.conjTranspose_map _ fun t => emb_star X v t).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.NOf
