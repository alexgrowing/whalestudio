import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemClosureImage
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GpHerm
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Onto

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hc_congr (x y : BV X) (hX : ∀ p, x (Sum.inl (Sum.inl p)) = y (Sum.inl (Sum.inl p)))
    (hR : ∀ b, x (Sum.inl (Sum.inr b)) = y (Sum.inl (Sum.inr b))) : Hc X u x = Hc X u y := by
  funext v
  have h1 : Xc X x v = Xc X y v := by
    ext b a
    simp only [Xc, hX]
  have h2 : Gc X u x v = Gc X u y v := by
    ext b c
    simp only [Gc, hR]
  simp only [Hc, h1, h2]

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  rw [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, -, l, hl, rfl⟩ := hz
    intro a
    obtain ⟨h1, h2⟩ := X.Lb_perp l hl a
    simp only [map_smul, h1, h2, smul_zero, and_self]
  | zero =>
    intro a
    simp only [map_zero, and_self]
  | add z w _ _ hz hw =>
    intro a
    simp only [map_add, (hz a).1, (hz a).2, (hw a).1, (hw a).2, add_zero, and_self]
  | smul r z _ hz =>
    intro a
    simp only [LinearMap.map_smul_of_tower, (hz a).1, (hz a).2, smul_zero, and_self]

theorem mem_cl_row (b : Fin D.R.rS) (z : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    z ∈ AddSubgroup.closure (rowV X u '' aaLb X b) ↔ ∃ y ∈ aaLb X b, rowV X u y = z := by
  exact mem_closure_image (rowHom X u)
    (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup z

def imH (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Set D.host.E) ∧ D.host.conj t = -t}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro s t ⟨hs1, hs2⟩ ⟨ht1, ht2⟩
    exact ⟨Submodule.add_mem _ hs1 ht1, by rw [map_add, hs2, ht2, neg_add]⟩
  neg_mem' := by
    rintro s ⟨hs1, hs2⟩
    exact ⟨Submodule.neg_mem _ hs1, by rw [map_neg, hs2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (z : InfinitePlace X.B.I.F → ℝ) :
    z ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ ∃ t ∈ imH a, imHom X t = z := by
  exact mem_closure_image (imHom X) (imH a) z

end Onto

open Onto in

theorem fibOnto_holds : FibOnto := by
  intro D X u x hx
  have hA : ∀ p : LsNc5.LtPair D.R.rS, ∃ t ∈ aaD D p.1.1 * (aaD D p.1.2)⁻¹,
      embV X t = x (Sum.inl (Sum.inl p)) := by
    intro p
    have h := hx (Sum.inl (Sum.inl p))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_emb X _ _).1 h
  have hB : ∀ b : Fin D.R.rS, ∃ y ∈ aaLb X b, rowV X u y = x (Sum.inl (Sum.inr b)) := by
    intro b
    have h := hx (Sum.inl (Sum.inr b))
    simp only [tauQ, sub_zero] at h
    exact (mem_cl_row X u b _).1 h
  have hC : ∀ p : LsNc5.LtPair D.R.rS, ∃ s ∈ aaD D p.1.1 * aaD D p.1.2,
      embV X s = fun v => x (Sum.inr (Sum.inl p)) v - Hc X u x v p.1.1 p.1.2 / 2 :=
    fun p => (mem_cl_emb X _ _).1 (hx (Sum.inr (Sum.inl p)))
  have hD : ∀ a : Fin D.R.rS, ∃ t ∈ imH a, imHom X t =
      fun v => x (Sum.inr (Sum.inr a)) v - -((Hc X u x v a a).re * (embS D (X.pl v) (theta D)).im) :=
    fun a => (mem_cl_im X u a _).1 (hx (Sum.inr (Sum.inr a)))
  choose tA htA htA' using hA
  choose xs hxs hxs' using hB
  choose sC hsC hsC' using hC
  choose tD htD htD' using hD
  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      X0 = fun b a => if h : b < a then tA ⟨(b, a), h⟩ else if b = a then 1 else 0 := ⟨_, rfl⟩
  have hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0 := by
    intro b a h
    simp [hX0, not_lt_of_gt h, ne_of_gt h]
  have hdg : ∀ a, X0 a a = 1 := by
    intro a
    simp [hX0]
  have hX0p : ∀ p : LsNc5.LtPair D.R.rS, X0 p.1.1 p.1.2 = tA p := by
    intro p
    simp [hX0, p.2]
  have hW : ∀ b, InW X (xs b) := fun b => aaLb_inW X (hxs b)
  have hGh : ∀ i j, star (Gp D X0 xs j i) = Gp D X0 xs i j := by
    intro i j
    have := congrFun (congrFun (Gp_herm X0 xs) i) j
    rwa [Matrix.conjTranspose_apply] at this
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      M = fun b a => if h : b < a then sC ⟨(b, a), h⟩
        else if h' : a < b then -Gp D X0 xs b a - star (sC ⟨(a, b), h'⟩)
        else tD a - Gp D X0 xs a a * theta D := ⟨_, rfl⟩
  have hMlt : ∀ p : LsNc5.LtPair D.R.rS, M p.1.1 p.1.2 = sC p := by
    intro p
    simp [hM, p.2]
  have hMgt : ∀ p : LsNc5.LtPair D.R.rS,
      M p.1.2 p.1.1 = -Gp D X0 xs p.1.2 p.1.1 - star (sC p) := by
    intro p
    simp [hM, p.2, not_lt_of_gt p.2]
  have hMd : ∀ a, M a a = tD a - Gp D X0 xs a a * theta D := by
    intro a
    simp [hM]
  have hth : star (theta D) = 1 - theta D := by
    rw [Inh.tie_star]
    exact eq_sub_of_add_eq' (theta_spec D).2
  have hData : DataOK X X0 xs M := by
    refine ⟨hup, hdg, hW, ?_⟩
    ext i j
    simp only [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.neg_apply]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hMlt ⟨(i, j), h⟩, hMgt ⟨(i, j), h⟩, star_sub, star_neg, star_star, hGh]
      ring
    · obtain ⟨-, hc⟩ := htD i
      rw [hMd, star_sub, star_mul', Inh.tie_star D (tD i), hc, hth, hGh]
      ring
    · rw [hMlt ⟨(j, i), h⟩, hMgt ⟨(j, i), h⟩]
      ring
  have hXb : ∀ p, x (Sum.inl (Sum.inl p)) = blkQ X u X0 xs M (Sum.inl (Sum.inl p)) := by
    intro p
    show _ = embV X (X0 p.1.1 p.1.2)
    rw [hX0p]
    exact (htA' p).symm
  have hRb : ∀ b, x (Sum.inl (Sum.inr b)) = blkQ X u X0 xs M (Sum.inl (Sum.inr b)) := by
    intro b
    exact (hxs' b).symm
  have hHc : ∀ v, Hc X u x v = (Gp D X0 xs).map (embS D (X.pl v)) := by
    intro v
    rw [hc_congr X u x _ hXb hRb]
    exact Hc_blkQ X u X0 xs M hup hdg hW v
  refine ⟨X0, xs, M, hData, ?_⟩
  funext p
  rcases p with ((p | b) | (p | a))
  · exact (hXb p).symm
  · exact (hRb b).symm
  · funext v
    show (embS D (X.pl v) (M p.1.1 p.1.2) - star (embS D (X.pl v) (M p.1.2 p.1.1))) / 2 = _
    have hs := congrFun (hsC' p) v
    simp only [embV, hHc v, Matrix.map_apply] at hs
    have e1 : star (embS D (X.pl v) (M p.1.2 p.1.1)) =
        -embS D (X.pl v) (Gp D X0 xs p.1.1 p.1.2) - embS D (X.pl v) (sC p) := by
      rw [hMgt, ← emb_star X, star_sub, star_neg, star_star, hGh, map_sub, map_neg]
    rw [e1, hMlt]
    linear_combination hs
  · funext v
    show (embS D (X.pl v) (M a a)).im = _
    have hs := congrFun (htD' a) v
    simp only [imHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hHc v, Matrix.map_apply] at hs
    have hr : (embS D (X.pl v) (Gp D X0 xs a a)).im = 0 := by
      have := congrArg (embS D (X.pl v)) (hGh a a)
      rw [emb_star X] at this
      exact Complex.conj_eq_iff_im.mp this
    rw [hMd, map_sub, map_mul, Complex.sub_im, Complex.mul_im, hr]
    linear_combination hs

end Formalism.L2.SG.Pf.NcReal.JX.NOf
