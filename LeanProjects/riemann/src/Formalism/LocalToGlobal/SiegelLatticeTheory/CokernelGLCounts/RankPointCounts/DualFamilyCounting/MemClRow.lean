import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GpHerm

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_cl_row (b : Fin D.R.rS) (x : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :
    x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ ∃ y ∈ aaLb X b, rowV X u y = x := by
  let f : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
    AddMonoidHom.mk' (rowV X u) (fun x y => rowV_add (X := X) (u := u) x y)
  let S : AddSubgroup (VS D).V := (Submodule.span (𝓞 D.host.E)
    {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}).toAddSubgroup
  have hc : cLat X u (Sum.inl (Sum.inr b)) = S.map f := AddSubgroup.closure_eq (S.map f)
  have key : x ∈ cLat X u (Sum.inl (Sum.inr b)) ↔ x ∈ S.map f := by
    rw [hc]; exact Iff.rfl
  exact key.trans AddSubgroup.mem_map

def imSub (a : Fin D.R.rS) : AddSubgroup D.host.E where
  carrier := {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
    D.host.conj t = -t}
  add_mem' := fun {s t} hs ht => ⟨Submodule.add_mem _ hs.1 ht.1, by rw [map_add, hs.2, ht.2, neg_add]⟩
  zero_mem' := ⟨Submodule.zero_mem _, by rw [map_zero, neg_zero]⟩
  neg_mem' := fun {t} ht => ⟨Submodule.neg_mem _ ht.1, by rw [map_neg, ht.2]⟩

def imHom : D.host.E →+ (InfinitePlace X.B.I.F → ℝ) where
  toFun t := fun v => (embS D (X.pl v) t).im
  map_zero' := by funext v; simp
  map_add' s t := by funext v; simp

theorem mem_cl_im (a : Fin D.R.rS) (x : InfinitePlace X.B.I.F → ℝ) :
    x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔
      ∃ t : D.host.E, t ∈ aaD D a * aaD D a ∧ D.host.conj t = -t ∧ (fun v => (embS D (X.pl v) t).im) = x := by
  have hc : cLat X u (Sum.inr (Sum.inr a)) = (imSub a).map (imHom X) :=
    AddSubgroup.closure_eq ((imSub a).map (imHom X))
  have key : x ∈ cLat X u (Sum.inr (Sum.inr a)) ↔ x ∈ (imSub a).map (imHom X) := by
    rw [hc]; exact Iff.rfl
  refine key.trans (AddSubgroup.mem_map.trans ?_)
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem im_inj {t t' : D.host.E} (ht : D.host.conj t = -t) (ht' : D.host.conj t' = -t')
    (h : ∀ v : InfinitePlace X.B.I.F, (embS D (X.pl v) t).im = (embS D (X.pl v) t').im) : t = t' := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace X.B.I.F))
  have hs : D.host.conj (t - t') = -(t - t') := by rw [map_sub, ht, ht']; ring
  have h1 := CovB.embS_conj (D := D) (X.pl v) (t - t')
  rw [hs, map_neg] at h1
  have him : (embS D (X.pl v) (t - t')).im = 0 := by rw [map_sub, Complex.sub_im, h v, sub_self]
  have hre : (embS D (X.pl v) (t - t')).re = 0 := by
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have h0 : embS D (X.pl v) (t - t') = 0 := Complex.ext hre him
  exact sub_eq_zero.mp ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

theorem aaLb_inW {b : Fin D.R.rS} {y : (VS D).V} (hy : y ∈ aaLb X b) : InW X y := by
  have hL : ∀ l ∈ X.Lb, InW X l := by
    intro l hl
    have hp := Alg.pW_inW (X := X) l
    have he : pW X l = l := by
      have h1 := Level.prV_Lb (X := X) l hl
      rw [Level.prV_apply] at h1
      simpa only [pW] using h1
    rwa [he] at hp
  simp only [aaLb, SetLike.mem_coe] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, l, hl, rfl⟩ := hx
    intro d
    exact ⟨by rw [map_smul, ((hL l hl) d).1, smul_zero], by rw [map_smul, ((hL l hl) d).2, smul_zero]⟩
  | zero => intro d; exact ⟨map_zero _, map_zero _⟩
  | add x z _ _ hx hz =>
    intro d
    exact ⟨by rw [map_add, (hx d).1, (hz d).1, add_zero], by rw [map_add, (hx d).2, (hz d).2, add_zero]⟩
  | smul o x _ hx =>
    intro d
    refine ⟨?_, ?_⟩
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).1, smul_zero]
    · rw [← algebraMap_smul D.host.E o x, map_smul, (hx d).2, smul_zero]

end Formalism.L2.SG.Pf.NcReal.JX.NOf
