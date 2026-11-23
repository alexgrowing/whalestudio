import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

theorem frame_values :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m r n : ℕ) (V : Submodule Ω E) (φ : Fin n → Module.Dual Ω E) (cb : Fin r → E), IsTwistGen ξ x L m φ → L.IsVB r V → LinearIndependent Ω cb → Submodule.span Ω (Set.range cb) = V → ∀ (p : Cpt ξ) (c : κ), InChart ξ x c p → ∃ (T : Matrix (Fin r) (Fin r) Ω) (C : Matrix (Fin r) (Fin n) Ω), IsUnit T.det ∧ L.IsFrameAt (colFrame cb T) p ∧ (∀ a b, ((Matrix.of fun a b => φ a (cb b)) * T) a b / x c ^ m ∈ regAt ξ p) ∧ (∀ a b, C a b ∈ regAt ξ p) ∧ ∀ a b, ∑ k, C a k * (((Matrix.of fun a b => φ a (cb b)) * T) k b / x c ^ m) = if a = b then 1 else 0 := by
  intro X Ω _ ξ E _ _ κ x L m r n V φ cb hG hV hli hsp p c hc
  obtain ⟨U, hU, b, hbsp, hb⟩ := hV p (Set.mem_univ p)
  have hf : L.IsFrameAt b p := hb p (Set.mem_univ p) hU
  have h1 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • cb a = b l := fun l => by
    have : b l ∈ Submodule.span Ω (Set.range cb) := by
      rw [hsp, ← hbsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  have h2 : ∀ l, ∃ t : Fin r → Ω, ∑ a, t a • b a = cb l := fun l => by
    have : cb l ∈ Submodule.span Ω (Set.range b) := by
      rw [hbsp, ← hsp]; exact Submodule.subset_span ⟨l, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  choose t ht using h1
  choose t' ht' using h2
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t l a
  let T' : Matrix (Fin r) (Fin r) Ω := Matrix.of fun a l => t' l a
  have hT : colFrame cb T = b := by
    funext l; exact ht l
  have hT' : colFrame b T' = cb := by
    funext l; exact ht' l
  have hmul : T * T' = 1 := by
    have e : colFrame cb (T * T') = colFrame cb (1 : Matrix (Fin r) (Fin r) Ω) := by
      rw [colFrame_mul, hT, hT', colFrame_one]
    ext a l
    have h3 := congrFun e l
    simp only [colFrame] at h3
    have h0 := (Fintype.linearIndependent_iff.1 hli) (fun a => (T * T') a l - (1 : Matrix _ _ Ω) a l)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h3, sub_self]) a
    exact sub_eq_zero.1 h0
  have hdet : IsUnit T.det := Matrix.isUnit_det_of_right_inverse hmul
  have hval : ∀ a l, ((Matrix.of fun a b => φ a (cb b)) * T) a l = φ a (b l) := by
    intro a l
    rw [← hT]
    simp [Matrix.mul_apply, colFrame, mul_comm]
  have hmem : ∀ l, b l ∈ L p := fun l => by
    rw [hf.2]; exact Submodule.subset_span ⟨l, rfl⟩
  have hw : ∀ l, ∃ w : Module.Dual Ω E, ∀ k, w (b k) = if l = k then 1 else 0 := fun l => by
    obtain ⟨w, h1, h0⟩ := GlobalTheory.CompanionTheory.Ar.FlagGrGen.exists_coord hf.1 l
    refine ⟨w, fun k => ?_⟩
    split_ifs with h
    · rw [← h]; exact h1
    · exact h0 k (Ne.symm h)
  choose w hw using hw
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hf.2] at he
    induction he using Submodule.span_induction with
    | mem e h =>
      obtain ⟨k, rfl⟩ := h
      rw [hw]
      split_ifs
      exacts [one_mem _, zero_mem _]
    | zero => simp [zero_mem]
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a e _ he =>
      have h4 : w l (a • e) = (a : Ω) * w l e := by rw [Subring.smul_def, map_smul, smul_eq_mul]
      rw [h4]; exact mul_mem a.2 he
  choose g hg hg' using fun l => hG.2 p c hc (w l) (hwreg l)
  refine ⟨T, Matrix.of g, hdet, ?_, ?_, ?_, ?_⟩
  · rw [hT]; exact hf
  · intro a l; rw [hval]; exact hG.1 a p c hc _ (hmem l)
  · intro a j; exact hg a j
  · intro a l
    simp only [hval, Matrix.of_apply]
    rw [← hg' a (b l) (hmem l), hw]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.RootsBase
