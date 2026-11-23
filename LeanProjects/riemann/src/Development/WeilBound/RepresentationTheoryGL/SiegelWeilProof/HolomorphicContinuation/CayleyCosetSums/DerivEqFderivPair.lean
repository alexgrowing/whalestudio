import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AnalyticAtInverseFirstBlock

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem deriv_eq_fderiv_pair (U : ℂ × V → ℂ) (z0 : ℂ) (w : V) (hU : DifferentiableAt ℂ U (z0, w)) :
    deriv (fun z => U (z, w)) z0 = fderiv ℂ U (z0, w) (1, 0) := by
  have hl : HasDerivAt (fun z : ℂ => (z, w)) ((1 : ℂ), (0 : V)) z0 := (hasDerivAt_id z0).prodMk (hasDerivAt_const z0 w)
  exact (hU.hasFDerivAt.comp_hasDerivAt z0 hl).deriv

theorem iFD_slice (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (z : ℂ) (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v = iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hU' : ContDiffOn ℂ ∞ (fun p : ℂ × V => U ((z, 0) + p)) (Set.univ ×ˢ D) :=
    hU.comp (contDiff_const.add contDiff_id).contDiffOn (fun p hp => ⟨trivial, by simpa using hp.2⟩)
  have hpre : (ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D) = D := by
    ext w
    simp
  have hfun : (fun w => U (z, w)) = (fun p : ℂ × V => U ((z, 0) + p)) ∘ (ContinuousLinearMap.inr ℂ ℂ V) := by
    funext w
    simp
  have hgw : ContinuousLinearMap.inr ℂ ℂ V w0 ∈ (Set.univ ×ˢ D : Set (ℂ × V)) := ⟨trivial, hw0⟩
  have hD' : IsOpen ((ContinuousLinearMap.inr ℂ ℂ V) ⁻¹' (Set.univ ×ˢ D)) := by rw [hpre]; exact hD
  rw [hfun, ← iteratedFDerivWithin_of_isOpen k hD' (by rw [hpre]; exact hw0),
    (ContinuousLinearMap.inr ℂ ℂ V).iteratedFDerivWithin_comp_right hU' hs.uniqueDiffOn hD'.uniqueDiffOn hgw
      (by exact_mod_cast (WithTop.coe_lt_top _).le),
    iteratedFDerivWithin_of_isOpen k hs hgw, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left]
  simp

private theorem natCast_le_infty_withTop (a : ℕ) : ((a : ℕ) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

private theorem inv_mul_mul_mul_eq_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → ℂ) (S : Set E)
    (hS : IsOpen S) (hf : ContDiffOn ℂ ∞ f S) (e : E) (k : ℕ) :
    ∀ y ∈ S, iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) y = fderiv ℂ (iteratedFDeriv ℂ k f) y e := by
  induction k with
  | zero =>
    intro y hy
    have hd : DifferentiableAt ℂ f y :=
      (hf.contDiffAt (hS.mem_nhds hy)).differentiableAt (by simp)
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp
  | succ k ih =>
    intro y hy
    have hev : iteratedFDeriv ℂ k (fun p => fderiv ℂ f p e) =ᶠ[nhds y]
        fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e :=
      Filter.eventually_of_mem (hS.mem_nhds hy) ih
    have hg : ContDiffAt ℂ 2 (iteratedFDeriv ℂ k f) y :=
      (hf.contDiffAt (hS.mem_nhds hy)).iteratedFDeriv_right (by
        have h : ((2 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
        exact_mod_cast h)
    have hsym : IsSymmSndFDerivAt ℂ (iteratedFDeriv ℂ k f) y :=
      hg.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
    have hdg : DifferentiableAt ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have happ : fderiv ℂ (fun p => fderiv ℂ (iteratedFDeriv ℂ k f) p e) y =
        (ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).comp (fderiv ℂ (fderiv ℂ (iteratedFDeriv ℂ k f)) y) :=
      ((ContinuousLinearMap.apply ℂ (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) ℂ) e).hasFDerivAt.comp y
        hdg.hasFDerivAt).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hev.fderiv_eq, happ,
      iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.comp_fderiv]
    ext m
    simp [hsym (m 0) e]

theorem iFD_deriv_comm (U : ℂ × V → ℂ) (D : Set V) (hD : IsOpen D) (hU : ContDiffOn ℂ ∞ U (Set.univ ×ˢ D))
    (w0 : V) (hw0 : w0 ∈ D) (k : ℕ) (v : Fin k → V) :
    iteratedFDeriv ℂ k (fun w => deriv (fun z => U (z, w)) 0) w0 v =
      deriv (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) 0 := by
  have hs : IsOpen (Set.univ ×ˢ D : Set (ℂ × V)) := isOpen_univ.prod hD
  have hdiffU : ∀ p ∈ (Set.univ ×ˢ D : Set (ℂ × V)), DifferentiableAt ℂ U p := fun p hp =>
    (hU.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have hU1 : ContDiffOn ℂ ∞ (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) (Set.univ ×ˢ D) :=
    (hU.fderiv_of_isOpen hs (m := ∞) (by exact le_of_eq (by rfl))).clm_apply contDiffOn_const
  have hL : (fun w => deriv (fun z => U (z, w)) 0) =ᶠ[nhds w0] fun w => fderiv ℂ U (0, w) ((1 : ℂ), (0 : V)) :=
    Filter.eventually_of_mem (hD.mem_nhds hw0) fun w hw => deriv_eq_fderiv_pair U 0 w (hdiffU (0, w) ⟨trivial, hw⟩)
  rw [((Filter.EventuallyEq.iteratedFDeriv ℂ hL k).eq_of_nhds),
    iFD_slice (fun p => fderiv ℂ U p ((1 : ℂ), (0 : V))) D hD hU1 0 w0 hw0 k v]
  have hR : (fun z => iteratedFDeriv ℂ k (fun w => U (z, w)) w0 v) =
      fun z => iteratedFDeriv ℂ k U (z, w0) (fun i => ((0 : ℂ), v i)) :=
    funext fun z => iFD_slice U D hD hU z w0 hw0 k v
  have hdI : DifferentiableAt ℂ (iteratedFDeriv ℂ k U) (0, w0) :=
    ((hU.contDiffAt (hs.mem_nhds ⟨trivial, hw0⟩)).iteratedFDeriv_right (m := 1) (by
      have h : ((1 + k : ℕ) : WithTop ℕ∞) ≤ ∞ := natCast_le_infty_withTop _
      exact_mod_cast h)).differentiableAt one_ne_zero
  have hdΦ : DifferentiableAt ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).differentiableAt.comp _ hdI
  rw [hR, deriv_eq_fderiv_pair _ 0 w0 hdΦ, inv_mul_mul_mul_eq_mul U _ hs hU _ k (0, w0) ⟨trivial, hw0⟩]
  have h2 : fderiv ℂ (fun p => iteratedFDeriv ℂ k U p (fun i => ((0 : ℂ), v i))) (0, w0) =
      (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).comp
        (fderiv ℂ (iteratedFDeriv ℂ k U) (0, w0)) :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => ℂ × V) ℂ (fun i => ((0 : ℂ), v i))).hasFDerivAt.comp
      (0, w0) hdI.hasFDerivAt).fderiv
  rw [h2]
  simp

end PositivityTheory.Rg.Sw.HSt
