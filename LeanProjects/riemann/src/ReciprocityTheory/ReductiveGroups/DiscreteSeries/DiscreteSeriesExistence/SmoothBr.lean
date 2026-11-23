import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

noncomputable section

open Finset Matrix Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}

theorem smBr_inUJ_one : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by
  unfold inUJ; simp

theorem smBr_hasDerivAt_ext (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (fderiv ℝ F g (g * X)) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp : HasDerivAt (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F g (g * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
    filter_upwards [hmem] with t ht
    exact hfF _ ht (Formalism.REAL.indefinite_unitary_mul_mem ε hgJ (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))
  exact hcomp.congr_of_eventuallyEq hev

theorem smBr_rdExt (f F : Matrix (Fin n) (Fin n) ℂ → E) (U : Set (Matrix (Fin n) (Fin n) ℂ))
    (g X : Matrix (Fin n) (Fin n) ℂ) (hU : IsOpen U) (hg : g ∈ U) (hgJ : inUJ ε g)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ h ∈ U, inUJ ε h → f h = F h) (hX : inG ε X) :
    S7.RdV X f g = fderiv ℝ F g (g * X) :=
  (smBr_hasDerivAt_ext f F U g X hU hg hgJ hF hfF hX).deriv

theorem smBr_rdBracket (f : Matrix (Fin n) (Fin n) ℂ → E) (X Y g : Matrix (Fin n) (Fin n) ℂ)
    (hf : S7.SmoothOnGV ε f) (hX : inG ε X) (hY : inG ε Y) (hg : inUJ ε g) :
    S7.RdV X (S7.RdV Y f) g - S7.RdV Y (S7.RdV X f) g = S7.RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inG ε Z → ∀ k ∈ U, inUJ ε k → S7.RdV Z f k = fderiv ℝ F k (k * Z) :=
    fun Z hZ k hk hkJ => smBr_rdExt f F U k Z hU hk hkJ hF hfF hZ
  have hsm : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      ContDiffOn ℝ ∞ (fun k => fderiv ℝ F k (k * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply (Formalism.REAL.mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) Formalism.REAL.withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Matrix (Fin n) (Fin n) ℂ, fderiv ℝ (fun k => fderiv ℝ F k (k * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (Formalism.REAL.mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : S7.RdV X (S7.RdV Y f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * Y)) g (g * X) :=
    smBr_rdExt (S7.RdV Y f) _ U g X hU hgU hg (hsm Y) (ext Y hY) hX
  have e2 : S7.RdV Y (S7.RdV X f) g = fderiv ℝ (fun k => fderiv ℝ F k (k * X)) g (g * Y) :=
    smBr_rdExt (S7.RdV X f) _ U g Y hU hgU hg (hsm X) (ext X hX) hY
  have e3 := ext _ (Formalism.REAL.lie_algebra_bracket_mem hX hY) g hgU hg
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

end Helpers

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smBr_loc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (h : ∀ g, inUJ ε g → f g = f' g)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hg : inUJ ε g) :
    S7.RdV X f g = S7.RdV X f' g := by
  unfold S7.RdV
  congr 1
  funext t
  exact h _ (Formalism.REAL.indefinite_unitary_mul_mem ε hg (Formalism.REAL.exp_indefinite_unitary_holds n ε X hX t))

theorem smBr_dS_eq (Z : Matrix (Fin n) (Fin n) ℂ) (w : H) :
    dS σ Z w = S7.RdV Z (fun g => σ g w) 1 := by
  simp only [dS, S7.RdV, one_mul]

theorem smBr_orbit (hσ : IsURepOn (UJset ε) σ) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z)
    {v : H} (hv : IsSmoothVecU ε σ v) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    σ g (dS σ Z v) = S7.RdV Z (fun g => σ g v) g := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hv 1 smBr_inUJ_one
  have hc := smBr_hasDerivAt_ext (fun g => σ g v) F U 1 Z hU h1U smBr_inUJ_one hF hfF hZ
  simp only [one_mul] at hc
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hfun : ((σ g) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Z)) v) =
      fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v := by
    funext t
    rw [hσ.1.2 g hg _ (Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t)]
    rfl
  have h3 : HasDerivAt (fun t : ℝ => σ (g * NormedSpace.exp ((t : ℂ) • Z)) v)
      (σ g (fderiv ℝ F 1 Z)) 0 := by
    rw [← hfun]; exact h2
  rw [dS, hc.deriv, S7.RdV, h3.deriv]

end Main

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem dS_bracket (hσ : IsURepOn (UJset ε) σ) {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (hY : inG ε Y)
    {v : H} (hv : IsSmoothVecU ε σ v) :
    dS σ X (dS σ Y v) - dS σ Y (dS σ X v) = dS σ (X * Y - Y * X) v := by
  have e1 : dS σ X (dS σ Y v) = S7.RdV X (S7.RdV Y (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hY hv hg) hX smBr_inUJ_one
  have e2 : dS σ Y (dS σ X v) = S7.RdV Y (S7.RdV X (fun g => σ g v)) 1 := by
    rw [smBr_dS_eq]
    exact smBr_loc (fun g hg => smBr_orbit hσ hX hv hg) hY smBr_inUJ_one
  rw [e1, e2, smBr_dS_eq]
  exact smBr_rdBracket _ X Y 1 hv hX hY smBr_inUJ_one

end ReciprocityTheory.ChartRestriction.DS
