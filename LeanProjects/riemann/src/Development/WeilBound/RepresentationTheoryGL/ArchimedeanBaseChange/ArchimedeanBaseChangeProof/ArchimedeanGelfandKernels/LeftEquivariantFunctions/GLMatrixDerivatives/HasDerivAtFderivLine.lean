import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KbCurve

noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbFr

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem isOpen_GLs' : IsOpen (GLs n) :=
  isOpen_compl_singleton.preimage (contDiff_det (n := n)).continuous

theorem line_mem (X : Mat n) : ∀ᶠ t : ℝ in 𝓝 0, 1 + t • X ∈ GLs n := det_line_ne X

theorem hasDerivAt_fderiv_line {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} {x : Mat n}
    (hF : DifferentiableAt ℝ F x) (v : Mat n) : HasDerivAt (fun t : ℝ => F (x + t • v)) (fderiv ℝ F x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simp only [id, one_smul] at h
    exact h
  exact hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

theorem diffAt_of {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {F : Mat n → Z} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ F x :=
  ((hF.contDiffAt (isOpen_GLs'.mem_nhds hx)).differentiableAt (by simp))

theorem one_mem : (1 : Mat n) ∈ GLs n := by simp [GLs]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem hasDerivAt_Fr_line (h : CxData lam E Fr ε ι S Γ T) (Y : Mat n) :
    HasDerivAt (fun t : ℝ => Fr (1 + t • Y)) (fderiv ℝ Fr 1 Y) 0 :=
  hasDerivAt_fderiv_line (diffAt_of h.smooth one_mem) Y

theorem conjT_line {X : Mat n} (hX : X.IsHermitian) (t : ℝ) : (1 + t • X)ᴴ = 1 + t • X := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hX.eq]
  simp

theorem frComm_at (h : CxData lam E Fr ε ι S Γ T) {X H : Mat n} (hX : X.IsHermitian) (hH : H.IsHermitian) :
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ := by
  have hF := hasDerivAt_Fr_line h X
  constructor
  · set εc : Mat n →L[ℝ] (E.V →L[ℂ] E.V) := LinearMap.toContinuousLinearMap ε
    have hM : HasDerivAt (fun t : ℝ => (1 + t • X) * H * (1 + t • X)) (X * H + H * X) 0 := by
      have := hasDerivAt_matmul (hasDerivAt_matmul (hasDerivAt_line X) (hasDerivAt_const (0 : ℝ) H)) (hasDerivAt_line X)
      refine this.congr_deriv ?_
      simp
    have hE : HasDerivAt (fun t : ℝ => ε ((1 + t • X) * H * (1 + t • X))) (ε (X * H + H * X)) 0 :=
      εc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
    have hR := hF.mul hE
    have hL := hF.const_mul (ε H)
    have e : ∀ᶠ t : ℝ in 𝓝 0, ε H * Fr (1 + t • X) = Fr (1 + t • X) * ε ((1 + t • X) * H * (1 + t • X)) := by
      filter_upwards [line_mem X] with t ht
      have := h.frε _ ht H hH
      rwa [conjT_line hX] at this
    have hL' := hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)
    have u := hL'.unique hR
    simp only [zero_smul, add_zero, h.one, one_mul, Matrix.mul_one] at u
    rw [u]; abel
  · have hL := hF.const_mul Γ
    have hR := hF.mul_const Γ
    have e : ∀ᶠ t : ℝ in 𝓝 0, Γ * Fr (1 + t • X) = Fr (1 + t • X) * Γ := by
      filter_upwards [line_mem X] with t ht
      exact h.ΓFr _ ht
    exact (hL.congr_of_eventuallyEq (e.mono fun t ht => ht.symm)).unique hR

end

theorem frComm : FrComm := fun _ _ _ _ _ _ _ _ _ h _X _H hX hH => frComm_at h hX hH

end PositivityTheory.RgBcC.LfSt.Kchain.KbFr
