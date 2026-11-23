import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolLowOnce

open GlobalTheory.HolDict.HolTo GlobalTheory.HolDict.CoefExt

theorem extLine_of_holShape : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S),
    GlobalTheory.HolDict.HolShape M → ExtLine M := by
  intro D V S M hM v v' hv hv' τ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have h1 : ∀ ρ, M.σ ρ 1 = 1 := fun ρ => (M.ds ρ).2.2.1.1.1
  have hv0 : ∀ ρ, ((v ρ : M.sm ρ) : M.H ρ) ≠ 0 := by
    intro ρ h0
    have hn := (hv ρ).1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  choose w hw using fun ρ c => wt_int (h1 ρ) (hv0 ρ) (hv ρ).2.2 (arr (nNeg (M.ε ρ)) c)
  have hW : WtIs M w := fun ρ c => hw ρ c
  obtain ⟨hsm, hk⟩ := GlobalTheory.T.baseFrameBorel_acts_extremalVector_by_weight D θ V S M w v hθ hM hW hv τ
  obtain ⟨hC, hU, hI, hO⟩ := GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal D V S M τ
  haveI := hC
  have hOF := (hO hM).1

  have hdet : (x0Mat M τ).det ≠ 0 := by
    intro h0
    have hd := congrArg Matrix.det hOF.2
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num

  set x : M.H τ := ((v τ : M.sm τ) : M.H τ) with hx
  set y : M.H τ := ((v' τ : M.sm τ) : M.H τ) with hy
  set c : ℂ := ⟪x, y⟫_ℂ with hc
  have hxx : ⟪x, x⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (hv τ).1]
    norm_num
  have horth : ⟪y - c • x, x⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_smul_left, hxx, mul_one, hc, inner_conj_symm, sub_self]
  have htor : ∀ s, M.rep τ (torEl (fun _ : Unit => x0Mat M τ) s ()) (y - c • x) =
      torCh (fun _ : Unit => w τ) s • (y - c • x) := by
    intro s
    have ex := torus_wt M hW τ (hv τ).2.2 s hdet
    have ey := torus_wt M hW τ (hv' τ).2.2 s hdet
    rw [map_sub, map_smul, ex, ey, smul_sub, smul_comm c]
  have hz := eq_zero_of_orth hOF hU hI hsm (hv0 τ) hk (y - c • x) (fun s => torEl_mem hOF s) htor horth
  have hyx : y = c • x := sub_eq_zero.mp hz
  refine ⟨c, ?_, ?_⟩
  · have hn := congrArg norm hyx
    rw [norm_smul, hy, (hv' τ).1, hx, (hv τ).1, mul_one] at hn
    exact hn.symm
  · exact Subtype.ext hyx

end GlobalTheory.HolLowOnce
