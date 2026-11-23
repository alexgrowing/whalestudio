import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RootMapRoot
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.HasseEt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

private theorem root_isUnit {F : Type} [Field F] (p : F[X]) (h : p.coeff 0 ≠ 0) :
    IsUnit (AdjoinRoot.root p) := by
  have h1 : AdjoinRoot.mk p (X * p.divX + C (p.coeff 0)) = 0 := by
    rw [X_mul_divX_add, AdjoinRoot.mk_self]
  rw [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_eq_zero_iff_eq_neg] at h1
  exact isUnit_of_mul_isUnit_left (h1 ▸ ((Ne.isUnit h).map (AdjoinRoot.of p)).neg)

private theorem root_reduced {F : Type} [Field F] (p : F[X]) (h : p.Separable) :
    IsReduced (AdjoinRoot p) :=
  (Ideal.isRadical_iff_quotient_reduced _).1
    (isRadical_iff_span_singleton.1 h.squarefree.isRadical)

theorem UpperTheory.ConvolutionTheory.D.nmHasse :
    UpperTheory.ConvolutionTheory.D.NmHasse := by
  intro F E _ _ _ _ _ _ σ hσ n γ hγ hf hi
  have hG := galField F E σ hσ
  haveI : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hσ⟩⟩
  haveI := root_reduced _ hγ
  haveI : Module.Finite F (AdjoinRoot (cp γ)) := (Matrix.charpoly_monic _).finite_adjoinRoot
  have hu : IsUnit (AdjoinRoot.root (cp γ)) := by
    refine root_isUnit _ fun h0 => ?_
    have h1 := Matrix.det_eq_sign_charpoly_coeff γ.val
    rw [cp] at h0
    rw [h0, mul_zero] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero h1
  refine (nmAlg F E F σ _ hG n γ hγ).2.2 (hasseEt F E _ hu.unit (fun v => ?_) fun v => ?_)
  · exact (nmAlg F E _ σ _ hG n γ hγ).1.1 (hf v)
  · exact (nmAlg F E _ σ _ hG n γ hγ).1.1 (hi v)
