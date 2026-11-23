import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdNormOne
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AutOrder
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem mapTrans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (σ.trans τ)) g : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap τ)
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 σ τ _

private theorem mapRefl (K : Type) [Field K] [NumberField K] (n : ℕ)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (RingEquiv.refl K)) g : AdelicGLn.AdelicGL K n) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _

private noncomputable def resMap (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : G1 K n) :
    G1 K n :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n),
    (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).1.2 g.2⟩

private theorem resMap_trans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K) (g : G1 K n) :
    resMap K n τ (resMap K n σ g) = resMap K n (σ.trans τ) g :=
  Subtype.ext (mapTrans K n σ τ g).symm

private theorem resMap_refl (K : Type) [Field K] [NumberField K] (n : ℕ) (g : G1 K n) :
    resMap K n (RingEquiv.refl K) g = g :=
  Subtype.ext (mapRefl K n g)

private theorem resMap_cont (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) :
    Continuous (resMap K n σ) := by
  refine Continuous.subtype_mk (Continuous.comp ?_ continuous_subtype_val) _
  exact Continuous.units_map _ (continuous_id.matrix_map (Formalism.L2.Host.CT.continuous_adMap σ))

private theorem resMap_iter (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (m : ℕ) (g : G1 K n) :
    (resMap K n σ)^[m] g = resMap K n (σ ^ m) g := by
  induction m with
  | zero => exact (resMap_refl K n g).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, resMap_trans, pow_succ']
    rfl

theorem UpperTheory.ConvolutionTheory.K.galEquiv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K), ∃ e : G1 K n ≃ₜ* G1 K n,
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g : G1 K n, ((e.symm g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.symm) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) ∧ ∃ m : ℕ, 0 < m ∧ ∀ g, (⇑e)^[m] g = g := by
  intro K _ _ n σ
  obtain ⟨m, hm, hσ⟩ := UpperTheory.ConvolutionTheory.K.autOrder K σ
  refine ⟨{ toFun := resMap K n σ
            invFun := resMap K n σ.symm
            left_inv := fun g => by rw [resMap_trans, RingEquiv.self_trans_symm, resMap_refl]
            right_inv := fun g => by rw [resMap_trans, RingEquiv.symm_trans_self, resMap_refl]
            map_mul' := fun g h => Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ))
              (g : AdelicGLn.AdelicGL K n) (h : AdelicGLn.AdelicGL K n))
            continuous_toFun := resMap_cont K n σ
            continuous_invFun := resMap_cont K n σ.symm },
    fun _ => rfl, fun _ => rfl, fun g => ?_, m, hm, fun g => ?_⟩
  · exact (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).2
  · change (resMap K n σ)^[m] g = g
    rw [resMap_iter, hσ]
    exact resMap_refl K n g
