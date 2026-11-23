import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Matrix

namespace GlobalTheory.AdelicSvN.Weyl

variable {F : Type} [Field F] [NumberField F]

theorem trace_eq_mixedTrace (m : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) m = mixedTrace F m := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi, mixedTrace_apply]
  simp only [Algebra.trace_complex_apply, Algebra.trace_self_apply]

theorem isStd_infinite {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (z : InfiniteAdeleRing F) :
    ψ (infiniteAdeleInl z) = (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have hat : At (evI F) (infiniteAdeleInl z : AF F) := by
    intro u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [hψ.2.2 _ hat, h2, trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AF F) : ψ a = (adelicChar F a : ℂ) := by
  have hfin : ∀ y : FiniteAdeleRing (𝓞 F) F,
      ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ) := by
    intro y
    refine (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F).induction_on
      (p := fun y => ψ (finiteAdeleInr y) = (adelicChar F (finiteAdeleInr y) : ℂ)) y
      (isClosed_eq (hψ.1.comp continuous_finiteAdeleInr)
        (continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp continuous_finiteAdeleInr))) fun k => ?_
    have hs := infiniteAdeleInl_add_finiteAdeleInr (algebraMap F (AF F) k)
    rw [adeleRing_algebraMap_fst, adeleRing_algebraMap_snd] at hs
    have e : (finiteAdeleInr (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AF F) =
        algebraMap F (AF F) k + infiniteAdeleInl (-algebraMap F (InfiniteAdeleRing F) k) := by
      rw [← hs, map_neg]; abel
    rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hψ.2.1, adelicChar_algebraMap, one_mul, one_mul,
      isStd_infinite hψ]
  rw [← infiniteAdeleInl_add_finiteAdeleInr a, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul,
    isStd_infinite hψ, hfin]

variable {κ : Type} [Fintype κ]

theorem pureA_eq (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f g = schwartzBruhatTensorPi f g := by
  funext x
  simp only [pureA, schwartzBruhatTensorPi]
  rfl

omit [Fintype κ] in
theorem mem_SB_iff (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ↔ g ∈ finiteSchwartzBruhatPi F :=
  (mem_finiteSchwartzBruhatPi F).symm

theorem schA_eq : schA F κ = schwartzBruhatPi F κ := by
  unfold schA schwartzBruhatPi
  congr 1

def fourierLin : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun φ := adelicFourierPi F φ.1
  map_add' φ φ' := adelicFourierPi_add (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ.2))
    (integrable_of_mem_schwartzBruhatPi (schA_eq (F := F) (κ := κ) ▸ φ'.2))
  map_smul' c φ := adelicFourierPi_smul c φ.1

theorem act_weyl [DecidableEq κ] (w : (κ → AF F) × (κ → AF F)) :
    act (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) w = (w.2, -w.1) := by
  have h0 : (0 : Matrix κ κ F).map (algebraMap F (AF F)) = 0 := Matrix.map_zero _ (map_zero _)
  have h1 : (1 : Matrix κ κ F).map (algebraMap F (AF F)) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (-1 : Matrix κ κ F).map (algebraMap F (AF F)) = -1 := by rw [Matrix.map_neg _ (map_neg _), h1]
  simp only [act, Matrix.fromBlocks_map, h0, h1, h2, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem integral_add_right_pi (f : (κ → AF F) → ℂ) (a : κ → AF F) :
    ∫ x, f (x + a) ∂(adeleMeasurePi F) = ∫ x, f x ∂(adeleMeasurePi F) := by
  let _ : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have : MeasurableAdd (κ → AdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  exact integral_add_right_eq_self f a

theorem fourier_schr {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    adelicFourierPi F (schr ψ w φ) = schr ψ (w.2, -w.1) (adelicFourierPi F φ) := by
  funext y
  simp only [adelicFourierPi, schr, ← isStd_eq hψ]
  rw [← integral_const_mul, ← integral_add_right_pi _ (-w.1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h2 : ⅟(2 : AF F) + ⅟(2 : AF F) = 1 := invOf_two_add_invOf_two
  have e : ((x + -w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (x + -w.1) ⬝ᵥ y =
      (y ⬝ᵥ -w.1 + ⅟(2 : AF F) * (w.2 ⬝ᵥ -w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, dotProduct_comm y w.1,
      dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  have e' := congrArg ψ e
  rw [AddChar.map_add_eq_mul ψ _ ((x + -w.1) ⬝ᵥ y), AddChar.map_add_eq_mul ψ _ (x ⬝ᵥ (y + w.2))] at e'
  simp only [neg_add_cancel_right]
  change _ * _ * ψ ((x + -w.1) ⬝ᵥ y) = _ * (_ * ψ (x ⬝ᵥ (y + w.2)))
  linear_combination φ x * e'

theorem realised_weyl : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ], Realised ψ (Matrix.fromBlocks (0 : Matrix κ κ F) 1 (-1) 0) := by
  intro F _ _ ψ hψ κ _ _
  have hk : ∀ φ ∈ schA F κ, adelicFourierPi F φ ∈ schA F κ := fun φ hφ => by
    rw [schA_eq] at hφ ⊢
    exact adelicFourierPi_mem_schwartzBruhatPi hφ
  have hinv : ∀ φ ∈ schA F κ, adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := fun φ hφ => by
    rw [schA_eq] at hφ
    exact adelicFourierPi_adelicFourierPi hφ
  refine ⟨adelicFourierPi F, hk, fun φ hφ => ⟨_, hk _ (hk _ (hk _ hφ)), ?_⟩, fun l hl => ?_, fun w φ _ => ?_⟩
  · rw [hinv _ (hk _ (hk _ hφ)), hinv _ hφ]
    simp only [neg_neg]
  · obtain ⟨T, hT⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
    have hT' : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩
    refine ⟨l ∘ₗ T, fun g hg => ?_, fun φ hφ => by rw [LinearMap.comp_apply, hT' φ hφ]⟩
    obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
    refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
    rw [LinearMap.comp_apply, hT' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
      pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]
  · rw [act_weyl, fourier_schr hψ]

end GlobalTheory.AdelicSvN.Weyl

end
