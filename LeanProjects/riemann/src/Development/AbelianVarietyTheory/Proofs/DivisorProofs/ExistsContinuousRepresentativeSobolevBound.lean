import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjModelExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDiscreteSeriesModelsUnitarilyEquivaleStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjEq

theorem exists_conjModel_cast {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (e : S' = fun τ => dualPar (S τ))
    (M : DSModel V S) (v : M.Vec) (hv : IsExtVec M v) :
    ∃ (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (v' : M'.Vec),
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ y, c τ (M'.rep τ g y) = M.rep τ g (c τ y)) ∧ IsExtVec M' v' := by
  subst e
  exact GlobalTheory.ConjExt.exists_conjModel_ext D V S M v hv

theorem exists_conj_equiv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ i σ, ¬ GoodEmb T.Q.c (res T σ) → ∃ c : ∀ τ, (R.MW i σ).H τ ≃ₗᵢ⋆[ℂ] (R.MW i ((starRingEnd ℂ).comp σ)).H τ, ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ), ∀ y, c τ ((R.MW i σ).rep τ g y) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (c τ y) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM hT i σ hσ
  have hg : GoodEmb T.Q.c (res T ((starRingEnd ℂ).comp σ)) := good_resC T hσ
  obtain ⟨hs, -, w, hw⟩ := GlobalTheory.HolDict.holShape_of_good D G Pl0 T0 A T R κ v₀ hT i _ hg
  obtain ⟨M', c, v', hc, hv'⟩ := exists_conjModel_cast (GlobalTheory.ConjReading.parAt_conj (Wc D i) σ) (R.MW i σ) (v₀ i σ)
    (hT.hv₀ i σ).1
  obtain ⟨U, hU⟩ := GlobalTheory.T.holomorphic_discrete_series_models_unitarily_equivalent D R.θ _ _ (R.MW i ((starRingEnd ℂ).comp σ)) M' w (v₀ i _) v' hM.inf hs hw
    (hT.hv₀ i _).1 hv'
  refine ⟨fun τ => (c τ).symm.trans (U τ), fun τ g hg y => ?_⟩
  show U τ ((c τ).symm _) = (R.MW i ((starRingEnd ℂ).comp σ)).rep τ g (U τ ((c τ).symm y))
  rw [← hU τ g hg]
  congr 1
  apply (c τ).injective
  rw [hc τ g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

end GlobalTheory.ConjEq
