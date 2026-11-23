import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLinkMeas

theorem map_covol {G H : Type} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalAddGroup G] [AddGroup H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [IsTopologicalAddGroup H] (e : G ≃+ H) (h1 : Continuous e) (h2 : Continuous e.symm) (Γ : AddSubgroup G)
    (Λ : AddSubgroup H) (hΓ : ∀ x, x ∈ Γ ↔ e x ∈ Λ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hv : μ 𝓕 = 1) :
    ∃ μ' : Measure H, (μ'.IsAddHaarMeasure ∧ ∃ 𝓕' : Set H, μ' 𝓕' = 1 ∧ IsAddFundamentalDomain Λ 𝓕' μ') ∧
      ∀ f : H → ℂ, ∫ y, f y ∂μ' = ∫ x, f (e x) ∂μ := by
  let t : G ≃ₜ H := { e.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  let E : G ≃ᵐ H := t.toMeasurableEquiv
  have hE : (E : G → H) = e := rfl
  refine ⟨μ.map e, ⟨AddEquiv.isAddHaarMeasure_map μ e h1 h2, e '' 𝓕, ?_, ?_⟩, fun f => integral_map_equiv E f⟩
  · rw [← hE, E.map_apply, Set.preimage_image_eq _ E.injective, hv]
  · let q : Λ ≃ Γ :=
      { toFun := fun y => ⟨e.symm y, (hΓ _).2 (by simpa using y.2)⟩
        invFun := fun x => ⟨e x, (hΓ _).1 x.2⟩
        left_inv := fun y => Subtype.ext (e.apply_symm_apply _)
        right_inv := fun x => Subtype.ext (e.symm_apply_apply _) }
    have hp : MeasurePreserving E μ (μ.map e) := ⟨E.measurable, rfl⟩
    refine h𝓕.image_of_equiv E.toEquiv (hp.symm E).quasiMeasurePreserving q fun g x => ?_
    show e (e.symm g + x) = g + e x
    rw [map_add, e.apply_symm_apply]

variable {D : D7} {m n d : ℕ}

theorem continuous_coord (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (coord ε : Mx D m n → _) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  exact continuous_pi fun p =>
    ((continuous_apply p.2.2).comp (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.toLinearMap)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))

theorem continuous_coordL_symm (ε : Module.Basis (Fin d) D.host.F D.host.E) : Continuous (coordL ε m n).symm := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  exact continuous_pi fun i => continuous_pi fun j =>
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF D.host.F) ε).equivFun.symm.toLinearMap).comp
      (continuous_pi fun k => continuous_apply (i, j, k))

theorem coord_rat (ε : Module.Basis (Fin d) D.host.F D.host.E) (γ : Matrix (Fin m) (Fin n) D.host.E)
    (p : Fin m × Fin n × Fin d) :
    coord ε (rat γ : Mx D m n) p = algebraMap D.host.F (AF D.host.F) (ε.repr (γ p.1 p.2.1) p.2.2) := by
  show (Algebra.TensorProduct.basis (AF D.host.F) ε).repr ((1 : AF D.host.F) ⊗ₜ[D.host.F] γ p.1 p.2.1) p.2.2 = _
  rw [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]

theorem mem_ratMx_iff (ε : Module.Basis (Fin d) D.host.F D.host.E) (x : Mx D m n) :
    x ∈ ratMx D m n ↔ coord ε x ∈
      (AddMonoidHom.compLeft (algebraMap D.host.F (AF D.host.F)).toAddMonoidHom (Fin m × Fin n × Fin d)).range := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨fun p => ε.repr (γ p.1 p.2.1) p.2.2, funext fun p => (coord_rat ε γ p).symm⟩
  · rintro ⟨c, hc⟩
    refine ⟨Matrix.of fun i j => ε.equivFun.symm fun k => c (i, j, k), (coord_bijective ε).1 ?_⟩
    rw [← hc]
    funext p
    refine (coord_rat ε _ p).trans ?_
    exact congrArg (algebraMap D.host.F (AF D.host.F))
      (congrFun (ε.equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2)

theorem exists_isTamagawa : ∀ (D : D7) (m n d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), IsCovolOne (ratMx D m n) μ 𝓕 → ∀ [MeasurableSpace (Fin m × Fin n × Fin d → AF D.host.F)] [BorelSpace (Fin m × Fin n × Fin d → AF D.host.F)], ∃ μ' : Measure (Fin m × Fin n × Fin d → AF D.host.F), IsTamagawa D.host.F (Fin m × Fin n × Fin d) μ' ∧ ∀ f : (Fin m × Fin n × Fin d → AF D.host.F) → ℂ, ∫ y, f y ∂μ' = ∫ x, f (coord ε x) ∂μ := by
  intro D m n d ε μ 𝓕 h _ _
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  exact map_covol (coordL ε m n).toAddEquiv (continuous_coord ε) (continuous_coordL_symm ε) (ratMx D m n) _
    (mem_ratMx_iff ε) μ 𝓕 h.1 h.2.1 h.2.2

end GlobalTheory.SWLinkMeas

end
