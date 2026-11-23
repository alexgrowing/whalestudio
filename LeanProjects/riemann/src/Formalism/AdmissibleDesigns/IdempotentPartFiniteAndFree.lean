import Formalism.AdmissibleDesigns.RowTopOf
import Formalism.AdmissibleDesigns.FiniteClassesLocalEq
import Formalism.AdmissibleDesigns.EKSymmCont

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section FinT

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

theorem rFree [Module.Finite O R'] : Module.Free O R' := by
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  exact Module.free_of_finite_type_torsion_free'

theorem idempotent_submodule_finite [Module.Finite O R'] (e₁ : R') : Module.Finite O (FirstSummandSubmodule O e₁) := by
  haveI : IsNoetherian O R' := isNoetherian_of_isNoetherianRing_of_finite O R'
  exact Module.Finite.of_injective (FirstSummandSubmodule O e₁).subtype Subtype.val_injective

theorem idempotent_submodule_free [Module.Finite O R'] (e₁ : R') : Module.Free O (FirstSummandSubmodule O e₁) := by
  haveI := idempotent_submodule_finite (R' := R') e₁
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  haveI : Module.IsTorsionFree O (FirstSummandSubmodule O e₁) := inferInstance
  exact Module.free_of_finite_type_torsion_free'

end FinT

section RecTop

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem idempotent_part_finite_and_free (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧ Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := Formalism.MainNotions.N.K.Topo.finite_R' hD
  exact ⟨idempotent_submodule_finite Dd.e₁, idempotent_submodule_free Dd.e₁⟩

def eL {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (FractionRing (D.nd.O i)) →ₗ[Br.LLw (D.nbr i _ hn)] Br.LLw (D.nbr i _ hn) where
  toFun k := eK (D.nbr i _ hn) k
  map_add' a b := map_add (eK (D.nbr i _ hn)) a b
  map_smul' c k := by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show FractionRing (D.nd.O i) from k)) =
      c * eK (D.nbr i _ hn) (show FractionRing (D.nd.O i) from k)
    rw [map_mul, RingEquiv.apply_symm_apply]

theorem rowTop1_S (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := K.Topo.finite_RD i r π g0 eB e₁ s Dd hD
  haveI : Module.Free (D.nd.O i) Dd.R' := rFree
  haveI := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  haveI := K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := K.Topo.rTop_smul (D.nd.O i) Dd.R'
  intro n _ hw c hc
  let b := Module.Free.chooseBasis (D.nd.O i) Dd.R'
  have hco : ∀ j, Continuous fun γ => b.equivFun ((c γ : Dd.R')) j := by
    intro j
    let f : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i] FractionRing (D.nd.O i) :=
      (Algebra.linearMap (D.nd.O i) (FractionRing (D.nd.O i))) ∘ₗ (b.coord j) ∘ₗ (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype
    let ℓ := (eL i dc hw).comp (trL (eK (D.nbr i _ hw)) (liftK f))
    have hℓ : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ
    have h1 : Continuous fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) := by
      have e1 : (fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))))) =
          fun g => ℓ (KRow.tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) := by
        funext g
        show _ = eK (D.nbr i _ hw) (liftK f (mkK (c (Br.iota D.nbr i _ hw g))))
        rw [liftK_mkK]
        rfl
      rw [e1]
      exact hℓ.comp hc
    have h2 : Continuous fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) := by
      refine continuous_induced_rng.2 ?_
      have e2 : ((↑) ∘ fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) =
          fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
            (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) :=
        funext fun g => (Br.toLLK_alg (D.nbr i _ hw) _).symm
      rw [e2]
      exact h1
    have h3 : Continuous fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')) := by
      have := (D.nbr i _ hw).eO_symm_cont.comp h2
      simpa [Function.comp_def] using this
    have heq : (fun γ => b.equivFun ((c γ : Dd.R')) j) =
        (fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) ∘ (Br.ιHomeo (D.nbr i _ hw)).symm := by
      funext γ
      simp only [Basis.equivFun_apply, Basis.coord_apply]
      exact congrArg (fun γ' => b.repr ((c γ' : Dd.R')) j) (((D.nbr i _ hw).e.symm_apply_apply γ).symm)
    rw [heq]
    exact h3.comp (Br.ιHomeo (D.nbr i _ hw)).symm.continuous
  have hv : Continuous fun γ => ((c γ : Dd.R')) := by
    have e3 : (fun γ => ((c γ : Dd.R'))) = fun γ => b.equivFun.symm (fun j => b.equivFun ((c γ : Dd.R')) j) :=
      funext fun γ => (b.equivFun.symm_apply_apply _).symm
    rw [e3]
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp (continuous_pi hco)
  exact continuous_induced_rng.2 hv

end RecTop

end Formalism.MainNotions.N.KRowA

end
