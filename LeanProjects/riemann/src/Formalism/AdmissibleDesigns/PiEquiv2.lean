import Formalism.AdmissibleDesigns.NormalizedRingData
import Formalism.AdmissibleDesigns.DisplayForms
import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap
import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound
import Formalism.AdmissibleDesigns.InertiaActsTrivially
import Formalism.AdmissibleDesigns.KernelLengthHigherColumns

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)

theorem rhoTwo_eq (g : Ω ≃ₐ[Ek] Ω) (y : {a // bl a = 0} → O) :
    rhoTwo (ρk 0) r χ ε g y = KLat.rho2 r χ bl ρk ε g y := by
  simp [rhoTwo, KLat.rho2, KLat.repL', KLat.M0]
  rfl

theorem pi_equiv2 (e₁ : R') (w : {a // bl a = 0} → O) (g : Ω ≃ₐ[Ek] Ω) (b : FirstSummandSubmodule O e₁) :
    piM (ρk 0) e₁ w (firstSummandRep O r χ e₁ ε g b) = KLat.rho2 r χ bl ρk ε g (piM (ρk 0) e₁ w b) := by
  rw [← rhoTwo_eq]
  apply pi_equiv

theorem gamM_eq (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0) : gamM (ρk 0) y m = KLat.gam bl ρk y m := rfl

end Gen

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc)

instance fracAdd : IsTopologicalAddGroup (FractionRing (D.nd.O i)) := Topo.fracTop_addGroup_O i
instance fracSmul : ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i)) := Topo.fracTop_smul_O i

instance rSmul {D : D7} (i : D.nd.Loc)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) :
    ContinuousConstSMul (D.nd.O i) Dd.R' := Topo.rTop_constSMul_RD i Dd

section Rec

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Lr : Type := LatM (D.nd.O i) (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev Vr : Type := LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev rho1 := firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)

abbrev rho2 := KLat.rho2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i)

theorem hKm : ContinuousMul (FractionRing (D.nd.O i)) := by
  infer_instance

theorem hEps : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
  KLat.eps_cont_nf (D.nd.l i) (Topo.padicCoeff_O i) (epsU D.nd i) (Topo.isCyc_eps i)

theorem hM0 (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KLat.block_zero_continuous Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (Topo.padicCoeff_O i) (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD)
    (Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc)

variable (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev DatS (w : ℕ) := KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev uDS (w : ℕ) := KLat.uD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev vDS (w : ℕ) := KLat.vD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS (w : ℕ) := KLat.modT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS' (w : ℕ) := KLat.modT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

theorem huDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    uDS i r π dc g0 eB e₁ s Dd hD hc w
        (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) ((decs D.host.E (Aw i dc)) w) g m) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρA g (uDS i r π dc g0 eB e₁ s Dd hD hc w m) :=
  KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w g m

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev piS := piDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hpDS (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Continuous fun t => vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KLat.hpD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (piS i Dd hT hrk)
    (piM_cont (Topo.padicCoeff_O i) (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD) (Dd.ρk 0) Dd.e₁
      (wDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk)) (Topo.fracTop_O i) w

theorem heDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (t : FirstSummandSubmodule (D.nd.O i) Dd.e₁) :
    vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk (resRep (rho1 i Dd) ((decs D.host.E (Aw i dc)) w) g t)) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρTl' g (vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t)) :=
  KLat.heD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (rho1 i Dd) (piS i Dd hT hrk)
    (fun g x => pi_equiv2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) Dd.e₁ _ g x) w g t

abbrev v1S := v1Dd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev eveS := eveDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev evES := evEDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT
abbrev lamS := lamDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hevES (g : GE D.nd) (a : LeftId (D.nd.O i) Dd.E) :
    evES i Dd hT (uElt Dd.r Dd.χ g • a) = evES i Dd hT a :=
  evEM_inv Dd.r Dd.χ _ _ _ _ (top_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT).2.2.2.2 g a

end Rec

end Formalism.MainNotions.N.K.St

end
