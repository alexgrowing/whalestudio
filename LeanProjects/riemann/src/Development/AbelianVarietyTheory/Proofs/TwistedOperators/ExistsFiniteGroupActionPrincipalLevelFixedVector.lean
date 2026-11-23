import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionIsAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PrinFixedRep

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GfC V) W}

theorem mem_fixed_iff {x : W} :
    x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) ↔
      ∀ h : GfC V, (h : GA D V) ∈ levG V β (flag1L L) → σ h x = x := by
  unfold GlobalTheory.PRep.fixed GlobalTheory.PRep.eig
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq,
    MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro H h hh
    exact H ⟨h, (Subgroup.mem_subgroupOf).2 hh⟩
  · intro H h
    exact H h ((Subgroup.mem_subgroupOf).1 h.2)

theorem act_eq_of_lifts {g0 : G0 L.Pg L.r} {κ κ' : GfC V} (hκ : IsLevelLift V β L g0 κ)
    (hκ' : IsLevelLift V β L g0 κ') {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) : σ κ' x = σ κ x := by
  have hm : ((κ⁻¹ * κ' : GfC V) : GA D V) ∈ levG V β (flag1L L) := by
    simpa using lift_div_mem hκ hκ'
  have e : κ' = κ * (κ⁻¹ * κ') := by group
  rw [e, map_mul, Module.End.mul_apply, (mem_fixed_iff.1 hx) _ hm]

theorem act_mem_fixed {g0 : G0 L.Pg L.r} {κ : GfC V} (hκ : IsLevelLift V β L g0 κ) {x : W}
    (hx : x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))) :
    σ κ x ∈ GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V)) := by
  rw [mem_fixed_iff] at hx ⊢
  intro h hh
  have hc := (GlobalTheory.FlagAction.conj_mem_flag1 hκ hh).1
  have hc' : ((κ⁻¹ * (h * κ) : GfC V) : GA D V) ∈ levG V β (flag1L L) := by simpa using hc
  have e : h * κ = κ * (κ⁻¹ * (h * κ)) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hx _ hc']

theorem main : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank),
    LiftsExist V β L → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
    ∃ ρ : Representation ℂ (G0 L.Pg L.r) (GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))),
      ∀ (g0 : G0 L.Pg L.r) (κ : GfC V), IsLevelLift V β L g0 κ → ∀ x, (ρ g0 x : W) = σ κ x := by
  intro D V β L hl W _ _ σ
  let lift : G0 L.Pg L.r → GfC V := fun g0 => ⟨(hl g0).choose, (hl g0).choose_spec.1⟩
  have hlift : ∀ g0, IsLevelLift V β L g0 (lift g0) := fun g0 => (hl g0).choose_spec
  let F := GlobalTheory.PRep.fixed σ ((levG V β (flag1L L)).subgroupOf (GfC V))
  have hs : ∀ g0, ∀ x ∈ F, σ (lift g0) x ∈ F := fun g0 x hx => act_mem_fixed (hlift g0) hx
  let ρ : Representation ℂ (G0 L.Pg L.r) F :=
    { toFun := fun g0 => (σ (lift g0)).restrict (hs g0)
      map_one' := LinearMap.ext fun x => Subtype.ext (by
        show σ (lift 1) x = x
        have h1 : IsLevelLift V β L 1 ((1 : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_one_of_mem (Subgroup.one_mem _)
        rw [act_eq_of_lifts h1 (hlift 1) x.2, map_one, Module.End.one_apply])
      map_mul' := fun g g' => LinearMap.ext fun x => Subtype.ext (by
        show σ (lift (g * g')) x = σ (lift g) (σ (lift g') x)
        have hm : IsLevelLift V β L (g * g') ((lift g * lift g' : GfC V) : GA D V) :=
          GlobalTheory.FlagAction.isLift_mul (hlift g) (hlift g')
        rw [act_eq_of_lifts hm (hlift (g * g')) x.2, map_mul, Module.End.mul_apply]) }
  refine ⟨ρ, fun g0 κ hκ x => ?_⟩
  show σ (lift g0) x = σ κ x
  exact act_eq_of_lifts hκ (hlift g0) x.2

end GlobalTheory.PrinFixedRep

end
