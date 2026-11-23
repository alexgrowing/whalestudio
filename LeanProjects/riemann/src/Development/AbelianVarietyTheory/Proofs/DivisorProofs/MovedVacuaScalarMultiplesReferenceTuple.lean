import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitNeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotScal

open GlobalTheory.KappaArith (AwayIm)

variable {D : D7} {T : Type} {Lc : LevCh D T}

theorem xi_awayIm_of_infPart {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ)
    (hu : infPart D (u : AE D) = 1) : AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨j, j1, j2, j3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D j j1 j2 (GlobalTheory.PlaceIdem.exists_isPlIdem D j j1 j2 j3)
    (Lc.xi t) (Lc.xiH t) (hL.xi t)
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom u)
  rw [hprod u hu S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS']
  exact AwayIm.prod _ _ fun P _ => GlobalTheory.KappaArith.awayIm_val hL hx m P (Formalism.L2.Host.atFin P (k P))

theorem xi_awayIm {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ) (u : (AE D)ˣ) :
    AwayIm D m ((Lc.xi t u : Circle) : ℂ) := by
  obtain ⟨v, hv1, hv2, hv3⟩ := GlobalTheory.TameFinitePart.exists_lift D (Units.map (finPart D).toMonoidHom u)
  obtain ⟨n, hn0, hn⟩ := hL.xi_fin t
  have h1 : Lc.xi t (u * v⁻¹) = 1 := GlobalTheory.TupRoot.eq_one_of_finPart (hL.xi t) hn0 hn _ (by
    rw [Units.val_mul, map_mul, hv3]
    exact Units.mul_inv (Units.map (finPart D).toMonoidHom u))
  have h2 : Lc.xi t u = Lc.xi t v := by
    have := congrArg (· * Lc.xi t v) h1
    simpa [map_mul, map_inv] using this
  rw [h2]
  exact xi_awayIm_of_infPart hL hx m v hv1

end GlobalTheory.BotScal

namespace GlobalTheory.BotScal

theorem moved_vacua_scal : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
    ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (Y : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    ∃ r r' : T → ℂ, (∀ t, r t ≠ 0 ∧ r' t ≠ 0) ∧ (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω μ₀ (g, h) Y.vac) ∧
      (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' μ₀ (g', h) Y.vac') ∧
      ∀ t, ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ r' t / r t = D.what₂.embLL ζ * (r' μ₀ / r μ₀) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW Y hY g hg g' hg' h hh
  have hI := hY.2.2.2.2.2.2.2
  obtain ⟨x, hx⟩ := GlobalTheory.RecDict.exists_isDetRoot D (GlobalTheory.Grid.neg A) ((GlobalTheory.Grid.ofSgn true A).symm g)
  obtain ⟨x', hx'⟩ := GlobalTheory.RecDict.exists_isDetRoot D A' g'
  obtain ⟨y, hy⟩ := GlobalTheory.RecDict.exists_isDetRoot D WW h
  have hvac : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW Y.vac := hI.isVac.2.theta
  have hvac' : IsThetaFunO W.ψ A' WW Y.vac' := hI.isVac'.2.theta
  have e := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ _ _ _ (hI.weil μ₀) (hI.weil t) _ h x y hx hy _ hvac
  have e' := fun t => GlobalTheory.WeilChange.weilData_differ_by_splitFac D W.ψ A' WW _ _ _ _ _ _ (hI.weil' μ₀) (hI.weil' t) g' h x' y hx' hy _ hvac'
  let a : T → (AE D)ˣ →* Circle := fun t => Lc.mu t (↑j + 1) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  let b : (AE D)ˣ →* Circle := G.ch.chi (D.R.m - ↑i) * Lc.eta ^ (rankV D ↑i ↑j % 2)
  refine ⟨fun t => ((splitFacO b (b / a t) x y : Circle) : ℂ) * ((splitFacO b (b / a μ₀) x y : Circle) : ℂ)⁻¹,
    fun t => ((splitFacO (a t) (a t / b) x' y : Circle) : ℂ) * ((splitFacO (a μ₀) (a μ₀ / b) x' y : Circle) : ℂ)⁻¹,
    fun t => ⟨?_, ?_⟩, fun t => ?_, fun t => ?_, ?_⟩
  rotate_left 2
  · have := e t
    simp only [GlobalTheory.Grid.WRep.toSgn, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.id_apply] at this
    exact this
  · exact e' t
  · intro t
    have hb : Lc.xi μ₀ = 1 := MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi μ₀))
    obtain ⟨ζ, hζ, hζe⟩ := xi_awayIm hL (hN.chars.xi t) (Qn G t) (x'⁻¹ * y * x⁻¹)
    refine ⟨ζ, hζ, ?_⟩
    rw [hζe]
    simp only [splitFacO, a, b, LevCh.mu, Formalism.IndefR.Lift.tup, hb, Circle.coe_mul, Circle.coe_inv, MonoidHom.div_apply,
      MonoidHom.mul_apply, MonoidHom.one_apply, map_mul, map_inv, Circle.coe_div, mul_one]
    field_simp [Circle.coe_ne_zero]
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  · exact mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

end GlobalTheory.BotScal
