import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomFiniteVectorEqFiniteHeisenbergCombStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingVacuumTranslateSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotKerLevel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem fixTranslate (hX : IsBottomTri W i j X) (t : T) (u : WO A' WW) (hu : u.map (infPart D) = 0) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' →
      X.ω' t (κ, 1) (heisO W.ψ A' WW u X.vac') = heisO W.ψ A' WW u X.vac' := by
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.T.exists_open_subgroup_fixes_vacuum_definiteBottom hX t
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.T.exists_open_fixing_vacuum_translate_source D W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac'
    hX.is.isVac' u hu
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun κ hκ hf => ?_⟩
  rw [hW.om_heis κ 1 u X.vac' hX.is.isVac'.2.theta, h₁ κ hκ.1 hf, h₂ κ hκ.2 hf]

theorem exists_open_fix (hX : IsBottomTri W i j X) (t : T) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) (X.f' t) = X.f' t := by
  obtain ⟨n, c, x, hx, e⟩ := GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb hX t
  choose U hU hfix using fun k => fixTranslate hX t (x k) (hx k)
  refine ⟨⨅ k, U k, ?_, fun κ hκ hf => ?_⟩
  · have e2 : (((⨅ k, U k) : Subgroup (GA D A')) : Set (GA D A')) = ⋂ k, (U k : Set (GA D A')) := by
      ext y; simp [Subgroup.mem_iInf]
    rw [e2]
    exact isOpen_iInter_of_finite hU
  · rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hfix k κ (Subgroup.mem_iInf.1 hκ k) hf]

theorem continuous_finPart (V : HSp D) : Continuous (GlobalTheory.DefiniteClassAvg.finPart V) := by
  have e : GlobalTheory.DefiniteClassAvg.finPart V = fun y => (GlobalTheory.DefiniteClassAvg.realPart V y)⁻¹ * y := by
    funext y
    exact eq_inv_mul_of_mul_eq (GlobalTheory.DefiniteClassAvg.realPart_mul_finPart V y)
  rw [e]
  exact ((GlobalTheory.DefiniteClassAvg.continuous_realPart V).inv).mul continuous_id

theorem finPart_one (V : HSp D) : GlobalTheory.DefiniteClassAvg.finPart V 1 = 1 := by
  have h1 := GlobalTheory.DefiniteClassAvg.finPart_mul_realPart V 1
  have h2 : GlobalTheory.DefiniteClassAvg.finPart V 1 ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, GlobalTheory.DefiniteClassAvg.finPart_mem V 1⟩
    have : GlobalTheory.DefiniteClassAvg.finPart V 1 = (GlobalTheory.DefiniteClassAvg.realPart V 1)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (GinfC V).inv_mem (GlobalTheory.DefiniteClassAvg.realPart_mem V 1)
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact h2

theorem eq_of_finE_eq (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : Lev.finE V a = Lev.finE V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := by
    have inj : Function.Injective (Formalism.UG.bc (n := Fin V.rank) (Lev.swapAE D)) := by
      intro x y hxy
      apply Units.ext
      ext p q
      have := congrArg (fun z : GL (Fin V.rank) (Lev.EAf D) => z.1 p q) hxy
      simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective this
    exact inj h
  have h2 : a⁻¹ * b ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, (GfC V).mul_mem ((GfC V).inv_mem ha) hb⟩
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

theorem exists_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hfix⟩ := exists_open_fix hX t
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hθ : IsInfFam W.θ := hX.is.isVac'.2.inf
  have hf' : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
  let K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)) := St X.rA'.β ⊓ (U ⊓ GfC A').map (Lev.finE A')
  have hKo : IsOpen ((K.comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have hU1 : GlobalTheory.DefiniteClassAvg.finPart A' ⁻¹' (U : Set (GA D A')) ∈ nhds (1 : GA D A') :=
      (continuous_finPart A').continuousAt.preimage_mem_nhds (by rw [finPart_one]; exact hUo.mem_nhds U.one_mem)
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅, hU1] with κ h1 h2
    exact ⟨h1.2.1, ⟨GlobalTheory.DefiniteClassAvg.finPart A' κ, ⟨h2, GlobalTheory.DefiniteClassAvg.finPart_mem A' κ⟩,
      GlobalTheory.DefiniteClassAvg.finE_finPart A' κ⟩⟩
  have hKc : IsCompact ((Lev.levA A' K : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hKo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2.1
  refine ⟨K, ⟨hKo, hKc⟩, fun P h k hk g => ?_⟩
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  obtain ⟨u, ⟨huU, huf⟩, hue⟩ := hk2.2
  have hku : k = u := (eq_of_finE_eq A' huf hk1 hue).symm
  have hk3 : X.ω' t (k, 1) (X.f' t) = X.f' t := hku ▸ hfix u huU huf
  show X.ω' t (g * k, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((g * k, h) : GA D A' × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hθ k hk1 1 (GfC WW).one_mem
    _ _ _ _ _ P hf', hk3]

end GlobalTheory.BotKerLevel
