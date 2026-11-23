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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRank
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingNegativeVacuumDefiniteBottomStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.SrcLevel

theorem ker_finE {D : D7} (V : HSp D) {k : GA D V} (hk : Lev.finE V k = 1) : k ∈ GinfC V := by
  show finHom V k = 1
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have h1 : Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1 := hk
  apply Units.ext
  have h2 := congrArg Units.val h1
  change Matrix.map (finHom V k).val (Lev.swapAE D) = 1 at h2
  refine Matrix.map_injective hinj ?_
  beta_reduce
  rw [h2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem level_of_open {D : D7} (V : HSp D) (U : Subgroup (GA D V)) (hUo : IsOpen (U : Set (GA D V)))
    (hinf : GinfC V ≤ U) :
    ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K ∧ ∀ k ∈ Lev.levA V K, k ∈ U := by
  obtain ⟨ho, hc⟩ := GlobalTheory.FunObj.congLev_open_compact V (GlobalTheory.HeckeDual.isLattice_frameLat V) (𝔪 := ⊤) top_ne_bot
  set K₀ := congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) ⊤ with hK₀
  have hmem : ∀ k ∈ Lev.levA V (K₀ ⊓ U.map (Lev.finE V)), k ∈ U := by
    intro k hk
    obtain ⟨-, hkK⟩ := Lev.mem_levA.1 hk
    obtain ⟨k', hk'U, e⟩ := Subgroup.mem_map.1 hkK.2
    have h1 : k'⁻¹ * k ∈ GinfC V := ker_finE V (by rw [map_mul, map_inv, e, inv_mul_cancel])
    have h2 := U.mul_mem hk'U (hinf h1)
    rwa [mul_inv_cancel_left] at h2
  have hopen : IsOpen (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [Subgroup.comap_inf, Subgroup.coe_inf]
    exact ho.inter (Subgroup.isOpen_mono (Subgroup.le_comap_map _ _) hUo)
  refine ⟨K₀ ⊓ U.map (Lev.finE V), ⟨hopen, ?_⟩, hmem⟩
  have hcl : IsClosed ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) =
        (GfC V : Set (GA D V)) ∩ (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
    rw [e]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ hopen)
  refine hc.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hk
  exact Lev.mem_levA.2 ⟨h1, h2.1⟩

theorem dat_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac → X.ω t (k, 1) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hUinf, hU⟩ := GlobalTheory.T.definiteBottom_deepPoints_fix_lattice_stdFirst hX t
  refine ⟨U, hUo, hUinf, fun k hkU hkf hv => ?_⟩
  obtain ⟨hΛ, hΦ⟩ := hU k hkU hkf
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hmv := GlobalTheory.TypeMove.isThetaAt_move hW hsdS hsdT (GlobalTheory.PlaceDatum.idemSum_mul_self (hX.is.idem t))
    (GlobalTheory.PlaceDatum.infPart_idemSum (hX.is.idem t)) hΛ hX.is.isVac.2.theta (by rw [e1]; exact hv) (hX.is.fst t)
  have hf := hX.is.fst t
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hmv
  obtain ⟨-, hall'⟩ := hf
  rw [← e1, hall T₀ hT₀, hall' T₀ hT₀]
  congr 1
  funext x
  exact hΦ x

theorem exists_level_ker : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, hU₁o, hU₁inf, hU₁⟩ := GlobalTheory.T.exists_open_fixing_negative_vacuum_definite_bottom hX t
  obtain ⟨U₂, hU₂o, hU₂inf, hU₂⟩ := dat_fix hX t
  obtain ⟨K, hK, hKU⟩ := level_of_open A (U₁ ⊓ U₂) (hU₁o.inter hU₂o) (le_inf hU₁inf hU₂inf)
  refine ⟨K, hK, fun P h k hk g => ?_⟩
  have hkf : k ∈ GfC A := (Lev.mem_levA.1 hk).1
  have hkU := hKU k hk
  have hv := hU₁ k hkU.1 hkf
  have hf := hU₂ k hkU.2 hkf hv
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hθ := hX.is.isVac.2.inf
  have hft : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac.1 hθ (hX.is.fst t) hX.is.isVac.2.theta
  have hκ : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact hkf)
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key : X.ω t (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P := by
    rw [← e1, GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW _ hθ _ hκ 1 (one_mem _) _ _ _ _ _ P hft, e1, hf]
  show X.ω t (g * k, h) _ 0 = X.ω t (g, h) _ 0
  have e : ((g * k, h) : GA D A × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.SrcLevel

end
