import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCrysBKFunctorOLOfBhattScholze
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLOfEPowSmulMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralConnectionTaylorFormulaTameBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModuleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersSubsetTameTypeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixesCrystallineImageDescentDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDescentDatumAndStableStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem exists_pack_isOfType : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), (∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ H) → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∃ Pk : Pack a ϖ η H T, Pk.D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) := by
  intro hBS hF l _ a e _ _ ϖ LL _ _ hl Pl AI hstd η H Sig U hU T hT
  obtain ⟨F⟩ := GlobalTheory.nonempty_crysBKFunctorOL_of_bhattScholze hBS l a e ϖ LL Pl AI hstd
  let B := F.obj (resF T (ϖ.field a)) hT.crys
  let I : Ident (thetaW a LL) ϖ B.P T := Ident.ofRes B.I
  have hBK : IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) :=
    B.isBK
  obtain ⟨C, hC, hTay⟩ := GlobalTheory.T.integralConnection_taylorFormula_tameBreuilKisin hBS l a e ϖ LL hl (Fin B.n) B.P T I hBK
  obtain ⟨⟨jB, hcmp⟩, -⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (Fin B.n) B.P T I
  have hhor := GlobalTheory.T.galois_fixes_crystalline_image_descentDatum l a e ϖ LL hl (Fin B.n) B.P T I jB hcmp C hC hTay
  obtain ⟨hst, hinf⟩ := GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed l a e ϖ LL (Fin B.n) B.P T I hBK
  have hK7 := GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule hBS l a e ϖ LL (Fin B.n) B.P T I hBK
  obtain ⟨⟨Δ, hΔ⟩, hLA⟩ := GlobalTheory.T.exists_galoisDescentDatum_and_stable l a e ϖ LL (Fin B.n) B.P T I hinf hK7
  obtain ⟨hEN, hjU⟩ := GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps hF l a e ϖ LL hl (Fin B.n) B.P T I jB Pl AI hstd hcmp hhor
  have hj : B.P.jumps ⊆ (U : Set ℤ) := hjU _ hT.jumps
  have hIcc : B.P.jumps ⊆ Set.Icc (-(η : ℤ)) H := fun i hi => hU i (hj hi)
  obtain ⟨hlow, hup⟩ := (GlobalTheory.BK.PhiMod.jumps_subset_Icc_iff _ _ l e a (Fin B.n) B.P η H).1 hIcc
  have hch := GlobalTheory.T.tameInertiaCharacters_subset_tameType l a e ϖ LL hl (Fin B.n) B.P T I jB Δ Pl AI hstd hcmp hhor hΔ Sig hT.type
  let D : BKDat ↥(OL LL) ↥LL.1 l e a (Fin B.n) η H :=
    { toPhiMod := B.P
      desc := Δ
      nabla_mem := fun m hm => hC ▸ C.mem_MM m hm
      EN_mem := hEN
      lower := hlow
      upper := hup }
  let R : GalDat (thetaW a LL) ϖ (sQ l) D T :=
    { I := I
      jB := jB
      cmp := hcmp
      desc := hΔ
      stable := hLA hst
      horiz := hhor }
  exact ⟨⟨B.n, D, R, hBK⟩, ⟨hch, hj⟩⟩

end GlobalTheory.BKGal
