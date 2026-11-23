import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizerStatement
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCrystallineComparisonOfIsCrisCmp
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorDeRhamCrysRelationGaloisStable
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorInclDeRhamInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T)
    (ε : OCb l) (hε : IsEps ε) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz t ϖ (sQ l) P jB)
    (hjD : ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z)
    (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (v : OD l O)
    (hv : GlobalTheory.GalStep.galOD O (sQ l g) (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v) (d : P.D) :
    jD.symm (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g (jD (GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d)))) =
      v ^ α • GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have hd : P.xi d ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 (cst d)).2
    (GlobalTheory.GalStep.cst_mem_Mext P d)
  have h1 := UpperTheory.KN.phiMod_crystalline_comparison_of_isCrisCmp l a e O K t ϖ ι P T I jB jD C ε hε hCmp hjD α hα ⟨P.xi d, hd⟩
  have h2 := UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable l O K T C g _ _ (GlobalTheory.GalStep.ED K t ϖ ^ α) (h1.trans (by rw [map_pow]))
  have h3 : TWact (galOB O (sQ l g)) T g (jB (toBcris t ϖ P ⟨P.xi d, hd⟩)) =
      jB (toBcris t ϖ P ⟨P.xi d, hd⟩) := hHor g hg d hd
  rw [h3, map_pow, hv, mul_pow, mul_comm, map_mul, mul_smul, map_pow (dRO l O) (GlobalTheory.GalStep.ED K t ϖ), ← h1,
    ← BasisCoord.tWincl_smul'] at h2
  have h4 := UpperTheory.KN.latticeTensorIncl_deRham_injective l O K T h2
  rw [← jD.map_smul] at h4
  exact (congrArg jD.symm h4).trans (jD.symm_apply_apply _)

theorem _root_.GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ v : OD l ↥(OL LL), GlobalTheory.GalStep.galOD ↥(OL LL) (sQ l g) (GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ) = GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ * v → ∀ d : P.D, GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d)) = v ^ α • GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d) := by
  intro _ l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI _ hCmp hHor jD hjD α hα g hg v hv d
  obtain ⟨-, ε, -, hε, -⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  exact gen (thetaW a LL) ϖ P T I jB jD ε hε hCmp hHor hjD α hα g hg v hv d
