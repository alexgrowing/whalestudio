import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private noncomputable def gdR {l : ℕ} [Fact l.Prime] (g : GQ l) : Per.BdR l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := Per.σD g
  commutes' z := (GlobalTheory.MemLoc.FilLaws.σD_alg g (algebraMap ℤ_[l] (Per.BdRp l) z)).trans
    (congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) ((GlobalTheory.GalStep.galD g).commutes z))

private noncomputable def gOdR {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) :
    OdR l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (gdR g)

private theorem gOdR_dRO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OD l O) :
    gOdR O g (dRO l O x) = dRO l O (GlobalTheory.GalStep.galOD O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.MemLoc.FilLaws.σD_alg g w)
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem gOdR_iotaO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (g : GQ l) (x : OB l O) :
    gOdR O g (iotaO O C x) = iotaO O C (galOB O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.BKGal.FilStable.ι_σB C g w).symm
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem act_incl {O G Qp LL R R' : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (i : R →ₐ[O] R') (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (i r) = i (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWact f' T g (TWincl i T z) = TWincl i T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem _root_.UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (g : Gl l) (y : TW (OD l O) T) (b : TW (OB l O) T) (x : OD l O),
    TWincl (dRO l O) T y = dRO l O x • TWincl (iotaO O C) T b →
    TWincl (dRO l O) T (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g y) =
      dRO l O (GlobalTheory.GalStep.galOD O (sQ l g) x) • TWincl (iotaO O C) T (TWact (galOB O (sQ l g)) T g b) := by
  intro l _ O K _ _ _ _ _ _ _ T C g y b x h
  have h1 := act_incl (dRO l O) (GlobalTheory.GalStep.galOD O (sQ l g)) (gOdR O (sQ l g)) (gOdR_dRO O (sQ l g)) T g y
  have h2 := act_incl (iotaO O C) (galOB O (sQ l g)) (gOdR O (sQ l g)) (gOdR_iotaO O C (sQ l g)) T g b
  have h3 := GlobalTheory.GalStep.TWact_smul_of (gOdR O (sQ l g)) T g (dRO l O x) (TWincl (iotaO O C) T b)
  have h4 := gOdR_dRO O (sQ l g) x
  refine h1.symm.trans ((congrArg (TWact (gOdR O (sQ l g)) T g) h).trans (h3.trans ?_))
  rw [h4, h2]
