import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.TamePhiModuleCrystallineBasisCompat
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModDeRhamImageCoordExpansion
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem twSmul {O R R' G Qp LL : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL]
    (f : R →ₐ[O] R') (T : LocLat G Qp LL O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWincl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

private theorem mxMem {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e]
    {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {α : ℕ} (hα : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M)
    (τ : ZMod a) (i j : ι) : E K l e ^ α * P.mx τ i j ∈ A O K := by
  let m : Vec K a ι := Pi.single τ (P.mx τ *ᵥ Pi.single j 1)
  have hm : m ∈ P.L := mem_tot.2 fun σ => by
    by_cases hσ : σ = τ
    · subst hσ
      simp only [m, Pi.single_eq_same]
      exact P.mem_extc.2 ⟨_, fun k => by
        rw [Pi.single_apply]; split_ifs
        exacts [one_mem _, zero_mem _], rfl⟩
    · simp only [m, Pi.single_eq_of_ne hσ]
      exact zero_mem _
  have := mem_tot.1 (hα m hm) τ i
  simpa [m] using this

theorem _root_.UpperTheory.KN.phiMod_crystalline_comparison_of_isCrisCmp :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T) (C : GlobalTheory.MemLoc.Core l) (ε : OCb l), IsEps ε → IsCrisCmp I jB →
    (∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z) →
    ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
    ∀ σ : P.MMl, TWincl (dRO l O) T (jD (GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1))) =
      dRO l O (GlobalTheory.GalStep.ED K t ϖ) ^ α • TWincl (iotaO O C) T (jB (toBcris t ϖ P σ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB jD C ε hε hB hD α hα σ
  have hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K := mxMem P hα
  have hσ : toBcris t ϖ P σ = ∑ j, ϖ.iB t K (coordL P (invL l (S O K e)) σ j) •
      (Pi.single j 1 : ι → OB l O) := by
    funext i
    rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [UpperTheory.KN.phiMod_deRham_image_coord_expansion l a e O K t ϖ ι P α hx σ, hσ, map_sum, map_sum, map_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [jD.map_smul, jB.map_smul, twSmul, twSmul,
    UpperTheory.KN.tame_phiModule_crystalline_basis_compat l a e O K t ϖ ι P T I jB jD C ε hε hB hD α hα hx j,
    UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C, smul_smul, smul_smul, mul_comm]
