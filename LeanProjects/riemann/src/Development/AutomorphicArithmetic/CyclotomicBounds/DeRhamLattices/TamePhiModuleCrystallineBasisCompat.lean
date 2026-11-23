import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.tame_phiModule_crystalline_basis_compat :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T) (C : GlobalTheory.MemLoc.Core l) (ε : OCb l), IsEps ε → IsCrisCmp I jB →
    (∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z) →
    ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
    ∀ (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (j : ι),
    TWincl (dRO l O) T (jD (fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)))) =
      dRO l O (GlobalTheory.GalStep.ED K t ϖ) ^ α • TWincl (iotaO O C) T (jB (Pi.single j 1)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I jB jD C ε hε hB hD α hα hx j
  set c : ι → OA l O := fun i => ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩) with hc
  set E0 : OA l O := ϖ.iTot t K (fun _ => EIn l e (A O K)) with hE0
  have hED : GlobalTheory.GalStep.ED K t ϖ = toOD l O E0 :=
    PiSys.iD_ofA t K ϖ (fun _ => EIn l e (A O K))
  have h1 : inclV l O ι c = inclL t ϖ P (fun i => E0 ^ α * (Pi.single j 1 : ι → OA l O) i) := by
    funext i
    rw [inclL_apply]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero, map_zero, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
    change inclO l O (c i) = _
    rw [hc, hE0, ← map_pow]
    simp only [← ϖ.iW_of_mem t K, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    change E K l e ^ α * P.mx τ i j = P.mx τ i j * ((EIn l e (A O K) ^ α : A O K) : K⟦X⟧)
    rw [mul_comm, SubmonoidClass.coe_pow]
    rfl
  obtain ⟨-, β, -, hβ⟩ := P.exists_exponents
  obtain ⟨δ, hδ, hδ1⟩ := hε.2
  obtain ⟨-, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  obtain ⟨z, hz⟩ := hK2 (inclV l O ι c) ⟨c, rfl⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ α) with hm
  have hV : inclV l O ι (fun i => m * c i) = inclO l O m • inclV l O ι c := by
    funext i
    change inclO l O (m * c i) = inclO l O m * inclO l O (c i)
    rw [map_mul]
  have h3 := hD (fun i => m * c i) z (by rw [hV, hz])
  have h4 := hB (fun i => m * (E0 ^ α * (Pi.single j 1 : ι → OA l O) i)) z (by
    rw [inclL_smul_coord, ← h1, hz])
  have e3 : (fun i => toOD l O (m * c i)) = toOD l O m • fun i => toOD l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  have e4 : (fun i => toB l O (m * (E0 ^ α * (Pi.single j 1 : ι → OA l O) i))) =
      toB l O (m * E0 ^ α) • (Pi.single j 1 : ι → OB l O) := by
    funext i
    by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, mul_one, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.single_eq_of_ne h, mul_zero, map_zero, Pi.smul_apply, smul_eq_mul]
  rw [e3, map_smul] at h3
  rw [e4, map_smul] at h4
  have h5 : ∀ y : TW (OA l O) T, TWincl (dRO l O) T (TWincl (toOD l O) T y) =
      TWincl (iotaO O C) T (TWincl (toB l O) T y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s x =>
      simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, iotaO_toB]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h6 := h5 z
  rw [← h3, ← h4, BasisCoord.tWincl_smul', BasisCoord.tWincl_smul', iotaO_toB, map_mul, map_mul, mul_smul,
    map_pow, map_pow, ← hED] at h6
  have hν : IsUnit (ainfToBdRp l (muOf δ)) := by
    apply (GlobalTheory.MemLoc.thetaD_props l).2.2.1
    change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    intro h
    have h0 : Per.θ l (muOf δ) = 0 := Subtype.ext h
    rw [muOf, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_eq_zero] at h0
    exact hδ1 h0
  have hu : IsUnit (dRO l O (toOD l O m)) := by
    have h2 : toOD l O m = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ) ^ α) := by
      rw [hm, toOD, Algebra.TensorProduct.map_tmul, map_one, map_pow]
      rfl
    rw [h2]
    exact ((hν.pow α).map _).map _
  exact hu.smul_left_cancel.1 h6
