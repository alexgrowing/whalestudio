import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiPole

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) :=
  GlobalTheory.MemLoc.ULaws.iota_aB C w

private theorem aB_alg (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) w) = Per.aB l w :=
  GlobalTheory.MemLoc.ULaws.iota_injective C (by rw [C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris, ι_aB])

private theorem toB_tmul (C : GlobalTheory.MemLoc.Core l) {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O)
    (w : Per.Ainf l) : toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w :=
  congrArg (fun y : Per.Bcris l => (o ⊗ₜ[ℤ_[l]] y : OB l O)) (aB_alg C w)

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem smul_TWincl_mem_filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {n : ℤ} {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l n) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ filT C T n := by
  unfold filT
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul C o w, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add, mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add, smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.XiPole

open GlobalTheory.BKGal.XiPole in

theorem GlobalTheory.BKGal.XiPole.jB_single_mem_filT : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R C i

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩

  obtain ⟨-, -, -, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε _ hEps hδl
  obtain ⟨z, hz⟩ := hK4 (inclL t ϖ D.toPhiMod (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
  rw [← inclL_smul_coord] at hz
  have hB := R.cmp _ z hz
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η) with hm
  have e1 : (fun j => toB l O (m * (Pi.single i (1 : OA l O) : ι → OA l O) j)) = toB l O m • (Pi.single i (1 : OB l O)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e1, map_smul] at hB
  have htm : toB l O m = (1 : O) ⊗ₜ[ℤ_[l]] Per.aB l (muOf ε ^ η) := toB_tmul C _ _

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [← aB_alg C]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  set d : Per.Bcris l := ((hμu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ η with hd
  have hdm : d * Per.aB l (muOf ε ^ η) = 1 := by
    rw [hd, map_pow, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  clear_value d
  have hjB : R.jB (Pi.single i 1) = ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z := by
    rw [← hB, smul_smul, htm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdm,
      ← Algebra.TensorProduct.one_def, one_smul]

  have hν : IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (GlobalTheory.MemLoc.TiedUnif.theta_piOne hE)
  obtain ⟨v', hv'⟩ := hν.exists_right_inv
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hUval : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hιμ : C.ι (Per.aB l (muOf ε)) = (U : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) := by
    rw [ι_aB, hUval, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ (GlobalTheory.MemLoc.TiedUnif.mu_eq ε))
  have h1 : C.ι d * (C.ι (Per.aB l (muOf ε))) ^ η = 1 := by
    rw [← map_pow, ← map_mul, ← map_pow, hdm, map_one]
  rw [hιμ] at h1
  have hpq : ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η = 1 := by
    rw [show ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) =
      ((U : Per.BdR l) * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε) * v') by
      rw [map_mul]; ring, Units.mul_inv, hv', map_one, one_mul, one_pow]
  have hU : ((U ^ (-(η : ℤ)) : (Per.BdR l)ˣ) : Per.BdR l) = ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ η := by
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hdF : C.ι d ∈ Per.FilD l (-(η : ℤ)) := by
    refine (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE _ _).2 ⟨v' ^ η, ?_⟩
    rw [← hUdef, hU, map_pow]
    calc C.ι d = C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η := by
          rw [hpq, mul_one]
      _ = (C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε))) ^ η) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v') ^ η := by
          rw [mul_pow _ _ η, mul_assoc]
      _ = _ := by rw [h1, one_mul, mul_pow]
  rw [hjB]
  exact smul_TWincl_mem_filT C T hdF z
