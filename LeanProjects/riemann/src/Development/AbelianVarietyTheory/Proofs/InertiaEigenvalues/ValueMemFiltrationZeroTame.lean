import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.ValueFil

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem toB_tmul_pt {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Per.Ainf l) :
    toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w := by
  rw [GlobalTheory.RingIface.aB_alg]
  rfl

theorem core_ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) := by
  rw [GlobalTheory.RingIface.aB_alg, C.ι_j, GlobalTheory.MemLoc.LogEx.algebraMap_acris, C.j_cris.on0, Subalgebra.coe_algebraMap]
  rfl

theorem one_mem_filZero : (1 : Per.BdR l) ∈ Per.FilD l 0 :=
  (GlobalTheory.MemLoc.filD_laws l).2.1

theorem alg_mem_filZero (u : Per.BdRp l) : algebraMap (Per.BdRp l) (Per.BdR l) u ∈ Per.FilD l 0 := by
  rw [← mul_one (algebraMap (Per.BdRp l) (Per.BdR l) u), ← Algebra.smul_def]
  exact Submodule.smul_mem _ u one_mem_filZero

theorem isUnit_aDp_of_theta {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    IsUnit (GlobalTheory.MemLoc.aDp l x) :=
  (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hx)

theorem ι_mem_filZero_of_mul (C : GlobalTheory.MemLoc.Core l) {d : Per.Bcris l} {x : Per.Ainf l} {n : ℕ}
    (hd : d * Per.aB l x ^ n = 1) (hx : IsUnit (GlobalTheory.MemLoc.aDp l x)) : C.ι d ∈ Per.FilD l 0 := by
  obtain ⟨v, hv⟩ := hx
  have h1 : C.ι d * algebraMap (Per.BdRp l) (Per.BdR l) ((v : Per.BdRp l) ^ n) = 1 := by
    rw [map_pow, hv, ← core_ι_aB, ← map_pow, ← map_mul, hd, map_one]
  have h2 : C.ι d = algebraMap (Per.BdRp l) (Per.BdR l) (((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
    calc C.ι d = C.ι d * algebraMap (Per.BdRp l) (Per.BdR l)
          ((v : Per.BdRp l) ^ n * ((v⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) ^ n) := by
          rw [← mul_pow, Units.mul_inv, one_pow, map_one, mul_one]
      _ = _ := by rw [map_mul, ← mul_assoc, h1, one_mul]
  rw [h2]
  exact alg_mem_filZero _

theorem theta_σA_ne_zero (g : Per.Gq l) {x : Per.Ainf l} (hx : (Per.θ l x : ℂ_[l]) ≠ 0) :
    (Per.θ l (Per.σA g x) : ℂ_[l]) ≠ 0 := by
  intro h
  apply hx
  have h' : Per.σC g (Per.θ l x : ℂ_[l]) = 0 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, ← (GlobalTheory.MemLoc.thetaD_props l).2.2.2.2,
      (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact h
  rw [← norm_eq_zero, ← GlobalTheory.RingBasics.norm_σC g, h', norm_zero]

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWact, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem TWact_TWincl (h : GQ l) (T : LocLat G ℚ_[l] K O) (g : G) (z : TW (OA l O) T) :
    TWact (galOB O h) T g (TWincl (toB l O) T z) = TWincl (toB l O) T (TWact (galOA O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c x =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    rw [toB, AlgHom.comp_apply, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem smul_TWincl_mem (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l 0) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ Submodule.span O {w : TW (OB l O) T |
      ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
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
        rw [toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, core_ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add, mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add, smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.ValueFil

open GlobalTheory.BKGal.ValueFil in

theorem GlobalTheory.BKGal.value_mem_filtration_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ (hy : y ∈ ME D.toPhiMod) (m₀ : ι → OW l O), phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩ → ∃ b₁, IsCrisVal t ϖ D.toPhiMod R.jB m₀ b₁ ∧ ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g b₁ - b₁ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hy m₀ h1

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
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ

  obtain ⟨hMA, -⟩ := GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
    ⟨y, hy⟩ hyY.1 m₀ h1
  obtain ⟨-, hK2, hK3, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hEps hδl
  obtain ⟨z, hz⟩ := hK2 _ hMA

  have hLA : ∀ (c : OA l O) {v : ι → OW l O}, v ∈ LA t ϖ D.toPhiMod → inclO l O c • v ∈ LA t ϖ D.toPhiMod := by
    rintro c _ ⟨d, rfl⟩
    exact ⟨fun i => c * d i, inclL_smul_coord t ϖ D.toPhiMod c d⟩
  have hT : ∀ z' : TW (OA l O) T, inclO l O (1 ⊗ₜ (muOf ε ^ H)) • R.I.j.symm (TWincl (inclO l O) T z') ∈
      LA t ϖ D.toPhiMod := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]; exact zero_mem _
    | tmul c x =>
      have e1 : TWincl (inclO l O) T (c ⊗ₜ[O] x) = inclO l O c • ((1 : OW l O) ⊗ₜ[O] x) := by
        rw [smul_tmul', smul_eq_mul, mul_one]; rfl
      rw [e1, map_smul, smul_comm]
      exact hLA c (hK3 x)
    | add c c' hc hc' => rw [map_add, map_add, smul_add]; exact add_mem hc hc'
  obtain ⟨cc, hcc⟩ := hT z
  rw [← hz, LinearEquiv.symm_apply_apply] at hcc

  have hB := R.cmp cc ((1 ⊗ₜ (muOf ε ^ H) : OA l O) • z) (by
    rw [hcc, map_smul, hz, TWincl_smul])
  rw [TWincl_smul] at hB

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [GlobalTheory.RingIface.aB_alg]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  have hνu : IsUnit (Per.aB l (muOf δ)) := by
    have e2 : Per.aB l (muOf ε) = Per.aB l (GlobalTheory.MemLoc.xi ε) * Per.aB l (muOf δ) := by
      rw [← map_mul]
      exact congrArg (Per.aB l) (GlobalTheory.MemLoc.TFil.mu_eq ε)
    rw [e2] at hμu
    exact isUnit_of_mul_isUnit_right hμu
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h
  set n := η + (H + η) with hn
  set d : Per.Bcris l := ((hνu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ n with hd
  have hdn : d * Per.aB l (muOf δ) ^ n = 1 := by
    rw [hd, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  have hm : ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))) : OA l O) =
      (1 ⊗ₜ (muOf ε ^ H)) * ((1 ⊗ₜ (muOf δ ^ η)) * (1 ⊗ₜ (muOf δ ^ (H + η)))) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  refine ⟨((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z,
    ⟨(1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η))), cc, ?_, ?_, ?_⟩, ?_⟩
  · have hu : IsUnit (Per.aB l (muOf ε ^ H * (muOf δ ^ η * muOf δ ^ (H + η)))) := by
      rw [map_mul, map_mul, map_pow, map_pow, map_pow]
      exact (hμu.pow H).mul ((hνu.pow _).mul (hνu.pow _))
    have := hu.map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    rw [toB_tmul_pt]
    exact this
  · rw [hcc, hm, map_mul, map_mul, mul_smul, mul_smul]
  · rw [hB, smul_smul]
    congr 1
    rw [toB_tmul_pt, toB_tmul_pt, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    have hdn' : d * Per.aB l (muOf δ) ^ (η + (H + η)) = 1 := hdn
    rw [map_mul, map_mul, map_pow, map_pow, map_pow]
    linear_combination (Per.aB l (muOf ε) ^ H) * hdn'
  · intro g _ C
    refine sub_mem ?_ (smul_TWincl_mem C T (ι_mem_filZero_of_mul C hdn (isUnit_aDp_of_theta hθν)) z)
    change TWact (galOB O (sQ l g)) T g (((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z) ∈ _
    rw [TWact_smul, TWact_TWincl]
    have hg : Per.σB (sQ l g) d * Per.aB l (Per.σA (sQ l g) (muOf δ)) ^ n = 1 := by
      rw [← (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.1, ← map_pow, ← map_mul, hdn, map_one]
    exact smul_TWincl_mem C T (ι_mem_filZero_of_mul C hg
      (isUnit_aDp_of_theta (theta_σA_ne_zero (sQ l g) hθν))) _
