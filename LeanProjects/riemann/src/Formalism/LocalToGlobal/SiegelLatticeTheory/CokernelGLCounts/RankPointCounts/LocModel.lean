import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LocalModelsSplitCofinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.BasisEApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.DenEqOneOfForallPadicNormLeOne
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalOrbitGerms
import Formalism.DoubleCosetMeasures.LatticeCoset

noncomputable section

namespace Formalism.L2.SG.Pf.LocModel.LM.DeltaA

open ValuativeRel

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra ℚ_[ℓ] K] [FiniteDimensional ℚ_[ℓ] K]
  [Algebra ℤ_[ℓ] K] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] K]

theorem oint_isIntegral (hc : Continuous (algebraMap ℚ_[ℓ] K)) {t : K} (ht : t ∈ 𝒪[K]) :
    IsIntegral ℤ_[ℓ] t := by
  have : T2Space K := IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => by
    refine ⟨{y | valuation K y < valuation K x}, ?_, fun h => lt_irrefl (valuation K x) h⟩
    rw [IsValuativeTopology.mem_nhds_zero_iff]
    exact ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).mpr hx), fun y hy => hy⟩
  have : ContinuousSMul ℚ_[ℓ] K := continuousSMul_of_algebraMap _ _ hc
  let b := Module.finBasis ℚ_[ℓ] K
  have hf : Continuous (b.equivFun.toLinearMap) := LinearMap.continuous_of_finiteDimensional _
  have hcpt : IsCompact {x : K | valuation K x ≤ 1} := IsNonarchimedeanLocalField.isCompact_closedBall K 1
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C (by exact_mod_cast hℓ.out.one_lt : (1 : ℝ) < ℓ)
  let M : Submodule ℤ_[ℓ] K := Submodule.span ℤ_[ℓ] (Set.range fun i => (((ℓ : ℚ_[ℓ]) ^ N)⁻¹) • b i)
  have hOM : ∀ x : K, valuation K x ≤ 1 → x ∈ M := by
    intro x hx
    have hb := hC x hx
    rw [← b.sum_equivFun x]
    refine Submodule.sum_mem _ fun i _ => ?_
    set c := b.equivFun x i with hcdef
    have hci : ‖c‖ ≤ C := (norm_le_pi_norm (b.equivFun x) i).trans hb
    have hz : ‖(ℓ : ℚ_[ℓ]) ^ N * c‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p]
      have hl0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ.out.pos
      rw [inv_pow]
      rw [inv_mul_le_iff₀ (pow_pos hl0 N), mul_one]
      exact hci.trans hN.le
    let z : ℤ_[ℓ] := ⟨(ℓ : ℚ_[ℓ]) ^ N * c, hz⟩
    have hne : ((ℓ : ℚ_[ℓ]) ^ N) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
    have : c • b i = z • ((((ℓ : ℚ_[ℓ]) ^ N)⁻¹) • b i) := by
      rw [← smul_assoc]
      congr 1
      show c = ((z : ℚ_[ℓ]) • ((ℓ : ℚ_[ℓ]) ^ N)⁻¹)
      simp only [smul_eq_mul, z]
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ_[ℓ] {t}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro y hy
    rw [Submonoid.closure_singleton_eq] at hy
    obtain ⟨n, rfl⟩ := hy
    simp only [powersHom_apply]
    exact hOM _ (by
      have := pow_mem ht n
      exact this)
  have := isNoetherian_of_fg_of_noetherian M hfg
  have hfg2 : (Subalgebra.toSubmodule (Algebra.adjoin ℤ_[ℓ] {t})).FG := by
    have h := (IsNoetherian.noetherian
      (Submodule.comap M.subtype (Subalgebra.toSubmodule (Algebra.adjoin ℤ_[ℓ] {t})))).map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h
  exact IsIntegral.of_mem_of_fg _ hfg2 t (Algebra.subset_adjoin rfl)

end Formalism.L2.SG.Pf.LocModel.LM.DeltaA

namespace Formalism.L2.SG.Pf.LocModel.LM.DeltaB

open Polynomial

variable {R K A : Type} [CommRing R] [Field K] [CommRing A] [Algebra R K] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A]

theorem trace_isIntegral_rank2 (b : Module.Basis (Fin 2) K A) {y : A} (hy : IsIntegral R y) :
    IsIntegral R (Algebra.trace K A y) := by
  classical
  have : Module.Finite K A := Module.Finite.of_basis b
  have : Nontrivial A := nontrivial_of_ne (b 0) 0 (b.linearIndependent.ne_zero 0)
  by_cases hr : y ∈ (algebraMap K A).range
  · obtain ⟨c, rfl⟩ := hr
    have hc : IsIntegral R c :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K A) (algebraMap K A).injective).mp hy
    rw [Algebra.trace_algebraMap, Module.finrank_eq_card_basis b]
    simpa [two_smul] using hc.add hc
  · set χ := (Algebra.leftMulMatrix b y).charpoly with hχdef
    have hχy : aeval y χ = 0 := by
      apply Algebra.leftMulMatrix_injective b
      rw [← Polynomial.aeval_algHom_apply, map_zero]
      exact Matrix.aeval_self_charpoly _
    have hmon : χ.Monic := Matrix.charpoly_monic _
    have hdeg : χ.natDegree = 2 := by simp [χ, Matrix.charpoly_natDegree_eq_dim]
    have hyK : IsIntegral K y := Algebra.IsIntegral.isIntegral y
    have hmin : χ = minpoly K y := by
      refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyK) hmon (minpoly.dvd K y hχy) ?_
      rw [hdeg]
      have h1 := minpoly.natDegree_pos hyK
      have h2 : (minpoly K y).natDegree ≠ 1 := fun h => hr (minpoly.natDegree_eq_one_iff.mp h)
      omega
    obtain ⟨f, hfm, hf⟩ := hy
    have hdvd : χ ∣ f.map (algebraMap R K) := by
      rw [hmin]
      refine minpoly.dvd K y ?_
      rw [aeval_map_algebraMap, aeval_def]
      exact hf
    let Kb := AlgebraicClosure K
    set χ' := χ.map (algebraMap K Kb) with hχ'
    have hs : χ'.Splits := IsAlgClosed.splits _
    have hroots : ∀ r ∈ χ'.roots, IsIntegral R r := by
      intro r hr'
      refine ⟨f, hfm, ?_⟩
      have h1 : χ'.IsRoot r := (mem_roots (hmon.map _).ne_zero).mp hr'
      obtain ⟨g, hg⟩ := hdvd
      have h2 : (f.map (algebraMap R Kb)).eval r = 0 := by
        rw [IsScalarTower.algebraMap_eq R K Kb, ← Polynomial.map_map, hg, Polynomial.map_mul, eval_mul]
        rw [show (χ.map (algebraMap K Kb)).eval r = 0 from h1, zero_mul]
      rwa [eval_map] at h2
    have hsum : IsIntegral R χ'.roots.sum := by
      have : χ'.roots.sum ∈ integralClosure R Kb :=
        multiset_sum_mem _ fun r hr' => (mem_integralClosure_iff R Kb).mpr (hroots r hr')
      exact (mem_integralClosure_iff R Kb).mp this
    have htr : algebraMap K Kb (Algebra.trace K A y) = χ'.roots.sum := by
      rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_eq_neg_charpoly_nextCoeff, map_neg,
        ← Polynomial.nextCoeff_map (algebraMap K Kb).injective, ← hχdef,
        hs.nextCoeff_eq_neg_sum_roots_of_monic (hmon.map _), neg_neg]
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K Kb) (algebraMap K Kb).injective).mp ?_
    rw [IsScalarTower.coe_toAlgHom', htr]
    exact hsum

end Formalism.L2.SG.Pf.LocModel.LM.DeltaB

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DeltaUnitCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def IotaIntCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (x : D.host.E), ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιE x ∈ (D.s.atP p).O

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM.DeltaC

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem norm_le_one_of_isIntegral_zl {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ_[ℓ] t) :
    ‖t‖ ≤ 1 := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht
  first
  | exact PadicInt.norm_le_one y
  | simpa using PadicInt.norm_le_one y

theorem mem_of_isIntegral_fp (L : LocAt F E sig p) {s : L.Fp} (hs : IsIntegral 𝒪[L.Fp] s) : s ∈ 𝒪[L.Fp] := by
  have hv := Valuation.integer.integers (ValuativeRel.valuation L.Fp)
  first
  | exact hv.mem_of_integral hs
  | (obtain ⟨t, rfl⟩ := hv.mem_of_integral hs; exact t.2)

theorem isIntegral_zl (L : LocAt F E sig p) {s : L.Fp} (hs : s ∈ 𝒪[L.Fp]) :
    haveI := L.ellPrime
    letI := ((algebraMap ℚ_[resChar p] L.Fp).comp (algebraMap ℤ_[resChar p] ℚ_[resChar p])).toAlgebra
    IsIntegral ℤ_[resChar p] s := by
  haveI := L.ellPrime
  letI := ((algebraMap ℚ_[resChar p] L.Fp).comp (algebraMap ℤ_[resChar p] ℚ_[resChar p])).toAlgebra
  haveI : IsScalarTower ℤ_[resChar p] ℚ_[resChar p] L.Fp := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := L.lf
  haveI := L.qlFin
  exact DeltaA.oint_isIntegral L.qlCont hs

theorem trace_mem (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : Algebra.trace L.Fp L.Ep y ∈ 𝒪[L.Fp] := by
  haveI := L.free
  haveI : Module.Finite L.Fp L.Ep := by
    first
    | exact Module.finite_of_finrank_eq_succ L.rank
    | exact Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
    | exact FiniteDimensional.of_finrank_pos (by rw [L.rank]; norm_num)
  have b := Module.finBasisOfFinrankEq L.Fp L.Ep L.rank
  rw [L.O_def] at hy
  exact mem_of_isIntegral_fp L (DeltaB.trace_isIntegral_rank2 b hy)

theorem psiE_O (L : LocAt F E sig p) {y : L.Ep} (hy : y ∈ L.O) : L.psiE y = 1 := by
  haveI := L.ellPrime
  obtain ⟨a, ⟨n, hn⟩, hTa, he⟩ := L.psiE_def y
  rw [he]
  refine PI.ProdFormulaE.Frac.exp_two_pi_of_den_eq_one (PI.ProdFormulaE.Frac.den_eq_one_of_norm_le_one hn ?_ hTa)
  rw [PI.ProdFormulaE.Base.trace_tower L y]
  letI := ((algebraMap ℚ_[resChar p] L.Fp).comp (algebraMap ℤ_[resChar p] ℚ_[resChar p])).toAlgebra
  haveI : IsScalarTower ℤ_[resChar p] ℚ_[resChar p] L.Fp := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := L.qlFin
  exact norm_le_one_of_isIntegral_zl (Algebra.isIntegral_trace (isIntegral_zl L (trace_mem L hy)))

end Formalism.L2.SG.Pf.LocModel.LM.DeltaC

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DiffTrivCof : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ᶠ p in Filter.cofinite, ∀ z : (D.s.atP p).Ep,
      (∀ y ∈ (D.s.atP p).O, (D.s.atP p).psiE (z * y) = 1) → z ∈ (D.s.atP p).O

theorem mem_of_alg_mem {D : Formalism.BasicNotions.D7} {p : PlF D} {a : (D.s.atP p).Fp}
    (h : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep a ∈ (D.s.atP p).O) : a ∈ 𝒪[(D.s.atP p).Fp] := by
  rw [(D.s.atP p).O_def] at h
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hinj : Function.Injective
      (IsScalarTower.toAlgHom 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep) :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective
  have hi : IsIntegral 𝒪[(D.s.atP p).Fp] a := (isIntegral_algHom_iff _ hinj).1 h
  exact DeltaC.mem_of_isIntegral_fp (D.s.atP p) hi

theorem delta_mem {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : Agree δ M p) :
    δ p ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨_, hδ0, _, hO, hpsi, _⟩ := hA
  apply mem_of_alg_mem
  have key := ((M p).L.additive_character_dual_ring (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p))).1
  rw [hO] at key
  apply key
  intro y hy
  rw [hpsi]
  have e : -(algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * y *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) = -y := by
    rw [mul_comm (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)) y, mul_assoc, ← map_mul,
      mul_inv_cancel₀ hδ0, map_one, mul_one]
  rw [e]
  exact DeltaC.psiE_O (D.s.atP p) (neg_mem hy)

theorem delta_inv_mem {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : Agree δ M p)
    (hD : ∀ z : (D.s.atP p).Ep, (∀ y ∈ (D.s.atP p).O, (D.s.atP p).psiE (z * y) = 1) → z ∈ (D.s.atP p).O) :
    (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨_, hδ0, _, hO, hpsi, _⟩ := hA
  apply mem_of_alg_mem
  apply hD
  intro y hy
  have h1 : (1 : (D.s.atP p).Ep) ∈ (M p).L.O := one_mem _
  have htriv := ((M p).L.additive_character_dual_ring 1).2 h1
  have h2 := htriv (-y) (by rw [hO]; exact neg_mem hy)
  rw [one_mul, hpsi] at h2
  convert h2 using 2
  ring

theorem deltaUnitCof_of (h : DiffTrivCof) : DeltaUnitCof := by
  intro D δ M hA
  filter_upwards [h D δ M hA] with p hp
  exact ⟨delta_mem (hA p), delta_inv_mem (hA p) hp⟩

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EpDualCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite, ∀ z : (D.s.atP p).Ep,
    (∀ y ∈ (D.s.atP p).O, Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (z * y) ∈ 𝒪[(D.s.atP p).Fp]) →
      z ∈ (D.s.atP p).O

def FpUnifCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite, ∀ x : (D.s.atP p).Fp, x ∉ 𝒪[(D.s.atP p).Fp] →
    (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) * x)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def FpDegCof : Prop :=
  ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite,
    haveI := (D.s.atP p).ellPrime
    ¬ (Loc.resChar p ∣ Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp)

theorem diffTrivCof_of (h1 : EpDualCof) (h2 : FpUnifCof) (h3 : FpDegCof) : DiffTrivCof := by
  intro D δ M _
  filter_upwards [h1 D, h2 D, h3 D] with p hE hU hG
  intro z hz
  by_contra hzO
  haveI := (D.s.atP p).ellPrime
  obtain ⟨y, hyO, hs⟩ : ∃ y ∈ (D.s.atP p).O,
      Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (z * y) ∉ 𝒪[(D.s.atP p).Fp] := by
    by_contra h
    push Not at h
    exact hzO (hE z h)
  set s := Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (z * y) with hsdef
  have hs0 : s ≠ 0 := fun h => hs (h ▸ zero_mem _)
  have hc := hU s hs
  set c := (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) * s)⁻¹ with hcdef
  have hcO : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
    rw [(D.s.atP p).O_def]
    have h := isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := ⟨c, hc⟩)
    rw [IsScalarTower.algebraMap_apply 𝒪[(D.s.atP p).Fp] (D.s.atP p).Fp (D.s.atP p).Ep] at h
    exact h
  have hps := hz _ (mul_mem hcO hyO)
  obtain ⟨a, -, hTa, he⟩ := (D.s.atP p).psiE_def (z * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y))
  rw [hps, eq_comm, Complex.exp_eq_one_iff] at he
  obtain ⟨k, hk⟩ := he
  have hak : a = k := by
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (a : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ h2pi
      rw [hk]; ring
    exact_mod_cast this
  rw [hak, PI.ProdFormulaE.Base.trace_tower (D.s.atP p)] at hTa
  have htr : Algebra.trace (D.s.atP p).Fp (D.s.atP p).Ep (z * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y))
      = algebraMap ℚ_[Loc.resChar p] (D.s.atP p).Fp ((Loc.resChar p : ℚ_[Loc.resChar p])⁻¹) := by
    rw [show z * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c * y) = c • (z * y) by
      rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul, ← hsdef, hcdef, mul_inv, mul_assoc,
      inv_mul_cancel₀ hs0, mul_one, map_inv₀, map_natCast]
  rw [htr, Algebra.trace_algebraMap] at hTa
  have hl : ‖(Loc.resChar p : ℚ_[Loc.resChar p])‖ < 1 := by
    rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : (Loc.resChar p).Prime).one_lt)
  have hn : ‖((Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp : ℕ) : ℚ_[Loc.resChar p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hG)
  have hk1 : ‖(((k : ℚ) : ℚ_[Loc.resChar p]))‖ ≤ 1 := by
    rw [Rat.cast_intCast]; exact Padic.norm_int_le_one k
  have hbig : ‖Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp • (Loc.resChar p : ℚ_[Loc.resChar p])⁻¹‖ ≤ 1 := by
    rw [← sub_add_cancel (Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp • (Loc.resChar p : ℚ_[Loc.resChar p])⁻¹)
      (((k : ℚ) : ℚ_[Loc.resChar p]))]
    exact (Padic.nonarchimedean _ _).trans (max_le hTa hk1)
  rw [nsmul_eq_mul, norm_mul, hn, one_mul, norm_inv] at hbig
  have hpos : 0 < ‖(Loc.resChar p : ℚ_[Loc.resChar p])‖ := by
    rw [Padic.norm_p]; exact inv_pos.mpr (by exact_mod_cast (Fact.out : (Loc.resChar p).Prime).pos)
  have := (one_lt_inv₀ hpos).mpr hl
  linarith

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem memO_iff {K : Type} [Field K] [ValuativeRel K] (x : K) : x ∈ 𝒪[K] ↔ x ≤ᵥ 1 := by
  simp only [Valuation.mem_integer_iff]
  first
  | rw [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K), map_one]
  | rw [Valuation.Compatible.rel_iff_le (v := ValuativeRel.valuation K), map_one]
  | exact ((Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K) x 1).trans (by rw [map_one])).symm
  | simp [Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation K)]
  | exact ValuativeRel.valuation_le_one_iff.symm

theorem iotaF_mem_cof (D : Formalism.BasicNotions.D7) (x : D.host.F) :
    ∀ᶠ p in Filter.cofinite, (D.s.atP p).ιF x ∈ 𝒪[(D.s.atP p).Fp] := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.F) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hb0
  have hfin := Ideal.finite_factors hI
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  have hbp : b ∉ p.asIdeal := by
    intro h
    apply hp
    show p.asIdeal ∣ Ideal.span {b}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  have hvb : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F b) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    first
    | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff (v := p)).2 hbp
    | (apply le_antisymm (p.intValuation_le_one _)
       rw [← not_lt, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
       exact hbp)
    | (apply le_antisymm (p.intValuation_le_one _)
       rw [← not_lt, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd,
         Ideal.dvd_span_singleton]
       exact hbp)
  have hva : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F a) ≤ 1 := by
    first
    | exact p.valuation_le_one a
    | exact p.valuation_le_one (K := D.host.F) a
  rw [memO_iff, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one, map_div₀, hvb, div_one]
  exact hva

theorem vec_mem_of {K : Type} [Field K] (R : Subring K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : ∀ i j, M i j ∈ R) (hd : M.det ≠ 0) (hdi : (M.det)⁻¹ ∈ R) (c : ι → K)
    (hc : ∀ j, Matrix.vecMul c M j ∈ R) : ∀ i, c i ∈ R := by
  intro i
  have hinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hd)
  have hcv : c = Matrix.vecMul (Matrix.vecMul c M) M⁻¹ := by
    rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  let M' : Matrix ι ι R := fun a b => ⟨M a b, hM a b⟩
  have hadj : ∀ a b, M.adjugate a b ∈ R := by
    intro a b
    have e : M = R.subtype.mapMatrix M' := by ext a b; rfl
    rw [e, ← RingHom.map_adjugate]
    exact (M'.adjugate a b).2
  have hinvR : ∀ a b, M⁻¹ a b ∈ R := by
    intro a b
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
    exact R.mul_mem hdi (hadj a b)
  rw [hcv]
  exact R.sum_mem fun j _ => R.mul_mem (hc j) (hinvR j i)

theorem iotaE_mem_of_int (D : Formalism.BasicNotions.D7) (p : PlF D) {w : D.host.E} (hw : IsIntegral ℤ w) :
    (D.s.atP p).ιE w ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  exact (hw.map (D.s.atP p).ιE.toIntAlgHom).tower_top

theorem alg_mem_O (D : Formalism.BasicNotions.D7) (p : PlF D) {c : (D.s.atP p).Fp} (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  first
  | exact isIntegral_algebraMap (x := (⟨c, hc⟩ : 𝒪[(D.s.atP p).Fp]))
  | exact (isIntegral_algebraMap (x := (⟨c, hc⟩ : 𝒪[(D.s.atP p).Fp])) : _)

theorem exists_theta (D : Formalism.BasicNotions.D7) :
    ∃ θ : D.host.E, IsIntegral ℤ θ ∧ θ ∉ (algebraMap D.host.F D.host.E).range := by
  have h2 := D.sp.cm.deg2
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, x ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra hall
    push Not at hall
    have hbt : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      rw [eq_top_iff]; intro x _; exact Algebra.mem_bot.mpr (hall x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbt
    omega
  have hxa : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨n, hn, hint⟩ := hxa.exists_integral_multiple
  refine ⟨n • x, hint, fun ⟨a, ha⟩ => hx ⟨(n : D.host.F)⁻¹ * a, ?_⟩⟩
  have hnE : (n : D.host.E) ≠ 0 := by exact_mod_cast hn
  rw [map_mul, ha, map_inv₀, map_intCast, zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]

theorem epsilonDual_almost_all : EpDualCof := by
  intro D
  have h2 := D.sp.cm.deg2
  obtain ⟨θ, hθi, hθ⟩ := exists_theta D
  have hli : LinearIndependent D.host.F ![(1 : D.host.E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have htE : algebraMap D.host.F D.host.E t ≠ 0 := (map_ne_zero _).mpr ht
      apply hθ
      refine ⟨-(s / t), ?_⟩
      rw [map_neg, map_div₀, neg_eq_iff_eq_neg, div_eq_iff htE]
      linear_combination hst
  let bF : Module.Basis (Fin 2) D.host.F D.host.E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hbF : ∀ i, bF i = ![(1 : D.host.E), θ] i := fun i => by
    simp [bF, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hbint : ∀ i, IsIntegral ℤ (bF i) := by
    intro i; rw [hbF]; fin_cases i
    · exact isIntegral_one
    · exact hθi
  set Tm := Algebra.traceMatrix D.host.F bF with hTm
  have hdet : Tm.det ≠ 0 := by
    have := Algebra.discr_not_zero_of_basis D.host.F bF
    rwa [Algebra.discr_def] at this
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => iotaF_mem_cof D (Tm i j),
    iotaF_mem_cof D (Tm.det)⁻¹] with p hT hdi
  intro z hz
  let bE := PI.ProdFormulaE.Base.basisE (D.s.atP p) bF h2
  have hbE : ∀ i, bE i = (D.s.atP p).ιE (bF i) := fun i => PI.ProdFormulaE.Base.basisE_apply (D.s.atP p) bF h2 i
  let M : Matrix (Fin 2) (Fin 2) (D.s.atP p).Fp := (D.s.atP p).ιF.mapMatrix Tm
  have hMdet : M.det = (D.s.atP p).ιF Tm.det := (RingHom.map_det (D.s.atP p).ιF Tm).symm
  have hc : ∀ j, Matrix.vecMul (bE.repr z) M j ∈ 𝒪[(D.s.atP p).Fp] := by
    intro j
    have h := hz ((D.s.atP p).ιE (bF j)) (iotaE_mem_of_int D p (hbint j))
    rw [← bE.sum_repr z, Finset.sum_mul, map_sum] at h
    convert h using 1
    simp only [Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, hbE, ← map_mul, PI.ProdFormulaE.Base.trace_ιE (D.s.atP p) h2]
    simp [M, hTm, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hcO := vec_mem_of 𝒪[(D.s.atP p).Fp] M (fun i j => hT i j) (by rw [hMdet]; exact (map_ne_zero _).mpr hdet)
    (by rw [hMdet, ← map_inv₀]; exact hdi) _ hc
  rw [← bE.sum_repr z]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def, hbE]
  exact Subring.mul_mem _ (alg_mem_O D p (hcO i)) (iotaE_mem_of_int D p (hbint i))

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem t2Space_of_nonarchimedeanLocalField' (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    T2Space K :=
  IsTopologicalAddGroup.t2Space_of_zero_sep fun x hx => by
    refine ⟨{y | valuation K y < valuation K x}, ?_, fun h => lt_irrefl (valuation K x) h⟩
    rw [IsValuativeTopology.mem_nhds_zero_iff]
    exact ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).mpr hx), fun y hy => hy⟩

theorem finrank_fp_le (D : Formalism.BasicNotions.D7) (p : PlF D) :
    haveI := (D.s.atP p).ellPrime
    Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp ≤ Module.finrank ℚ D.host.F := by
  haveI := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).qlFin
  haveI := t2Space_of_nonarchimedeanLocalField' (D.s.atP p).Fp
  haveI : ContinuousSMul ℚ_[Loc.resChar p] (D.s.atP p).Fp :=
    continuousSMul_of_algebraMap _ _ (D.s.atP p).qlCont
  let b := Module.finBasis ℚ D.host.F
  let S : Submodule ℚ_[Loc.resChar p] (D.s.atP p).Fp :=
    Submodule.span ℚ_[Loc.resChar p] (Set.range fun i => (D.s.atP p).ιF (b i))
  have hsub : Set.range (D.s.atP p).ιF ⊆ (S : Set (D.s.atP p).Fp) := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (D.s.atP p).ιF (b.repr x i • b i) =
        ((b.repr x i : ℚ) : ℚ_[Loc.resChar p]) • (D.s.atP p).ιF (b i) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcl : IsClosed (S : Set (D.s.atP p).Fp) := Submodule.closed_of_finiteDimensional S
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hd : Dense (S : Set (D.s.atP p).Fp) := (D.s.atP p).dense.mono hsub
    have : x ∈ closure (S : Set (D.s.atP p).Fp) := hd x
    rwa [hcl.closure_eq] at this
  calc Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp
      = Module.finrank ℚ_[Loc.resChar p] (⊤ : Submodule ℚ_[Loc.resChar p] (D.s.atP p).Fp) := (finrank_top ℚ_[Loc.resChar p] (D.s.atP p).Fp).symm
    _ = Module.finrank ℚ_[Loc.resChar p] S := by rw [htop]
    _ ≤ Fintype.card (Fin (Module.finrank ℚ D.host.F)) := finrank_range_le_card _
    _ = Module.finrank ℚ D.host.F := Fintype.card_fin _

theorem residueDegree_almost_all : FpDegCof := by
  intro D
  set d := Module.finrank ℚ D.host.F
  have hfin : {p : PlF D | Loc.resChar p ≤ d}.Finite := by
    have : {p : PlF D | Loc.resChar p ≤ d} = ⋃ ℓ ∈ Finset.range (d + 1), {p | Loc.resChar p = ℓ} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
      exact ⟨fun h => ⟨_, by omega, rfl⟩, fun ⟨ℓ, h1, h2⟩ => by omega⟩
    rw [this]
    exact Set.Finite.biUnion (Finset.finite_toSet _) fun ℓ _ => PI.UnitaryGroupMassFormula.CntFormula.resChar_finite D ℓ
  rw [Filter.eventually_cofinite]
  refine hfin.subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  by_contra hlt
  push Not at hlt
  apply hp
  haveI := (D.s.atP p).ellPrime
  haveI := (D.s.atP p).lf
  haveI := (D.s.atP p).qlFin
  intro hdvd
  have hpos : 0 < Module.finrank ℚ_[Loc.resChar p] (D.s.atP p).Fp := Module.finrank_pos
  have := Nat.le_of_dvd hpos hdvd
  have := finrank_fp_le D p
  omega

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

theorem withZero_exp_lt_one {a : WithZero (Multiplicative ℤ)} (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le'
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem withZero_exp_gt_neg_two {a : WithZero (Multiplicative ℤ)} (h : WithZero.exp (-2 : ℤ) < a) :
    WithZero.exp (-1 : ℤ) ≤ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact absurd h not_lt_zero'
  · rw [← WithZero.exp_log ha] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem unif_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Loc.LocAt F E sig p) (y₀ : F)
    (hunif : ∀ y : F, p.valuation F y < 1 → p.valuation F y ≤ p.valuation F y₀) :
    ∀ x : A.Fp, x ∉ 𝒪[A.Fp] → (A.ιF y₀ * x)⁻¹ ∈ 𝒪[A.Fp] := by
  have := A.lf
  have key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← Valuation.vle_iff_le]; exact A.val x y
  have keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1 := fun x => by
    have h := key 1 x
    rw [map_one, map_one, map_one] at h
    rw [← not_le, ← not_le, h]
  intro x hx
  have hv : 1 < valuation A.Fp x := by
    rw [Valuation.mem_integer_iff, not_le] at hx
    exact hx
  have hx0 : valuation A.Fp x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hv)
  have hw0 : valuation A.Fp x⁻¹ ≠ 0 := by rw [map_inv₀]; exact inv_ne_zero hx0
  have hw1 : valuation A.Fp x⁻¹ < 1 := by
    rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hv
  have hS : {w : A.Fp | valuation A.Fp (w - x⁻¹) < valuation A.Fp x⁻¹} ∈ nhds (x⁻¹ : A.Fp) :=
    (IsValuativeTopology.hasBasis_nhds' (x⁻¹ : A.Fp)).mem_of_mem hw0
  obtain ⟨w, ⟨y, rfl⟩, hw⟩ := A.dense.inter_nhds_nonempty hS
  have hw' : valuation A.Fp (A.ιF y - x⁻¹) < valuation A.Fp x⁻¹ := hw
  have heq : valuation A.Fp (A.ιF y) = valuation A.Fp x⁻¹ := Valuation.map_eq_of_sub_lt _ hw'
  have hy1 : p.valuation F y < 1 := (keylt1 y).1 (heq ▸ hw1)
  have hle : valuation A.Fp x⁻¹ ≤ valuation A.Fp (A.ιF y₀) := by
    rw [← heq]; exact (key y y₀).2 (hunif y hy1)
  rw [Valuation.mem_integer_iff, map_inv₀, map_mul]
  have hpos : 0 < valuation A.Fp (A.ιF y₀) * valuation A.Fp x := by
    refine mul_pos ?_ (zero_lt_iff.2 hx0)
    exact lt_of_lt_of_le (zero_lt_iff.2 hw0) hle
  rw [inv_le_one₀ hpos]
  rw [map_inv₀] at hle
  calc (1 : _) = (valuation A.Fp x)⁻¹ * valuation A.Fp x := (inv_mul_cancel₀ hx0).symm
    _ ≤ valuation A.Fp (A.ιF y₀) * valuation A.Fp x := by gcongr

theorem ramSq_finite (F : Type) [Field F] [NumberField F] :
    {p : HeightOneSpectrum (𝓞 F) | ((Loc.resChar p : ℕ) : 𝓞 F) ∈ p.asIdeal ^ 2 ∧
      (Loc.resChar p).Prime}.Finite := by
  refine (Ideal.finite_factors (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot).subset ?_
  intro p ⟨hp, hpr⟩
  simp only [Set.mem_ofPred_eq]
  have hmax : (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hpr).irreducible
  have hne : Ideal.span {((Loc.resChar p : ℕ) : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hpr.ne_zero
  have hdvd : p.asIdeal ^ 2 ∣ (Ideal.span {((Loc.resChar p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 F)) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.dvd_span_singleton]
    simpa using hp
  have := pow_sub_one_dvd_differentIdeal (A := ℤ) (B := 𝓞 F) p.asIdeal 2 hne hdvd
  simpa using this

theorem fpUnif_cof : ∀ D : Formalism.BasicNotions.D7, ∀ᶠ p in Filter.cofinite, ∀ x : (D.s.atP p).Fp, x ∉ 𝒪[(D.s.atP p).Fp] →
    (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) * x)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  intro D
  rw [Filter.eventually_cofinite]
  refine (ramSq_finite D.host.F).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  have hpr : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
  refine ⟨?_, hpr⟩
  by_contra hsq
  apply hp
  have hmem : ((Loc.resChar p : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h0 : ((Loc.resChar p : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := ringChar.Nat.cast_ringChar
    rwa [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem] at h0
  have hvℓ : p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) =
      p.intValuation ((Loc.resChar p : ℕ) : 𝓞 D.host.F) := by
    have h := p.valuation_of_algebraMap (K := D.host.F) ((Loc.resChar p : ℕ) : 𝓞 D.host.F)
    rw [← h]
    congr 1
  have hlo : WithZero.exp (-2 : ℤ) < p.intValuation ((Loc.resChar p : ℕ) : 𝓞 D.host.F) := by
    rw [← not_le]
    intro h
    exact hsq ((p.intValuation_le_pow_iff_mem _ 2).1 (by exact_mod_cast h))
  have hunif : ∀ y : D.host.F, p.valuation D.host.F y < 1 →
      p.valuation D.host.F y ≤ p.valuation D.host.F ((Loc.resChar p : ℕ) : D.host.F) := by
    intro y hy
    rw [hvℓ]
    exact (withZero_exp_lt_one hy).trans (withZero_exp_gt_neg_two hlo)
  intro x hx
  have := unif_loc (D.s.atP p) ((Loc.resChar p : ℕ) : D.host.F) hunif x hx
  simpa using this

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

theorem uniformizer_almost_all_places : FpUnifCof := fpUnif_cof

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

theorem differentTrivial_almost_all : DiffTrivCof := diffTrivCof_of epsilonDual_almost_all uniformizer_almost_all_places residueDegree_almost_all

theorem differentUnit_almost_all : DeltaUnitCof := deltaUnitCof_of differentTrivial_almost_all

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel.LM

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem ιE_int_mem_O (p : PlF D) (a : 𝓞 D.host.E) : (D.s.atP p).ιE (a : D.host.E) ∈ (D.s.atP p).O := iotaE_mem_of_int D p (NumberField.RingOfIntegers.isIntegral_coe a)

theorem algebraMap_mem_O (p : PlF D) {t : (D.s.atP p).Fp} (ht : t ∈ 𝒪[(D.s.atP p).Fp]) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep t ∈ (D.s.atP p).O := alg_mem_O D p ht

theorem inv_intCast_mem (p : PlF D) (n : ℤ) (hn : ((n : 𝓞 D.host.F)) ∉ p.asIdeal) :
    ((D.s.atP p).ιF (n : D.host.F))⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
  have hv : p.valuation D.host.F (n : D.host.F) = 1 := by
    have e : ((n : D.host.F)) = algebraMap (𝓞 D.host.F) D.host.F (n : 𝓞 D.host.F) := by simp
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    first
    | exact (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff (v := p)).2 hn
    | (apply le_antisymm (p.intValuation_le_one _)
       rw [← not_lt, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
       exact hn)
    | (apply le_antisymm (p.intValuation_le_one _)
       rw [← not_lt, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_dvd,
         Ideal.dvd_span_singleton]
       exact hn)
  rw [memO_iff, ← map_inv₀, ← map_one (D.s.atP p).ιF, (D.s.atP p).val, map_one, map_inv₀, hv]
  all_goals simp

theorem intMem_finite (n : ℤ) (hn : n ≠ 0) : {p : PlF D | (n : 𝓞 D.host.F) ∈ p.asIdeal}.Finite := by
  have hI : Ideal.span {((n : 𝓞 D.host.F))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hp

theorem iotaIntegral_almost_all : IotaIntCof := by
  intro D x
  obtain ⟨m, hm0, hmx⟩ : ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : D.host.E) * x) := by
    first
    | (obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
          (nonZeroDivisors ℤ) x (Algebra.IsIntegral.isIntegral (R := ℚ) x)
       exact ⟨m, nonZeroDivisors.ne_zero hm, by simpa [Submonoid.smul_def, Submonoid.mk_smul, zsmul_eq_mul] using hmx⟩)
    | (obtain ⟨m, hm, hmx⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) x).exists_integral_multiple
       exact ⟨m, hm, by simpa [zsmul_eq_mul] using hmx⟩)
  filter_upwards [(intMem_finite (D := D) m hm0).compl_mem_cofinite] with p hp
  have hmp : ((m : 𝓞 D.host.F)) ∉ p.asIdeal := hp
  have hmE : ((m : D.host.E)) ≠ 0 := by exact_mod_cast hm0
  have e : x = algebraMap D.host.F D.host.E ((m : D.host.F)⁻¹) * ((m : D.host.E) * x) := by
    rw [map_inv₀, map_intCast, ← mul_assoc, inv_mul_cancel₀ hmE, one_mul]
  rw [e, map_mul, (D.s.atP p).compat, map_inv₀]
  exact mul_mem (algebraMap_mem_O p (inv_intCast_mem p m hmp)) (iotaE_mem_of_int D p hmx)

end Formalism.L2.SG.Pf.LocModel.LM

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem resCard_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : Loc.LocAt F E sig p) :
    Nat.card 𝓀[A.Fp] = p.asIdeal.absNorm := by
  have := A.lf
  have key : ∀ x y : F, valuation A.Fp (A.ιF x) ≤ valuation A.Fp (A.ιF y) ↔
      p.valuation F x ≤ p.valuation F y := fun x y => by
    rw [← Valuation.vle_iff_le]; exact A.val x y
  have keyle1 : ∀ x : F, valuation A.Fp (A.ιF x) ≤ 1 ↔ p.valuation F x ≤ 1 := fun x => by
    have h := key x 1
    rwa [map_one, map_one, map_one] at h
  have keylt1 : ∀ x : F, valuation A.Fp (A.ιF x) < 1 ↔ p.valuation F x < 1 := fun x => by
    have h := key 1 x
    rw [map_one, map_one, map_one] at h
    rw [← not_le, ← not_le, h]
  let f : 𝓞 F →+* 𝒪[A.Fp] :=
    { toFun := fun x => ⟨A.ιF (algebraMap (𝓞 F) F x),
        (keyle1 _).2 (p.valuation_le_one (K := F) x)⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  let φ : 𝓞 F →+* 𝓀[A.Fp] := (IsLocalRing.residue 𝒪[A.Fp]).comp f
  have hmax : ∀ w : 𝒪[A.Fp], w ∈ IsLocalRing.maximalIdeal 𝒪[A.Fp] ↔ valuation A.Fp (w : A.Fp) < 1 :=
    fun w => by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hker : RingHom.ker φ = p.asIdeal := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax]
    exact (keylt1 _).trans (p.valuation_lt_one_iff_mem (K := F) x)
  have hsurj : Function.Surjective φ := by
    intro z0
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z0
    have hS : {w : A.Fp | valuation A.Fp (w - z) < 1} ∈ nhds (z : A.Fp) :=
      (IsValuativeTopology.hasBasis_nhds' (z : A.Fp)).mem_of_mem one_ne_zero
    obtain ⟨w, ⟨x', rfl⟩, hw⟩ := A.dense.inter_nhds_nonempty hS
    have hw' : valuation A.Fp (A.ιF x' - z) < 1 := hw
    have hx' : p.valuation F x' ≤ 1 := by
      rw [← keyle1]
      have hz : valuation A.Fp (z : A.Fp) ≤ 1 := z.2
      have := Valuation.map_add_le (valuation A.Fp) hw'.le hz
      simpa using this
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer
      (v := p) (K := F) hx' 1
    have ha' : p.valuation F (algebraMap (𝓞 F) F a - x') < 1 := by simpa using ha
    refine ⟨a, ?_⟩
    rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hmax]
    have h1 : valuation A.Fp (A.ιF (algebraMap (𝓞 F) F a - x')) < 1 := (keylt1 _).2 ha'
    have h2 := Valuation.map_add_lt (valuation A.Fp) h1 hw'
    have he : ((f a - z : 𝒪[A.Fp]) : A.Fp) =
        A.ιF (algebraMap (𝓞 F) F a - x') + (A.ιF x' - z) := by
      simp only [map_sub]
      show A.ιF (algebraMap (𝓞 F) F a) - (z : A.Fp) = _
      ring
    rw [he]
    exact h2
  rw [← hker, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv).symm

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PtUnit

variable {D : Formalism.BasicNotions.D7}

def UnitIn {B : Type} [CommRing B] (O : Subring B) (x : B) : Prop := x ∈ O ∧ ∃ y ∈ O, x * y = 1

theorem det_mem_of {B : Type} [CommRing B] (O : Subring B) {n : ℕ} (A : Matrix (Fin n) (Fin n) B)
    (h : ∀ i j, A i j ∈ O) : A.det ∈ O := by
  rw [Matrix.det_apply]
  refine O.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (O.prod_mem fun i _ => h _ _) _

theorem modBlocks_some {A B : Type} [CommRing B] (O : Subring B) (f : ℕ → ℕ → A → B) :
    ∀ (L : List (A × ℕ)) (a : ℕ), (∀ b ∈ L, 0 < b.2) → (∀ a', ∀ b ∈ L, UnitIn O (f a' b.2 b.1)) →
      ∃ l, modBlocks f a L = some l ∧ l.map (fun b => (b.2 : ℕ)) = L.map Prod.snd ∧
        ∀ b ∈ l, UnitIn O (b.1 : B) ∧ UnitIn O (((b.1)⁻¹ : Bˣ) : B)
  | [], _, _, _ => ⟨[], rfl, rfl, by simp⟩
  | (t, s) :: rest, a, hs, hu => by
    have h0 : 0 < s := hs (t, s) List.mem_cons_self
    obtain ⟨hx, y, hy, hxy⟩ := hu a (t, s) List.mem_cons_self
    have hU : IsUnit (f a s t) := IsUnit.of_mul_eq_one _ hxy
    obtain ⟨l, hl, hls, hlu⟩ := modBlocks_some O f rest (a + s) (fun b hb => hs b (List.mem_cons_of_mem _ hb))
      (fun a' b hb => hu a' b (List.mem_cons_of_mem _ hb))
    refine ⟨(hU.unit, ⟨s, h0⟩) :: l, ?_, ?_, ?_⟩
    · simp only [modBlocks, dif_pos (show IsUnit (f a s t) ∧ 0 < s from ⟨hU, h0⟩), hl, Option.map_some]
    · simp [hls]
    · intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · have hinv : ((hU.unit⁻¹ : Bˣ) : B) = y := Units.inv_eq_of_mul_eq_one_right hxy
        refine ⟨⟨hx, y, hy, hxy⟩, ?_⟩
        simp only
        rw [hinv]
        exact ⟨hy, f a s t, hx, by rw [mul_comm]; exact hxy⟩
      · exact hlu b hb

theorem getD_unitIn {B : Type} [CommRing B] (O : Subring B) (l : List (Bˣ × ℕ+))
    (hl : ∀ b ∈ l, UnitIn O (b.1 : B) ∧ UnitIn O (((b.1)⁻¹ : Bˣ) : B)) (i : ℕ) :
    ((l.map Prod.fst).getD i 1 : B) ∈ O ∧ ((((l.map Prod.fst).getD i 1)⁻¹ : Bˣ) : B) ∈ O := by
  rw [List.getD_eq_getElem?_getD]
  cases hgi : (l.map Prod.fst)[i]? with
  | none => simp
  | some u =>
    simp only [Option.getD_some]
    obtain ⟨b, hb, rfl⟩ : ∃ b ∈ l, b.1 = u := by
      have hm := List.mem_of_getElem? hgi
      simpa using hm
    exact ⟨(hl b hb).1.1, (hl b hb).2.1⟩

theorem inGLR_of_units {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {n : ℕ} (a : Loc.Pt E n)
    (ha : ∀ b ∈ a.blocks, UnitIn M.R (b.1 : E) ∧ UnitIn M.R (((b.1)⁻¹ : Eˣ) : E)) : M.InGLR a := by
  have ht : ∀ i, (((Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 i : Eˣ) : E) ∈ M.R ∧
      ((((Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 i)⁻¹ : Eˣ) : E) ∈ M.R := fun i => getD_unitIn M.R a.blocks ha i
  set s := (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1
  set t := (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2
  have hP : ∀ i j, Formalism.DoubleCosetMeasures.pt s t i j ∈ M.R := by
    intro i j
    unfold Formalism.DoubleCosetMeasures.pt
    split_ifs
    · exact (ht _).1
    · exact M.R.zero_mem
  have hPi : ∀ i j, (Formalism.DoubleCosetMeasures.pt s t)⁻¹ i j ∈ M.R := by
    intro i j
    rw [Formalism.FourierDecayAlt.P.A5x7.pt_inv (s, t)]
    unfold Formalism.DoubleCosetMeasures.P.Phase.ptI Formalism.DoubleCosetMeasures.P.Phase.mono
    split_ifs
    · exact (ht _).2
    · exact M.R.zero_mem
  refine ⟨fun i j => ?_, (Formalism.DoubleCosetMeasures.pt s t)⁻¹.det, det_mem_of M.R _ hPi, ?_⟩
  · rw [Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]
    exact hP _ _
  · rw [Formalism.MainNotions.LocalModelPeriodLattices.det_eq, ← Matrix.det_mul,
      Matrix.mul_nonsing_inv _ (Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit (s, t)), Matrix.det_one]

end PtUnit

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section PtUnit2

variable {D : Formalism.BasicNotions.D7}

theorem unitAt_mem₂ (p : PlF D) :
    uP p ∈ ({((D.host.g 0 : ℕ) : ℚ) / (Lat.gS D : ℚ), ((D.host.g 1 : ℕ) : ℚ) / (Lat.gS D : ℚ),
      1 / (Lat.gS D : ℚ)} : Finset ℚ) := by
  unfold uP gpart
  split_ifs <;> simp

theorem gS_ne' : (Lat.gS D : ℚ) ≠ 0 := by
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  unfold Lat.gS
  positivity

theorem unitAt_ne_zero₂ (p : PlF D) : uP p ≠ 0 := by
  have h := gS_ne' (D := D)
  unfold Lat.gS at h
  push_cast at h
  have h0 : ((D.host.g 0 : ℕ) : ℚ) ≠ 0 := left_ne_zero_of_mul h
  have h1 : ((D.host.g 1 : ℕ) : ℚ) ≠ 0 := right_ne_zero_of_mul h
  unfold uP gpart
  refine div_ne_zero ?_ gS_ne'
  split_ifs <;> first | exact h0 | exact h1 | norm_num

theorem ring_inverse_pow_eq {B : Type} [CommRing B] {x y : B} (h : x * y = 1) (ν : ℕ) :
    Ring.inverse (x ^ ν) = y ^ ν := by
  let u : Bˣ := ⟨x, y, h, by rw [mul_comm]; exact h⟩
  have e : x ^ ν = ((u ^ ν : Bˣ) : B) := by simp [u]
  rw [e, Ring.inverse_unit]
  simp [u]

theorem split_none_of_agree {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {p : PlF D} (hA : Agree δ M p)
    (hs : (M p).split = none) : (D.s.atP p).split = none := by
  have h := hA.2.2.2.2.2
  rw [hs] at h
  revert h
  cases hD : (D.s.atP p).split <;> simp

theorem good_place {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (T T' : ℕ) {n : ℕ} (w : Point D.host.E n)
    (p : PlF D) (hA : Agree δ M p) (hsM : (M p).split = none)
    (hδ1 : δ p ∈ 𝒪[(D.s.atP p).Fp]) (hδ2 : (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hUp : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (hNp : ∀ b ∈ w.1, ∀ k : Fin 3, b.1 + ((k : ℕ) : D.host.E) ≠ 0 →
      (D.s.atP p).ιE (b.1 + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
        (D.s.atP p).ιE ((b.1 + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O) :
    (∀ x ∈ (M p).R, (M p).psiR x = 1) ∧ ∃ a, modPt δ T T' p w = some a ∧ (M p).InGLR a := by
  have hsD : (D.s.atP p).split = none := split_none_of_agree hA hsM
  obtain ⟨hOK, hδ0, hcj, hO, hpsi, -⟩ := hA
  have hRL : (M p).R = (M p).L.O := by simp only [Loc.Model.R, hsM]
  have hR : (M p).R = (D.s.atP p).O := hRL.trans hO
  refine ⟨fun x hx => ?_, ?_⟩
  · have hψ : (M p).psiR = (M p).L.psi0 := by simp only [Loc.Model.psiR, hsM]
    rw [hψ]
    have h1 := ((M p).L.additive_character_dual_ring 1).mpr (Subring.one_mem _) x (hRL ▸ hx)
    rwa [one_mul] at h1

  set w0 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
    with hw0
  set w1 : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ *
    (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw1
  have hw01 : w0 * w1 = 1 := by
    rw [hw0, hw1, mul_mul_mul_comm, ← map_mul, ← map_mul, mul_inv_cancel₀ hδ0,
      mul_inv_cancel₀ (by exact_mod_cast unitAt_ne_zero₂ p), map_one, map_one, one_mul]
  have hw0O : w0 ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (LM.algebraMap_mem_O p hδ1) hUp.1
  have hw1O : w1 ∈ (D.s.atP p).O :=
    Subring.mul_mem _ (LM.algebraMap_mem_O p hδ2) hUp.2
  have htau : tau0 p T T' = 0 := by simp only [tau0, hsD]
  have htM : ∀ ν s t, tMod δ p ν s t = w1 ^ ν * (D.s.atP p).ιE t := by
    intro ν s t
    simp only [tMod, twist, qE, hsD, Ring.inverse_one, mul_one]
    rw [ring_inverse_pow_eq hw01]
  have hbM : ∀ a s t, blkMod δ T T' p a s t = w1 ^ nu D.R.rS a (a + s - 1) * (D.s.atP p).ιE t := by
    intro a s t
    simp only [blkMod, htau, ite_self, sub_zero, htM]
  have hnt : Nontrivial (D.s.atP p).Ep := PI.ProdFormulaE.Base.nontrivial (D.s.atP p)

  have hunit : ∀ a', ∀ b ∈ w.1, UnitIn (D.s.atP p).O (blkTop δ T T' p a' b.2 b.1) := by
    intro a' b hb
    obtain ⟨t, s⟩ := b
    have ht0 : t ≠ 0 := (w.2.1 (t, s) hb).1
    have h0 := hNp (t, s) hb 0 (by simpa using ht0)
    simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h0
    have htt : (D.s.atP p).ιE t * (D.s.atP p).ιE t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ht0, map_one]
    by_cases hsp : a' + s - 1 = D.R.rS + 1 ∧ s = 1
    · have hnu : nu D.R.rS a' (a' + s - 1) = 0 := by unfold nu; omega
      have hb0 : blkMod δ T T' p a' s t = (D.s.atP p).ιE t := by rw [hbM, hnu, pow_zero, one_mul]
      simp only [blkTop, if_pos hsp, hb0]
      have hc : ∃ k : Fin 3, IsUnit ((D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) :=
        ⟨0, by simpa using IsUnit.of_mul_eq_one _ htt⟩
      simp only [nSh, dif_pos hc]
      set k := hc.choose with hk
      have hku : IsUnit ((D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep)) := hc.choose_spec
      have he : (D.s.atP p).ιE t + (((k : Fin 3) : ℕ) : (D.s.atP p).Ep) =
          (D.s.atP p).ιE (t + (((k : Fin 3) : ℕ) : D.host.E)) := by rw [map_add, map_natCast]
      rw [he] at hku ⊢
      have hne : t + (((k : Fin 3) : ℕ) : D.host.E) ≠ 0 := by
        intro h0'
        rw [h0', map_zero] at hku
        exact not_isUnit_zero hku
      obtain ⟨hk1, hk2⟩ := hNp (t, s) hb k hne
      exact ⟨hk1, _, hk2, by rw [← map_mul, mul_inv_cancel₀ hne, map_one]⟩
    · simp only [blkTop, if_neg hsp, hbM]
      refine ⟨Subring.mul_mem _ (Subring.pow_mem _ hw1O _) h0.1, w0 ^ nu D.R.rS a' (a' + s - 1) *
        (D.s.atP p).ιE t⁻¹, Subring.mul_mem _ (Subring.pow_mem _ hw0O _) h0.2, ?_⟩
      calc w1 ^ nu D.R.rS a' (a' + s - 1) * (D.s.atP p).ιE t *
            (w0 ^ nu D.R.rS a' (a' + s - 1) * (D.s.atP p).ιE t⁻¹)
          = (w0 * w1) ^ nu D.R.rS a' (a' + s - 1) * ((D.s.atP p).ιE t * (D.s.atP p).ιE t⁻¹) := by ring
        _ = 1 := by rw [hw01, htt, one_pow, one_mul]
  obtain ⟨l, hl, hls, hlu⟩ := modBlocks_some (D.s.atP p).O (blkTop δ T T' p) w.1 1
    (fun b hb => (w.2.1 b hb).2) hunit
  have hsum : (l.map (fun b => (b.2 : ℕ))).sum = n := by rw [hls]; exact w.2.2
  refine ⟨⟨l, hsum⟩, ?_, ?_⟩
  · simp only [modPt, hl, dif_pos hsum]
  · apply inGLR_of_units
    intro b hb
    rw [hR]
    exact hlu b hb

def PtUnitAEBody (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (T T' n : ℕ) (w : Point D.host.E n), n ≤ D.R.rS + 1 →
    {p : PlF D | ¬ ((M p).split = none ∧ (∀ x ∈ (M p).R, (M p).psiR x = 1) ∧
      ∃ a, modPt δ T T' p w = some a ∧ (M p).InGLR a)}.Finite

theorem good_cofinite (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (X : Finset D.host.E) :
    ∀ᶠ p in Filter.cofinite, (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧
        (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
      ∀ t ∈ X, ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
        (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
  set S : Finset ℚ := {((D.host.g 0 : ℕ) : ℚ) / (Lat.gS D : ℚ), ((D.host.g 1 : ℕ) : ℚ) / (Lat.gS D : ℚ),
      1 / (Lat.gS D : ℚ)} with hS
  have hU : ∀ᶠ p in Filter.cofinite, ∀ c ∈ S, (D.s.atP p).ιE (c : D.host.E) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((c : D.host.E)⁻¹) ∈ (D.s.atP p).O := by
    rw [Filter.eventually_all_finset]
    intro c _
    exact (LM.iotaIntegral_almost_all D _).and (LM.iotaIntegral_almost_all D _)
  have hN : ∀ᶠ p in Filter.cofinite, ∀ t ∈ X, ∀ k : Fin 3, t + ((k : ℕ) : D.host.E) ≠ 0 →
        (D.s.atP p).ιE (t + ((k : ℕ) : D.host.E)) ∈ (D.s.atP p).O ∧
          (D.s.atP p).ιE ((t + ((k : ℕ) : D.host.E))⁻¹) ∈ (D.s.atP p).O := by
    rw [Filter.eventually_all_finset]
    intro t _
    rw [Filter.eventually_all]
    intro k
    by_cases h0 : t + ((k : ℕ) : D.host.E) = 0
    · exact Filter.Eventually.of_forall fun _ h => absurd h0 h
    · exact ((LM.iotaIntegral_almost_all D _).and (LM.iotaIntegral_almost_all D _)).mono fun _ hp _ => hp
  filter_upwards [PI.UnitaryGroupMassFormula.CntFormula.local_models_split_cofinite D δ M hA, LM.differentUnit_almost_all D δ M hA, hU, hN]
    with p h1 h2 h3 h4
  exact ⟨h1, h2, h3 _ (unitAt_mem₂ p), h4⟩

theorem ptUnitAE_body (D : Formalism.BasicNotions.D7) : PtUnitAEBody D := by
  intro δ M hA T T' n w _
  have hev := good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro hgood
  apply hp
  obtain ⟨hs, ⟨hδ1, hδ2⟩, hUp, hX⟩ := hgood
  obtain ⟨hψ, ha⟩ := good_place T T' w p (hA p) hs hδ1 hδ2 hUp
    (fun b hb k hk => hX b.1 (List.mem_toFinset.2 (List.mem_map.2 ⟨b, hb, rfl⟩)) k hk)
  exact ⟨hs, hψ, ha⟩

end PtUnit2

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory
open Classical

section Triv

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

def oneMat (M : Loc.Model F E) (m : ℕ) : M.Mat (m + 1) :=
  ⟨1, by rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]; exact isUnit_one⟩

def trivCls (M : Loc.Model F E) (m : ℕ) : M.Cls m := Quotient.mk (M.isoSetoid m) (oneMat M m)

theorem cok_one_subsingleton (M : Loc.Model F E) (m : ℕ) : Subsingleton (M.Cok (oneMat M m)) := by
  unfold Loc.Model.Cok
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro x _
  exact ⟨x, by simp [oneMat]⟩

theorem iso_of_sub (M : Loc.Model F E) {m : ℕ} (Z Z' : M.Mat (m + 1)) (h : Subsingleton (M.Cok Z))
    (h' : Subsingleton (M.Cok Z')) : Nonempty (M.Iso Z Z') :=
  ⟨⟨LinearEquiv.ofSubsingleton _ _, Subsingleton.elim _ _, fun v => by
    rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero]⟩⟩

theorem nIso_self_eq_one (M : Loc.Model F E) {m : ℕ} (Z : M.Mat (m + 1)) (h : Subsingleton (M.Cok Z)) :
    M.nIso Z Z = 1 := by
  unfold Loc.Model.nIso
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun x => Subsingleton.elim _ _)⟩,
    ⟨⟨LinearEquiv.refl _ _, rfl, fun _ => rfl⟩⟩⟩

theorem sub_iff_triv (M : Loc.Model F E) {m : ℕ} (Z : M.Mat (m + 1)) :
    Subsingleton (M.Cok Z) ↔ Quotient.mk (M.isoSetoid m) Z = trivCls M m := by
  constructor
  · intro h
    exact Quotient.sound (iso_of_sub M Z (oneMat M m) h (cok_one_subsingleton M m))
  · intro h
    have h2 : Quotient.mk (M.isoSetoid m) (oneMat M m) = Quotient.mk (M.isoSetoid m) Z := h.symm
    obtain ⟨φ⟩ := Quotient.exact h2
    haveI := cok_one_subsingleton M m
    exact φ.1.symm.injective.subsingleton

theorem nAut_triv (M : Loc.Model F E) (m : ℕ) : M.nAut (trivCls M m) = 1 := by
  unfold Loc.Model.nAut
  apply nIso_self_eq_one
  exact (sub_iff_triv M _).2 (Quotient.out_eq (s := M.isoSetoid m) _)

theorem cls_of_nIso (M : Loc.Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) (c : M.Cls m)
    (hn : M.nIso ZZ (Quotient.out c) ≠ 0) : Quotient.mk (M.isoSetoid m) ZZ = c := by
  unfold Loc.Model.nIso at hn
  obtain ⟨φ⟩ := (Nat.card_ne_zero.1 hn).1
  exact (Quotient.sound (s := M.isoSetoid m) (show Nonempty (M.Iso ZZ (Quotient.out c)) from ⟨φ⟩)).trans
    (Quotient.out_eq (s := M.isoSetoid m) c)

theorem uLow_det {n : ℕ} (x : Loc.IL n → E) : (Loc.uLow x).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (fun i j hij => by
    have h' : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp [Loc.uLow, h'.ne, not_lt.2 h'.le])]
  simp [Loc.uLow]

theorem uUp_det {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : (Loc.uUp w y).det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => by
    have h' : j < i := hij
    simp [Loc.uUp, h'.ne', not_lt.2 h'.le])]
  simp [Loc.uUp]

theorem cls_of_bb_ne (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) (h : M.BB a c ≠ 0) :
    ∃ ZZ : M.Mat (m + 1), ((ZZ.Z.det : M.R) : E) = a.mat.det ∧ Quotient.mk (M.isoSetoid m) ZZ = c := by
  by_contra hno
  apply h
  unfold Loc.Model.BB
  have hz : (fun xy => M.bbIntegrand a c xy) = fun _ => 0 := by
    funext xy
    unfold Loc.Model.bbIntegrand
    simp only
    split_ifs with hZ
    · refine mul_eq_zero_of_left ?_ _
      rw [Nat.cast_eq_zero]
      by_contra hn
      refine hno ⟨_, ?_, cls_of_nIso M _ c hn⟩
      change M.R.subtype (Matrix.det _) = _
      rw [RingHom.map_det]
      have e : M.R.subtype.mapMatrix (Matrix.of fun i j =>
          (⟨(Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j, hZ.1 i j⟩ : M.R)) =
          Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2 := by ext; rfl
      rw [e, Matrix.det_mul, Matrix.det_mul, uLow_det, uUp_det, one_mul, mul_one]
    · rfl
  rw [hz, integral_zero]

theorem bb_glr (M : Loc.Model F E) (hOK : M.OK) (hψ : ∀ x ∈ M.R, M.psiR x = 1) {m : ℕ} (a : Loc.Pt E (m + 1))
    (ha : M.InGLR a) (c : M.Cls m) : M.BB a c = if c = trivCls M m then 1 else 0 := by
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK M hOK
  obtain ⟨μ₁, μ₂, hi1, hi2, hs1, hs2, hv1, hv2, hint⟩ := Formalism.MainNotions.LocalOrbitGerms.ctAll F E M hOK (m + 1) a
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.BB_eq M a μ₁ μ₂ hint c]
  have hD := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK M hOK
  haveI := hD.t2
  haveI := hi1
  haveI := hi2
  haveI := hs1
  haveI := hs2
  rw [Formalism.DoubleCosetMeasures.Final.bbNorm E M.R hD.isOpen _ _ M.psiR hψ μ₁ μ₂ hv1 hv2 _ _ _
    (Formalism.DoubleCosetMeasures.Final.suppCompact E M.R hD.isOpen hD.isCompact _ _ _ _ _ _)]
  have hg := Formalism.MainNotions.LocalModelPeriodLattices.inGLR_tr a ha
  rw [finsum_eq_single _ (Formalism.FourierDecayAlt.P.A5x7.cos1 M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a))]
  · have c1 := (Formalism.FourierDecayAlt.P.A5x7.cos_eq_iff M.R _ (Formalism.FourierDecayAlt.P.A5x7.cos1 M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a))).mp rfl
    obtain ⟨i1, j1, k1⟩ := Formalism.FourierDecayAlt.P.A5x7.orb_of_int M.R _ hg _ c1.1 c1.2
    have hph := Formalism.FourierDecayAlt.P.A5x7.phase_one M.R M.psiR hψ _ _ c1.1 c1.2
    unfold Formalism.FourierDecayAlt.A5.orbZ Formalism.FourierDecayAlt.A5.rep at i1 j1 k1
    unfold Formalism.FourierDecayAlt.A5.phase Formalism.FourierDecayAlt.A5.rep at hph
    unfold Formalism.DoubleCosetMeasures.phi
    rw [if_pos i1, hph, mul_one]
    haveI hsub := Formalism.FourierDecayAlt.P.A5x7.coker_subsingleton M.R j1 k1
    by_cases hc : c = trivCls M m
    · rw [if_pos hc, Nat.cast_eq_one, Nat.card_eq_one_iff_unique]
      haveI hC : Subsingleton (M.Cok (Quotient.out c)) :=
        (sub_iff_triv M _).2 ((Quotient.out_eq (s := M.isoSetoid m) c).trans hc)
      refine ⟨⟨fun x y => Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)⟩,
        ⟨⟨LinearEquiv.ofSubsingleton _ _, Subsingleton.elim _ _, fun v => ?_⟩⟩⟩
      rw [Formalism.FourierDecayAlt.P.A5x7.lamLin_zero M.R j1 v, Subsingleton.elim (LinearEquiv.ofSubsingleton _ _ _) 0, map_zero]
    · rw [if_neg hc, Nat.cast_eq_zero, Nat.card_eq_zero]
      refine Or.inl ⟨fun x => hc ?_⟩
      haveI : Subsingleton (M.Cok (Quotient.out c)) := x.1.symm.injective.subsingleton
      exact (Quotient.out_eq (s := M.isoSetoid m) c).symm.trans ((sub_iff_triv M (Quotient.out c)).1 this)
  · intro q hq
    unfold Formalism.DoubleCosetMeasures.phi
    rw [if_neg, zero_mul]
    intro hI
    exact hq ((Formalism.FourierDecayAlt.P.A5x7.int_iff M.R _ hg q).mp hI)

end Triv

section Top

variable {D : Formalism.BasicNotions.D7}

def thTriv (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) : ∀ p, Option ((M p).Cls D.R.rS) :=
  fun p => some (trivCls (M p) D.R.rS)

theorem autP_thTriv (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) :
    autP M p (thTriv M p) = 1 := by
  first
  | (simp only [autP, thTriv]; rw [nAut_triv]; simp)
  | (show (((M p).nAut (trivCls (M p) D.R.rS) : ℕ) : ℂ) = 1; rw [nAut_triv]; simp)
  | simp [autP, thTriv, nAut_triv]

theorem bbtop_good {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ)
    (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) (hsM : (M p).split = none)
    (hψ : ∀ x ∈ (M p).R, (M p).psiR x = 1) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ T T' p w = some a) (hG : (M p).InGLR a) (o : Option ((M p).Cls D.R.rS)) :
    BBtop M δ T T' p w o = if o = thTriv M p then 1 else 0 := by
  have hsD := split_none_of_agree (hA p) hsM
  have hd : dfac M δ T T' p w = 1 := by unfold dfac; rw [hsD]
  cases o with
  | none => simp [BBtop, ha, thTriv]
  | some c =>
    simp only [BBtop, ha, hd, one_mul, bb_glr (M p) (hA p).1 hψ a hG c, thTriv, Option.some.injEq]

theorem bbsq_all {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ)
    (w : Point D.host.E (D.R.rS + 1)) (p : PlF D) : BBsq M δ T T' p w := by
  unfold BBsq
  apply summable_of_finite_support
  rcases hm : modPt δ T T' p w with _ | a
  · refine Set.finite_empty.subset fun o ho => ho ?_
    simp [BBtop, hm]
  · have hd : IsUnit a.mat.det := by
      rw [Formalism.MainNotions.LocalModelPeriodLattices.det_eq]; exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
    refine ((Formalism.MainNotions.LocalOrbitGerms.Cls.finite_S (M p) (hA p).1 D.R.rS a.mat.det hd).image some).subset ?_
    intro o ho
    cases o with
    | none => exact absurd (by simp [BBtop, hm]) ho
    | some c =>
      refine ⟨c, ?_, rfl⟩
      apply cls_of_bb_ne (M p) a c
      intro h0
      apply ho
      simp [BBtop, hm, h0]

def TopUnramBody (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ T T' : ℕ, ∃ θ0 : ∀ p, Option ((M p).Cls D.R.rS),
      ∀ w : Point D.host.E (D.R.rS + 1), (∃ S : Finset (PlF D), UnramOff M δ T T' θ0 S w) ∧
        ∀ p, BBsq M δ T T' p w

theorem topUnram_body (D : Formalism.BasicNotions.D7) : TopUnramBody D := by
  intro δ M hA T T'
  refine ⟨thTriv M, fun w => ⟨?_, fun p => bbsq_all hA T T' w p⟩⟩
  have hev := good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hev
  refine ⟨hev.toFinset, fun p hp => ⟨autP_thTriv M p, fun o => ?_⟩⟩
  rw [Set.Finite.mem_toFinset] at hp
  simp only [Set.mem_setOf_eq, not_not] at hp
  obtain ⟨hs, ⟨hδ1, hδ2⟩, hUp, hX⟩ := hp
  obtain ⟨hψ, a, ha, hG⟩ := good_place T T' w p (hA p) hs hδ1 hδ2 hUp
    (fun b hb k hk => hX b.1 (List.mem_toFinset.2 (List.mem_map.2 ⟨b, hb, rfl⟩)) k hk)
  exact bbtop_good hA T T' w p hs hψ a ha hG o

end Top

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups
open Classical

section Alp

variable {D : Formalism.BasicNotions.D7}

def qPl (p : PlF D) : ℝ := (Nat.card (IsLocalRing.ResidueField 𝒪[(D.s.atP p).Fp]) : ℝ)

theorem qPl_eq (p : PlF D) : qPl p = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := by
  first
  | rw [qPl, resCard_loc (D.s.atP p)]
  | simp [qPl, resCard_loc]

theorem two_le_qPl (p : PlF D) : (2 : ℝ) ≤ qPl p := by
  rw [qPl_eq]
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
  have h2 : 2 ≤ Ideal.absNorm p.asIdeal := by omega
  exact_mod_cast h2

theorem exp_neg_two_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) : Real.exp (-(2 * y)) ≤ 1 - y := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 2 * y by linarith)
  have h2 : Real.exp (-(2 * y)) * Real.exp (2 * y) = 1 := by rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos (-(2 * y))
  have h4 : 1 ≤ (1 - y) * Real.exp (2 * y) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 - y by linarith) (sub_nonneg.2 h1),
      mul_nonneg hy0 (mul_nonneg hy0 (show (0:ℝ) ≤ 1 / 2 - y by linarith)),
      mul_nonneg hy0 (show (0:ℝ) ≤ 1 / 2 - y by linarith)]
  calc Real.exp (-(2 * y)) = Real.exp (-(2 * y)) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-(2 * y)) * ((1 - y) * Real.exp (2 * y)) := mul_le_mul_of_nonneg_left h4 h3.le
    _ = 1 - y := by rw [mul_comm (1 - y), ← mul_assoc, h2, one_mul]

theorem geom_Icc_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (a b : ℕ) :
    ∑ i ∈ Finset.Icc a b, x ^ i ≤ 2 * x ^ a := by
  have key : ∀ n : ℕ, x ^ (n + 1) * 2 ≤ x ^ n := fun n => by
    rw [pow_succ]; nlinarith [pow_nonneg hx0 n]
  rcases Nat.lt_or_ge b a with hba | hab
  · have he : Finset.Icc a b = ∅ := by
      first
      | exact Finset.Icc_eq_empty_of_lt hba
      | exact Finset.Icc_eq_empty (by omega)
      | simp; omega
    rw [he, Finset.sum_empty]
    exact mul_nonneg (by norm_num) (pow_nonneg hx0 a)
  · have hc : ∀ c, a ≤ c → ∑ i ∈ Finset.Icc a c, x ^ i ≤ 2 * x ^ a - 2 * x ^ (c + 1) := by
      intro c hc
      induction c, hc using Nat.le_induction with
      | base => rw [Finset.Icc_self, Finset.sum_singleton]; linarith [key a]
      | succ c hc ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        linarith [key (c + 1)]
    linarith [hc b hab, pow_nonneg hx0 (b + 1)]

theorem prod_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) {η : ℝ} (hη : η = 1 ∨ η = -1) (a b : ℕ)
    (ha : 1 ≤ a) :
    Real.exp (-(4 * x ^ a)) ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) ∧
      ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) ≤ Real.exp (2 * x ^ a) := by
  have hxi : ∀ i ∈ Finset.Icc a b, x ^ i ≤ 1 / 2 := by
    intro i hi
    have hi1 : 1 ≤ i := le_trans ha (Finset.mem_Icc.1 hi).1
    calc x ^ i ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) hi1
      _ = x := pow_one x
      _ ≤ 1 / 2 := hx
  have hfac : ∀ i : ℕ, 1 - x ^ i ≤ 1 - η ^ i * x ^ i ∧ 1 - η ^ i * x ^ i ≤ 1 + x ^ i := by
    intro i
    have hxi0 := pow_nonneg hx0 i
    rcases hη with rfl | rfl
    · simp only [one_pow, one_mul]; constructor <;> linarith
    · rcases neg_one_pow_eq_or ℝ i with h | h <;> rw [h] <;> constructor <;> linarith
  have hS := geom_Icc_le hx0 hx a b
  constructor
  · calc Real.exp (-(4 * x ^ a)) ≤ Real.exp (-(2 * ∑ i ∈ Finset.Icc a b, x ^ i)) := by
          apply Real.exp_le_exp.2; linarith
      _ = ∏ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) := by
          first
          | (rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib])
          | (rw [← Real.exp_sum]; congr 1; simp [Finset.mul_sum])
          | simp [← Real.exp_sum, Finset.mul_sum]
      _ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) := by
          apply Finset.prod_le_prod
          · intro i _; exact (Real.exp_pos _).le
          · intro i hi
            exact (exp_neg_two_le (pow_nonneg hx0 i) (hxi i hi)).trans (hfac i).1
  · calc ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) ≤ ∏ i ∈ Finset.Icc a b, Real.exp (x ^ i) := by
          apply Finset.prod_le_prod
          · intro i hi; linarith [(hfac i).1, hxi i hi]
          · intro i _
            exact (hfac i).2.trans (by linarith [Real.add_one_le_exp (x ^ i)])
      _ = Real.exp (∑ i ∈ Finset.Icc a b, x ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * x ^ a) := Real.exp_le_exp.2 hS

theorem etaP_pm (p : PlF D) : Formalism.L2.SG.DataInst.eta₃ p = 1 ∨ Formalism.L2.SG.DataInst.eta₃ p = -1 := by
  unfold Formalism.L2.SG.DataInst.eta₃
  split_ifs <;> simp

theorem aPD_bounds (hk : 1 ≤ D.R.k) (p : PlF D) (T : ℕ) :
    Real.exp (-(4 * (qPl p)⁻¹ ^ D.R.k)) ≤ Formalism.L2.SG.DataInst.aPD p T ∧
      Formalism.L2.SG.DataInst.aPD p T ≤ Real.exp (2 * (qPl p)⁻¹ ^ D.R.k) := by
  have hq := two_le_qPl p
  have hx0 : 0 ≤ (qPl p)⁻¹ := inv_nonneg.2 (by linarith)
  have hx1 : (qPl p)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    first
    | exact inv_anti₀ (by norm_num) hq
    | exact inv_le_inv_of_le (by norm_num) hq
  have key : ∀ a, 1 ≤ a →
      Real.exp (-(4 * (qPl p)⁻¹ ^ a)) ≤ ∏ i ∈ Finset.Icc a D.R.r,
        (1 - Formalism.L2.SG.DataInst.eta₃ p ^ i / ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ i) ∧
      ∏ i ∈ Finset.Icc a D.R.r,
        (1 - Formalism.L2.SG.DataInst.eta₃ p ^ i / ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ i) ≤
        Real.exp (2 * (qPl p)⁻¹ ^ a) := by
    intro a ha
    have e : ∀ i : ℕ, (1 - Formalism.L2.SG.DataInst.eta₃ p ^ i / ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ^ i) =
        1 - Formalism.L2.SG.DataInst.eta₃ p ^ i * (qPl p)⁻¹ ^ i := by
      intro i; rw [qPl_eq, inv_pow, div_eq_mul_inv]
    simp only [e]
    exact prod_bounds hx0 hx1 (etaP_pm p) a D.R.r ha
  unfold Formalism.L2.SG.DataInst.aPD
  split_ifs with hT
  · exact key _ hk
  · obtain ⟨h1, h2⟩ := key (D.R.k + 1) (by omega)
    have hpow : (qPl p)⁻¹ ^ (D.R.k + 1) ≤ (qPl p)⁻¹ ^ D.R.k :=
      pow_le_pow_of_le_one hx0 (by linarith) (by omega)
    constructor
    · exact le_trans (Real.exp_le_exp.2 (by linarith)) h1
    · exact le_trans h2 (Real.exp_le_exp.2 (by linarith))

def AlpBoundBody (D : Formalism.BasicNotions.D7) : Prop :=
  2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → ∀ (u u' : D.what₂.Word) (p : PlF D),
    Real.exp (-(2 * (qPl p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤ Formalism.L2.SG.DataInst.alpD u u' p ∧
      Formalism.L2.SG.DataInst.alpD u u' p ≤ Real.exp (2 * (qPl p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)

theorem alpBound_body (D : Formalism.BasicNotions.D7) : AlpBoundBody D := by
  intro hk u u' p
  have hk1 : 1 ≤ D.R.k := by omega
  have hq := two_le_qPl p
  have hx0 : 0 ≤ (qPl p)⁻¹ := inv_nonneg.2 (by linarith)
  have hx1 : (qPl p)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    first
    | exact inv_anti₀ (by norm_num) hq
    | exact inv_le_inv_of_le (by norm_num) hq
  obtain ⟨a1, a2⟩ := aPD_bounds hk1 p (D.mem u).A.T
  obtain ⟨b1, b2⟩ := aPD_bounds hk1 p (D.mem u').A.T
  rw [← inv_pow]
  set m := D.R.k - 2 * D.R.rS - 2 with hm
  set x := (qPl p)⁻¹ with hx
  have hxm := pow_nonneg hx0 m
  have hxk : x ^ D.R.k ≤ x ^ m / 4 := by
    have h2 : x ^ D.R.k ≤ x ^ (m + 2) := pow_le_pow_of_le_one hx0 (by linarith) (by omega)
    have h3 : x ^ (m + 2) = x ^ m * x * x := by ring
    have h4 : x ^ m * x ≤ x ^ m * (1 / 2) := mul_le_mul_of_nonneg_left hx1 hxm
    have h5 : x ^ m * x * x ≤ x ^ m * x * (1 / 2) := mul_le_mul_of_nonneg_left hx1 (mul_nonneg hxm hx0)
    rw [h3] at h2
    linarith
  unfold Formalism.L2.SG.DataInst.alpD
  split_ifs
  · constructor
    · exact le_trans (Real.exp_le_exp.2 (by linarith)) a1
    · exact le_trans a2 (Real.exp_le_exp.2 (by linarith))
  · constructor
    · calc Real.exp (-(2 * x ^ m)) ≤ Real.exp (-(4 * x ^ D.R.k)) * Real.exp (-(4 * x ^ D.R.k)) := by
            rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
        _ ≤ _ := mul_le_mul a1 b1 (Real.exp_pos _).le (le_trans (Real.exp_pos _).le a1)
    · calc _ ≤ Real.exp (2 * x ^ D.R.k) * Real.exp (2 * x ^ D.R.k) :=
            mul_le_mul a2 b2 (le_trans (Real.exp_pos _).le b1) (Real.exp_pos _).le
        _ ≤ Real.exp (2 * x ^ m) := by rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)

end Alp

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf.LocModel

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.FourierDecayAlt Formalism.L2.SG.DataInst
open Classical

section LMK

variable {D : Formalism.BasicNotions.D7}

theorem plF_nonempty (D : Formalism.BasicNotions.D7) : Nonempty (PlF D) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  have hnf : ¬ IsField (𝓞 D.host.F) := by
    first
    | exact NumberField.RingOfIntegers.not_isField D.host.F
    | exact NumberField.RingOfIntegers.not_isField
    | exact NumberField.RingOfIntegers.not_isField (K := D.host.F)
  have hne : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm hnf
  first
  | exact ⟨⟨m, hm.isPrime, hne⟩⟩
  | exact ⟨{ asIdeal := m, isPrime := hm.isPrime, ne_bot := hne }⟩

def placeOf (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hOK : ∀ p, (M p).OK) (p : PlF D) :
    PB.Place D.host.E where
  K := (D.s.atP p).Ep
  tr := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) (hOK p)
  R := (M p).R
  ψ := (M p).psiR
  datum := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) (hOK p)
  char0 := fun n hn => by
    haveI := (D.s.atP p).char0
    have h : ((n : (D.s.atP p).Fp)) ≠ 0 := Nat.cast_ne_zero.2 hn
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep) n]
    exact (IsUnit.mk0 _ h).map _
  σ := (D.s.atP p).ιE

def ePt (K : Type) [CommRing K] : A5.Point K := ([], fun _ => 1)

theorem kp_ePt {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) (hOK : M.OK) :
    A5.Kp M.R M.psiR (ePt E) (ePt E) = 1 := by
  have h := Formalism.MainNotions.LocalOrbitGerms.KKAll_proved F E M hOK 0 ⟨[], rfl⟩ ⟨[], rfl⟩
  have ht : Formalism.MainNotions.LocalModelPeriodLattices.tr (⟨[], rfl⟩ : Loc.Pt E 0) = ePt E := by
    unfold Formalism.MainNotions.LocalModelPeriodLattices.tr ePt
    simp
  rw [ht] at h
  rw [← h]
  rfl

def mpt (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' i : ℕ) (p : PlF D) (x : TB.Pt D.host.E) :
    Option (Loc.Pt (D.s.atP p).Ep i) :=
  (ptOfList i x).bind (fun w => modPt δ T T' p w)

def etaL (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' i : ℕ) (p : PlF D) (x : TB.Pt D.host.E) :
    A5.Point (D.s.atP p).Ep :=
  match mpt δ T T' i p x with
  | some a => Formalism.MainNotions.LocalModelPeriodLattices.tr a
  | none => ePt _

def dL (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' i : ℕ) (p : PlF D) (x : TB.Pt D.host.E) : ℂ :=
  match mpt δ T T' i p x with
  | some _ => 1
  | none => 0

def dT (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)
    (p : PlF D) (x : TB.Pt D.host.E) : ℂ :=
  match ptOfList (D.R.rS + 1) x with
  | some w => (match modPt δ T T' p w with
    | some _ => dfac M δ T T' p w
    | none => 0)
  | none => 0

def clT (x : TB.Pt D.host.E) : Option D.host.E :=
  match ptOfList (D.R.rS + 1) x with
  | some w => kind w
  | none => none

def aL (i : ℕ) (x : TB.Pt D.host.E) : ℝ :=
  match ptOfList i x with
  | some _ => (phi i x)⁻¹
  | none => 0

theorem locK_eq_kp {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' i : ℕ) (p : PlF D)
    {x y : TB.Pt D.host.E} {w w' : Point D.host.E i} (hx : ptOfList i x = some w) (hy : ptOfList i y = some w') :
    dL δ T T' i p x * (starRingEnd ℂ) (dL δ T T' i p y) *
        A5.Kp (M p).R (M p).psiR (etaL δ T T' i p x) (etaL δ T T' i p y) = locK M δ T T' p i w w' := by
  have ex : mpt δ T T' i p x = modPt δ T T' p w := by simp [mpt, hx]
  have ey : mpt δ T T' i p y = modPt δ T T' p w' := by simp [mpt, hy]
  unfold dL etaL locK
  rw [ex, ey]
  rcases ha : modPt δ T T' p w with _ | a <;> rcases hb : modPt δ T T' p w' with _ | b
  · simp
  · simp
  · simp
  · simp only [map_one, one_mul]
    exact (Formalism.MainNotions.LocalOrbitGerms.KKAll_proved _ _ (M p) (hA p).1 i a b).symm

theorem topTerm_eq_localTerm {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D)
    {x y : TB.Pt D.host.E} {w w' : Point D.host.E (D.R.rS + 1)} (hx : ptOfList (D.R.rS + 1) x = some w)
    (hy : ptOfList (D.R.rS + 1) y = some w') :
    dT M δ T T' p x * (starRingEnd ℂ) (dT M δ T T' p y) *
        A5.Kp (M p).R (M p).psiR (etaL δ T T' (D.R.rS + 1) p x) (etaL δ T T' (D.R.rS + 1) p y) =
      KtopP M δ T T' p w w' := by
  have ex : mpt δ T T' (D.R.rS + 1) p x = modPt δ T T' p w := by simp [mpt, hx]
  have ey : mpt δ T T' (D.R.rS + 1) p y = modPt δ T T' p w' := by simp [mpt, hy]
  unfold dT etaL KtopP locK
  rw [ex, ey, hx, hy]
  rcases ha : modPt δ T T' p w with _ | a <;> rcases hb : modPt δ T T' p w' with _ | b
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb]
  · simp only [ha, hb]
    rw [← Formalism.MainNotions.LocalOrbitGerms.KKAll_proved _ _ (M p) (hA p).1 _ a b]
    ring

theorem clK_core {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) (T T' i : ℕ)
    (Y : Finset (TB.Pt D.host.E)) :
    ∃ (P : Type) (_ : Fintype P) (pl : P → PB.Place D.host.E) (η : ∀ p, TB.Pt D.host.E → A5.Point (pl p).K)
      (cl : P → TB.Pt D.host.E → Option D.host.E) (d : P → TB.Pt D.host.E → ℂ) (a : TB.Pt D.host.E → ℝ),
      ∀ x ∈ Y, ∀ y ∈ Y, KrOf δ M T T' i x y = (a x : ℂ) * a y *
        ∏ p, if cl p x = cl p y then
          d p x * (starRingEnd ℂ) (d p y) * A5.Kp (pl p).R (pl p).ψ (η p x) (η p y) else 0 := by
  have hOK : ∀ p, (M p).OK := fun p => (hA p).1
  obtain ⟨p0⟩ := plF_nonempty D
  have hk0 : A5.Kp (placeOf M hOK p0).R (placeOf M hOK p0).ψ (ePt (placeOf M hOK p0).K)
      (ePt (placeOf M hOK p0).K) = 1 := kp_ePt (M p0) (hOK p0)
  have hunit : ∀ z : ℂ, (∏ _q : Unit, if (none : Option D.host.E) = none then
      (1 : ℂ) * (starRingEnd ℂ) 1 * A5.Kp (placeOf M hOK p0).R (placeOf M hOK p0).ψ (ePt (placeOf M hOK p0).K)
        (ePt (placeOf M hOK p0).K) else 0) * z = z := by
    intro z
    rw [Fintype.prod_unique, if_pos rfl, hk0, map_one, one_mul, one_mul, one_mul]
  by_cases h0 : i = 0
  · subst h0
    refine ⟨Unit, inferInstance, fun _ => placeOf M hOK p0, fun _ _ => ePt _, fun _ _ => none, fun _ _ => 1,
      fun x => if x = [] then 1 else 0, ?_⟩
    intro x _ y _
    rw [mul_comm, hunit]
    unfold KrOf
    rw [if_pos rfl]
    by_cases hx : x = [] <;> by_cases hy : y = [] <;> simp [hx, hy]
  by_cases hbig : D.R.rS + 1 < i
  · refine ⟨Unit, inferInstance, fun _ => placeOf M hOK p0, fun _ _ => ePt _, fun _ _ => none, fun _ _ => 1,
      fun _ => 0, ?_⟩
    intro x _ y _
    rw [mul_comm, hunit]
    unfold KrOf
    rw [if_neg h0, if_pos hbig]
    simp
  have hle : i ≤ D.R.rS + 1 := by omega

  let bad : TB.Pt D.host.E → Finset (PlF D) := fun x =>
    match ptOfList i x with
    | none => ∅
    | some w => (LocModel.ptUnitAE_body D δ M hA T T' i w hle).toFinset
  set B : Finset (PlF D) := insert p0 (Y.biUnion bad) with hB
  have hp0 : p0 ∈ B := Finset.mem_insert_self _ _
  have hgood : ∀ x ∈ Y, ∀ w, ptOfList i x = some w → ∀ p, p ∉ B → p ∉ Formalism.L2.SG.DataCut.badSet δ M T T' i w := by
    intro x hx w hw p hp hbad
    apply hp
    refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨x, hx, ?_⟩)
    simp only [bad, hw]
    exact (Set.Finite.mem_toFinset _).2 hbad
  by_cases ht : i = D.R.rS + 1
  · subst ht
    refine ⟨{p // p ∈ B}, inferInstance, fun q => placeOf M hOK q.1,
      fun q x => etaL δ T T' (D.R.rS + 1) q.1 x, fun _ x => clT x, fun q x => dT M δ T T' q.1 x,
      aL (D.R.rS + 1), ?_⟩
    intro x hx y hy
    rcases hxw : ptOfList (D.R.rS + 1) x with _ | w
    · have h1 : KrOf δ M T T' (D.R.rS + 1) x y = 0 := by
        unfold KrOf; rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hxw]
      have h2 : aL (D.R.rS + 1) x = 0 := by unfold aL; rw [hxw]
      rw [h1, h2]; simp
    rcases hyw : ptOfList (D.R.rS + 1) y with _ | w'
    · have h1 : KrOf δ M T T' (D.R.rS + 1) x y = 0 := by
        unfold KrOf; rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hxw, hyw]
      have h2 : aL (D.R.rS + 1) y = 0 := by unfold aL; rw [hyw]
      rw [h1, h2]; simp
    have hK : KrOf δ M T T' (D.R.rS + 1) x y = KtopG M δ T T' w w' / ((phi (D.R.rS + 1) x : ℂ) * (phi (D.R.rS + 1) y : ℂ)) := by
      unfold KrOf
      rw [if_neg (Nat.succ_ne_zero _), if_neg (lt_irrefl _), hxw, hyw]
      simp only
      rw [Kglob, dif_pos rfl]
    rw [hK]
    have hcl : ∀ q : {p // p ∈ B}, (clT x = clT y) = (kind w = kind w') := by
      intro q; simp [clT, hxw, hyw]
    have hprod : (∏ q : {p // p ∈ B}, if clT x = clT y then
          dT M δ T T' q.1 x * (starRingEnd ℂ) (dT M δ T T' q.1 y) *
            A5.Kp (placeOf M hOK q.1).R (placeOf M hOK q.1).ψ (etaL δ T T' (D.R.rS + 1) q.1 x)
              (etaL δ T T' (D.R.rS + 1) q.1 y) else 0) = KtopG M δ T T' w w' := by
      have hc : (clT x = clT y) ↔ (kind w = kind w') := by simp [clT, hxw, hyw]
      unfold KtopG
      by_cases hk : kind w = kind w'
      · rw [if_pos hk]
        simp only [if_pos (hc.2 hk)]
        have e1 : ∀ q : {p // p ∈ B}, dT M δ T T' q.1 x * (starRingEnd ℂ) (dT M δ T T' q.1 y) *
            A5.Kp (placeOf M hOK q.1).R (placeOf M hOK q.1).ψ (etaL δ T T' (D.R.rS + 1) q.1 x)
              (etaL δ T T' (D.R.rS + 1) q.1 y) = KtopP M δ T T' q.1 w w' := fun q =>
          topTerm_eq_localTerm hA T T' q.1 hxw hyw
        rw [Fintype.prod_congr _ _ e1, Finset.prod_coe_sort B (fun p => KtopP M δ T T' p w w')]
        symm
        refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
        by_contra hpB
        apply hp
        have g1 := hgood x hx w hxw p hpB
        have g2 := hgood y hy w' hyw p hpB
        have hs : (M p).split = none := by
          simp only [Formalism.L2.SG.DataCut.badSet, Set.mem_ofPred_eq, not_not] at g1; exact g1.1
        show KtopP M δ T T' p w w' = 1
        unfold KtopP
        rw [Formalism.L2.SG.DataCut.dfac_eq_one hA hs, Formalism.L2.SG.DataCut.dfac_eq_one hA hs,
          Formalism.L2.SG.DataCut.locK_eq_one Formalism.MainNotions.LocalOrbitGerms.KKAll_proved hA g1 g2]
        simp
      · rw [if_neg hk]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨p0, hp0⟩) ?_
        rw [if_neg (fun h => hk (hc.1 h))]
    rw [hprod]
    have hax : aL (D.R.rS + 1) x = (phi (D.R.rS + 1) x)⁻¹ := by unfold aL; rw [hxw]
    have hay : aL (D.R.rS + 1) y = (phi (D.R.rS + 1) y)⁻¹ := by unfold aL; rw [hyw]
    rw [hax, hay]
    rw [div_eq_mul_inv, mul_inv, Complex.ofReal_inv, Complex.ofReal_inv]
    ring
  · refine ⟨{p // p ∈ B}, inferInstance, fun q => placeOf M hOK q.1,
      fun q x => etaL δ T T' i q.1 x, fun _ _ => none, fun q x => dL δ T T' i q.1 x, aL i, ?_⟩
    intro x hx y hy
    rcases hxw : ptOfList i x with _ | w
    · have h1 : KrOf δ M T T' i x y = 0 := by
        unfold KrOf; rw [if_neg h0, if_neg hbig, hxw]
      have h2 : aL i x = 0 := by unfold aL; rw [hxw]
      rw [h1, h2]; simp
    rcases hyw : ptOfList i y with _ | w'
    · have h1 : KrOf δ M T T' i x y = 0 := by
        unfold KrOf; rw [if_neg h0, if_neg hbig, hxw, hyw]
      have h2 : aL i y = 0 := by unfold aL; rw [hyw]
      rw [h1, h2]; simp
    have hK : KrOf δ M T T' i x y = (∏ᶠ p, locK M δ T T' p i w w') / ((phi i x : ℂ) * (phi i y : ℂ)) := by
      unfold KrOf
      rw [if_neg h0, if_neg hbig, hxw, hyw]
      simp only
      rw [Kglob, dif_neg ht]
    rw [hK]
    have e1 : ∀ q : {p // p ∈ B}, (if (none : Option D.host.E) = none then
        dL δ T T' i q.1 x * (starRingEnd ℂ) (dL δ T T' i q.1 y) *
          A5.Kp (placeOf M hOK q.1).R (placeOf M hOK q.1).ψ (etaL δ T T' i q.1 x) (etaL δ T T' i q.1 y)
        else 0) = locK M δ T T' q.1 i w w' := fun q => by
      rw [if_pos rfl]
      exact locK_eq_kp hA T T' i q.1 hxw hyw
    rw [Fintype.prod_congr _ _ e1, Finset.prod_coe_sort B (fun p => locK M δ T T' p i w w')]
    have hf : ∏ᶠ p, locK M δ T T' p i w w' = ∏ p ∈ B, locK M δ T T' p i w w' := by
      refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
      by_contra hpB
      exact hp (Formalism.L2.SG.DataCut.locK_eq_one Formalism.MainNotions.LocalOrbitGerms.KKAll_proved hA
        (hgood x hx w hxw p hpB) (hgood y hy w' hyw p hpB))
    rw [hf]
    have hax : aL i x = (phi i x)⁻¹ := by unfold aL; rw [hxw]
    have hay : aL i y = (phi i y)⁻¹ := by unfold aL; rw [hyw]
    rw [hax, hay]
    rw [div_eq_mul_inv, mul_inv, Complex.ofReal_inv, Complex.ofReal_inv]
    ring

end LMK

end Formalism.L2.SG.Pf.LocModel

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.DataCut

theorem resCardD_holds (D : Formalism.BasicNotions.D7) : ResCardD D := by
  intro p
  have h := LocModel.resCard_loc (D.s.atP p)
  first
  | exact h
  | simpa using h

theorem placesOver_holds (D : Formalism.BasicNotions.D7) : PlacesOver D := placesOver_of (resCardD_holds D)

theorem topUnram_holds (D : Formalism.BasicNotions.D7) : TopUnram D := by
  first
  | exact LocModel.topUnram_body D
  | (intro δ M hA T T'; exact LocModel.topUnram_body D δ M hA T T')

theorem alpBound_holds (D : Formalism.BasicNotions.D7) : AlpBound D := by
  first
  | exact LocModel.alpBound_body D
  | (intro hk u u' p; exact LocModel.alpBound_body D hk u u' p)

end Formalism.L2.SG.Pf

namespace Formalism.L2.SG.Pf

open Classical

theorem localModelK_holds (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.DataCut.LocalModelK D := by
  intro Wp Wq _ _ _ _ S δ M hA u u' _ i Y
  first
  | exact LocModel.clK_core hA _ _ i Y
  | exact LocModel.clK_core hA (D.mem u).A.T (D.mem u').A.T i Y

end Formalism.L2.SG.Pf
