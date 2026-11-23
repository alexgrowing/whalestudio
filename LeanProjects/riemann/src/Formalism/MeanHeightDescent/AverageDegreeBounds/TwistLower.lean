import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

open scoped Pointwise

section

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]

theorem covol_of_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N M : Submodule (𝓞 K) V) (hN : N.FG) (hM : M.FG) (hle : N ≤ M)
    (hrk : rkK N = rkK M) :
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) =
      (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
  obtain ⟨hMlat, hrkM, -⟩ := place_lattice_structure K V ι b X hX M hM
  obtain ⟨-, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hN
  have := hMlat.2
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b X) N ≤ zl (Formalism.HermitianLatticesTheory.realize b X) M := shiftInv_zl_mono _ hle
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) N) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
    have h1 : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) M := by
      rw [hrkN, hrkM, hrk]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _ hzl hrkeq
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : (zl (Formalism.HermitianLatticesTheory.realize b X) N).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) M).toAddSubgroup = N.toAddSubgroup.relIndex M.toAddSubgroup := by
    simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  rw [hcov, hidx]

theorem covol_ideal_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG) (𝔟 : Ideal (𝓞 K))
    (h𝔟 : 𝔟 ≠ ⊥) :
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) (𝔟 • M)) =
      (Ideal.absNorm 𝔟 : ℝ) ^ rkK M * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hfg : (𝔟 • M).FG := Submodule.FG.smul (IsNoetherian.noetherian 𝔟) hM
  have hrk : rkK (𝔟 • M) = rkK M := by
    unfold rkK
    rw [Formalism.HN.DualPolygon.twist_span_smul M 𝔟 h𝔟]
  rw [covol_of_le b X hX (𝔟 • M) M hfg hM Submodule.smul_le_right hrk,
    Formalism.HN.DualPolygon.twist_index M hM 𝔟 h𝔟, Nat.cast_pow]
  rfl

omit [StarRing K] [IsTotallyComplex K] in

theorem den_smul_idealSmul (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (M : Submodule (𝓞 K) V) :
    (Ideal.span {(I.den : 𝓞 K)}) • Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M = I.num • M := by
  have hmem : ∀ a ∈ (I : Submodule (𝓞 K) K), ∃ c ∈ I.num,
      (algebraMap (𝓞 K) K c) = (I.den : 𝓞 K) • a := by
    intro a ha
    have h1 : I.den • a ∈ I.den • (I : Submodule (𝓞 K) K) := Submodule.smul_mem_pointwise_smul a I.den _ ha
    rw [FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨c, hc, hca⟩ := h1
    exact ⟨c, hc, hca⟩
  have hmem2 : ∀ c ∈ I.num, ∃ a ∈ (I : Submodule (𝓞 K) K),
      (I.den : 𝓞 K) • a = algebraMap (𝓞 K) K c := by
    intro c hc
    have h1 : algebraMap (𝓞 K) K c ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := ⟨c, hc, rfl⟩
    rw [← FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨a, ha, hax⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact ⟨a, ha, hax⟩
  unfold Formalism.HermitianLatticesTheory.idealSmul
  rw [Submodule.ideal_span_singleton_smul]
  apply le_antisymm
  · have key : Submodule.span (𝓞 K) {z | ∃ a ∈ (I : Submodule (𝓞 K) K), ∃ x ∈ M, z = a • x} ≤
        (I.num • M).comap (LinearMap.lsmul (𝓞 K) V (I.den : 𝓞 K)) := by
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, x, hx, rfl⟩
      obtain ⟨c, hc, hca⟩ := hmem a ha
      show (I.den : 𝓞 K) • (a • x) ∈ I.num • M
      rw [← smul_assoc, ← hca, algebraMap_smul]
      exact Submodule.smul_mem_smul hc hx
    rintro _ ⟨n, hn, rfl⟩
    exact key hn
  · rw [Submodule.smul_le]
    intro c hc x hx
    obtain ⟨a, ha, hax⟩ := hmem2 c hc
    have h1 : a • x ∈ Submodule.span (𝓞 K) {z | ∃ a ∈ (I : Submodule (𝓞 K) K), ∃ x ∈ M, z = a • x} :=
      Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
    have h2 := Submodule.smul_mem_pointwise_smul (a • x) (I.den : 𝓞 K) _ h1
    rw [← smul_assoc, hax, algebraMap_smul] at h2
    exact h2

omit [StarRing K] [IsTotallyComplex K] in
theorem rkK_pos' (M : Submodule (𝓞 K) V) (hM0 : M ≠ ⊥) [FiniteDimensional K V] : 0 < rkK (K := K) M := by
  unfold rkK
  apply Nat.pos_of_ne_zero
  intro h
  apply hM0
  rw [Submodule.finrank_eq_zero] at h
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ Submodule.span K (M : Set V) := Submodule.subset_span hx
  rw [h] at hx'
  exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot K).mp hx')

theorem muDef_eq_covol (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    muDef b X M = 2 * (-Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M)) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ))) - Real.log 2 +
        logDisc K / (Module.finrank ℚ K : ℝ) := by
  obtain ⟨-, hrkM, -⟩ := place_lattice_structure K V ι b X hX M hM
  have h1 : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) M) = Module.finrank ℚ K * rkK M := hrkM
  unfold muDef Formalism.HN.slope Formalism.F.slope Formalism.F.deg
  rw [h1]
  push_cast
  rfl

theorem idealScale_mu (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI : I ≠ 0)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hM0 : M ≠ ⊥) :
    (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M).FG ∧
      rkK (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) = rkK M ∧
      muDef b X (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M) =
        muDef b X M - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  set N := Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) M with hNdef
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero I.den
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h0
    exact hd0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
  have hJ : I.num ≠ ⊥ := fun h => hI (FractionalIdeal.num_eq_zero_iff.1 h)
  have hD : Ideal.span {d} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hd0
  have heq : Ideal.span {d} • N = I.num • M := den_smul_idealSmul I M
  have heq' : d • N = I.num • M := by rw [← heq, Submodule.ideal_span_singleton_smul]
  let ψ : V →ₗ[𝓞 K] V :=
    (((algebraMap (𝓞 K) K d)⁻¹ • LinearMap.id : V →ₗ[K] V)).restrictScalars (𝓞 K)
  have hψ : ∀ z : V, ψ (d • z) = z := by
    intro z
    show (algebraMap (𝓞 K) K d)⁻¹ • (d • z) = z
    rw [← algebraMap_smul K d z, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  have hNmap : N = (I.num • M).map ψ := by
    ext z
    constructor
    · intro hz
      refine ⟨d • z, ?_, hψ z⟩
      rw [← heq']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hz
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, ← heq'] at hy
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      rw [hψ]
      exact hz
  have hNfg : N.FG := by
    rw [hNmap]
    exact (Submodule.FG.smul (IsNoetherian.noetherian I.num) hM).map _
  have hrk : rkK N = rkK M := by
    unfold rkK
    rw [← Formalism.HN.DualPolygon.twist_span_smul N _ hD, heq, Formalism.HN.DualPolygon.twist_span_smul M _ hJ]
  refine ⟨hNfg, hrk, ?_⟩
  have c1 := covol_ideal_smul b X hX N hNfg _ hD
  have c2 := covol_ideal_smul b X hX M hM _ hJ
  rw [heq, c2, hrk] at c1
  obtain ⟨hMlat, -, -⟩ := place_lattice_structure K V ι b X hX M hM
  obtain ⟨hNlat, -, -⟩ := place_lattice_structure K V ι b X hX N hNfg
  have hcM := Formalism.F.covolPos _ _ hMlat.2
  have hcN := Formalism.F.covolPos _ _ hNlat.2
  have hr : (0 : ℝ) < rkK M := by exact_mod_cast rkK_pos' M hM0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hJpos : (0 : ℝ) < (Ideal.absNorm I.num : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h))
  have hDpos : (0 : ℝ) < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hD (Ideal.absNorm_eq_zero_iff.1 h))
  have hnorm : ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      (Ideal.absNorm I.num : ℝ) / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    rw [FractionalIdeal.absNorm_eq, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl
  have hlog := congrArg Real.log c1
  rw [Real.log_mul (pow_pos hJpos _).ne' hcM.ne', Real.log_mul (pow_pos hDpos _).ne' hcN.ne',
    Real.log_pow, Real.log_pow] at hlog
  rw [muDef_eq_covol b X hX N hNfg, muDef_eq_covol b X hX M hM, hrk, hnorm,
    Real.log_div hJpos.ne' hDpos.ne']
  have hcNeq : Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N)) =
      (rkK M : ℝ) * Real.log (Ideal.absNorm I.num : ℝ) +
        Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M)) -
        (rkK M : ℝ) * Real.log (Ideal.absNorm (Ideal.span {d}) : ℝ) := by linarith
  rw [hcNeq]
  field_simp
  ring

end

theorem twist_lower_bound : TwistLower := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B I hI hAfg hBfg hA0 hinj
    hle hrkBA
  have : FiniteDimensional K W := Module.Finite.of_basis b'
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set A' := A.map (φ.restrictScalars (𝓞 K)) with hA'def
  have hA'fg : A'.FG := hAfg.map _
  have hA'0 : A' ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ A' := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hNfg, hrkN, hmuN⟩ := idealScale_mu b' X' hX' I hI A' hA'fg hA'0
  set N := Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) A' with hNdef
  have hrkNB : rkK N = rkK B := by rw [hrkN, hrkeq, hrkBA]
  have hcov := covol_of_le b' X' hX' N B hNfg hBfg hle hrkNB
  obtain ⟨hBlat, -, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨hNlat, -, -⟩ := place_lattice_structure K W κ b' X' hX' N hNfg
  have hcB := Formalism.F.covolPos _ _ hBlat.2
  have hcN := Formalism.F.covolPos _ _ hNlat.2
  have hidx : (1 : ℝ) ≤ (N.toAddSubgroup.relIndex B.toAddSubgroup : ℝ) := by
    rcases Nat.eq_zero_or_pos (N.toAddSubgroup.relIndex B.toAddSubgroup) with h | h
    · rw [h, Nat.cast_zero, zero_mul] at hcov
      exact absurd hcov hcN.ne'
    · exact_mod_cast h
  have hcle : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') B) ≤
      Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') N) := by
    rw [hcov]
    nlinarith
  have hlogle := Real.log_le_log hcB hcle
  have hr : (0 : ℝ) < rkK B := by
    rw [← hrkNB, hrkN]
    exact_mod_cast rkK_pos' A' hA'0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hmuNB : muDef b' X' N ≤ muDef b' X' B := by
    rw [muDef_eq_covol b' X' hX' N hNfg, muDef_eq_covol b' X' hX' B hBfg, hrkNB]
    have : -Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') N)) /
        ((Module.finrank ℚ K : ℝ) * (rkK B : ℝ)) ≤
        -Real.log (Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b' X') B)) /
        ((Module.finrank ℚ K : ℝ) * (rkK B : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hmuA : muDef b X A - htMap b X b' X' φ ≤ muDef b' X' A' := by
    unfold muDef
    linarith
  linarith

end Formalism.ExtensionFiltration
