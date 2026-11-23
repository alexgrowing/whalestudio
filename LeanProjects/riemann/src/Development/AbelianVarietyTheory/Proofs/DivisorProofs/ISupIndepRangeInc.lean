import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerRealizeEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGramComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalMulVecApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegAddLeDegOfIdealSmulLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.SumSlope

variable {K : Type} [Field K] [NumberField K] {O : Type} [Fintype O] [DecidableEq O] {ι : O → Type}
  [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)]

def sumNorm (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (σ : K →+* ℂ) (x : ∀ o, ι o → K) : ℝ :=
  Real.sqrt (∑ o, matNorm (Y o) σ (x o) ^ 2)

abbrev inc (o : O) : (ι o → K) →ₗ[K] (∀ o, ι o → K) := LinearMap.single K (fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem inc_injective (o : O) : Function.Injective (inc (K := K) (ι := ι) o) :=
  Pi.single_injective (M := fun o => ι o → K) o

omit [NumberField K] [Fintype O] [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] in
theorem iSupIndep_range_inc : iSupIndep fun o => LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
  have h : (⨆ p, ⨆ (_ : p ≠ o), LinearMap.range (inc (K := K) (ι := ι) p)) ≤
      LinearMap.ker (LinearMap.proj (R := K) (φ := fun o => ι o → K) o) := by
    refine iSup₂_le fun p hp => ?_
    rintro _ ⟨x, rfl⟩
    simp [Pi.single_eq_of_ne hp.symm]
  refine Submodule.disjoint_def.2 ?_
  rintro _ ⟨x, rfl⟩ hx
  have h1 : x = 0 := by simpa using h hx
  rw [h1, map_zero]

variable (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ)

omit [NumberField K] [Fintype O] [DecidableEq O] [∀ o, DecidableEq (ι o)] in
theorem matNorm_zero (o : O) (σ : K →+* ℂ) : matNorm (Y o) σ 0 = 0 := by
  have h : (fun j : ι o => σ ((0 : ι o → K) j)) = 0 := by funext j; simp
  simp only [matNorm, h, Matrix.mulVec_zero]
  simp

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_inc (o : O) (σ : K →+* ℂ) (x : ι o → K) : sumNorm Y σ (inc o x) = matNorm (Y o) σ x := by
  unfold sumNorm
  rw [Finset.sum_eq_single o]
  · simp only [LinearMap.coe_single, Pi.single_eq_same]
    exact Real.sqrt_sq (Real.sqrt_nonneg _)
  · intro p _ hp
    simp only [LinearMap.coe_single, Pi.single_eq_of_ne hp, matNorm_zero]
    simp
  · intro h; exact absurd (Finset.mem_univ o) h

omit [NumberField K] [∀ o, DecidableEq (ι o)] in
theorem sumNorm_sum (σ : K →+* ℂ) (f : O → ∀ o, ι o → K) (hf : ∀ o, f o ∈ LinearMap.range (inc (K := K) (ι := ι) o)) :
    sumNorm Y σ (∑ o, f o) ^ 2 = ∑ o, sumNorm Y σ (f o) ^ 2 := by
  choose g hg using hf
  have h : ∑ o, f o = g := by
    rw [← Finset.univ_sum_single g]
    exact Finset.sum_congr rfl fun o _ => (hg o).symm
  rw [h, sumNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun o _ => by rw [← hg o, sumNorm_inc]

theorem hasGram_sumNorm (hY : ∀ o σ, (Y o σ).det ≠ 0) : HasGram (sumNorm Y) := by
  refine GlobalTheory.OrthSumGram.orth_sum_hasGram K _ O (sumNorm Y) (fun o => LinearMap.range (inc (K := K) (ι := ι) o))
    (fun _ _ => Real.sqrt_nonneg _) iSupIndep_range_inc (LinearMap.iSup_range_single K _) (fun o => ?_)
    (fun σ f => sumNorm_sum Y σ (fun o => f o) fun o => (f o).2)
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := (isGram_matNorm K (ι o) (Y o) (hY o)).2
  let e := LinearEquiv.ofInjective (inc (K := K) (ι := ι) o) (inc_injective o)
  have h := GlobalTheory.RestrictNorm.hasGram_comp (matNorm (Y o)) e.symm.toLinearMap e.symm.injective b X hG
  convert h using 3 with σ x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact sumNorm_inc Y o σ y

theorem le_slope_sq_of_sum : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (O : Type) [Fintype O] [Nonempty O] (ι : O → Type) [∀ o, Fintype (ι o)] [∀ o, DecidableEq (ι o)] [∀ o, Nonempty (ι o)] (Nv : (K →+* ℂ) → V → ℝ) (M : Submodule (𝓞 K) V) (Y : ∀ o, (K →+* ℂ) → Matrix (ι o) (ι o) ℂ) (L : ∀ o, Submodule (𝓞 K) (ι o → K)) (Φ : (∀ o, ι o → K) →ₗ[K] V) (s : ℝ), HasGram Nv → M.FG → (∀ o σ, (Y o σ).det ≠ 0) → (∀ o, Submodule.IsLattice K (L o)) → Function.Injective Φ → (∀ x, (∀ o, x o ∈ L o) → Φ x ∈ M) → (∀ v ∈ M, v ∈ LinearMap.range Φ) → (∀ σ x, Nv σ (Φ x) ^ 2 ≤ ∑ o, matNorm (Y o) σ (x o) ^ 2) → (∀ o, s ≤ slope_sq (matNorm (Y o)) (L o)) → s ≤ slope_sq Nv M := by
  intro K _ _ _ V _ _ _ _ O _ _ ι _ _ _ Nv M Y L Φ s hNv hM hY hL hΦ hin hrg hle hs
  classical
  have hG := hasGram_sumNorm Y hY
  let P : O → Submodule (𝓞 K) (∀ o, ι o → K) := fun o => (L o).map ((inc o).restrictScalars (𝓞 K))
  have hsp : ∀ o, Submodule.span K (P o : Set (∀ o, ι o → K)) = LinearMap.range (inc (K := K) (ι := ι) o) := fun o => by
    rw [LinearMap.range_eq_map, ← (hL o).span_eq_top, ← Submodule.span_image]
    rfl
  have hP : ∀ o, (P o).FG := fun o => (hL o).fg.map _
  obtain ⟨hrk, hdeg⟩ := GlobalTheory.OrthRankDeg.rkK_deg_iSup K _ O (sumNorm Y) P hG hP
    fun σ f hf => sumNorm_sum Y σ f fun o => hsp o ▸ hf o
  have hd : ∀ o, (Formalism.HN.rkK (P o) : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (P o) := fun o => by
    obtain ⟨h1, h2⟩ := (GlobalTheory.RestrictNorm.restrict_deg K _ _ (sumNorm Y) (inc o) (inc_injective o) hG).2
      (L o) (hL o).fg
    have h3 : (fun σ x => sumNorm Y σ (inc o x)) = matNorm (Y o) := by
      funext σ x; exact sumNorm_inc Y o σ x
    rw [h3] at h2
    show (Formalism.HN.rkK ((L o).map _) : ℝ) * _ ≤ GlobalTheory.AllWt.deg _ ((L o).map _)
    rw [h1, h2, GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope]
    exact mul_le_mul_of_nonneg_left (by linarith [hs o]) (Nat.cast_nonneg _)
  have htop : Submodule.span K ((⨆ o, P o : Submodule (𝓞 K) _) : Set (∀ o, ι o → K)) = ⊤ := by
    rw [eq_top_iff, ← LinearMap.iSup_range_single K (fun o => ι o → K)]
    refine iSup_le fun o => ?_
    rw [← hsp o]
    exact Submodule.span_mono (le_iSup P o)
  have hmap : (⨆ o, P o).map (Φ.restrictScalars (𝓞 K)) ≤ M := by
    rw [Submodule.map_iSup]
    refine iSup_le fun o => ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine hin _ fun p => ?_
    by_cases hp : p = o
    · subst hp; simpa using hx
    · simp [Pi.single_eq_of_ne hp]
  have hspM : Submodule.span K (M : Set V) = LinearMap.range Φ := by
    refine le_antisymm (Submodule.span_le.2 hrg) ?_
    rw [LinearMap.range_eq_map, ← htop, ← Submodule.span_image]
    exact Submodule.span_mono hmap
  have hrkS : Formalism.HN.rkK (⨆ o, P o) = finrank K (∀ o, ι o → K) := by
    rw [Formalism.HN.rkK, htop, finrank_top]
  have hrkM : Formalism.HN.rkK M = Formalism.HN.rkK (⨆ o, P o) := by
    rw [hrkS, Formalism.HN.rkK, hspM, LinearMap.finrank_range_of_inj hΦ]
  have key := GlobalTheory.TwistIdeal.deg_add_le_deg_of_ideal_smul_le K _ V (sumNorm Y) Nv Φ (fun _ => 1) (⨆ o, P o) M ⊤ hG hNv hΦ
    (fun _ => one_pos) (fun _ => rfl)
    (fun σ x => by rw [one_mul]; exact (le_abs_self _).trans (Real.abs_le_sqrt (hle σ x)))
    (Submodule.fg_iSup _ hP) hM top_ne_bot (by rwa [Submodule.top_smul]) hrkM
  have hpos : (0 : ℝ) < Formalism.HN.rkK M := by
    rw [hrkM, hrkS]
    exact_mod_cast Module.finrank_pos
  have h1 : (Formalism.HN.rkK M : ℝ) * (s / 2) ≤ GlobalTheory.AllWt.deg (sumNorm Y) (⨆ o, P o) := by
    rw [hdeg, hrkM, hrk, Nat.cast_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun o _ => hd o
  simp only [Real.log_one, Finset.sum_const_zero, Ideal.absNorm_top, Nat.cast_one, zero_div, neg_zero, sub_zero,
    mul_zero, add_zero] at key
  have h2 := h1.trans key
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope] at h2
  have h3 := le_of_mul_le_mul_left h2 hpos
  linarith

end GlobalTheory.SumSlope

end
