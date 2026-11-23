import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogISupInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsEqISup

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.GaussFrac

variable {F : Type} [Field F] [NumberField F]

def scaledIdeal (c : 𝓞 F) (I : Submodule (𝓞 F) F) : Ideal (𝓞 F) :=
  (I.map (LinearMap.lsmul (𝓞 F) F c)).comap (Algebra.linearMap (𝓞 F) F)

theorem absNorm_span_eq (c : 𝓞 F) (hc : c ≠ 0) (I : Submodule (𝓞 F) F) (h1I : 1 ≤ I)
    (hcI : ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) :
    Ideal.absNorm (Ideal.span {c}) =
      (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup * Ideal.absNorm (scaledIdeal c I) := by
  set ι : 𝓞 F →+ F := (Algebra.linearMap (𝓞 F) F).toAddMonoidHom
  set φ : F →+ F := (LinearMap.lsmul (𝓞 F) F c).toAddMonoidHom
  set A := (1 : Submodule (𝓞 F) F).toAddSubgroup
  set B := I.toAddSubgroup
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hφ : Function.Injective φ := fun x y h => by
    simp only [φ, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply] at h
    have h' : (c : F) * x = (c : F) * y := by simpa [Algebra.smul_def] using h
    exact mul_left_cancel₀ hc' h'
  have hA : (⊤ : AddSubgroup (𝓞 F)).map ι = A := by
    ext x; simp [ι, A, Submodule.mem_one]
  have hAB : A ≤ B := h1I
  have hBA : B.map φ ≤ A := by
    rintro _ ⟨y, hy, rfl⟩; exact hcI y hy
  have hAA : A.map φ ≤ B.map φ := AddSubgroup.map_mono hAB
  have e1 : (A.map φ).comap ι = (Ideal.span {c}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, A, Submodule.mem_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, h⟩
      refine ⟨y, ?_⟩
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def] at h
      rw [map_mul, ← h, mul_comm]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨y, rfl⟩, ?_⟩
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def]
      rw [map_mul, mul_comm]
  have e2 : (B.map φ).comap ι = (scaledIdeal c I).toAddSubgroup := by
    ext a; rfl
  have k := AddSubgroup.relIndex_mul_relIndex _ _ _ hAA hBA
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hφ] at k
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot, ← e1, ← e2,
    ← AddSubgroup.relIndex_top_right, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap,
    AddSubgroup.relIndex_comap, hA, ← k]

theorem finsum_log_gaussAbs_le : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 →
    ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, coeff m g / δ ∈ I) →
    ∑ᶠ q : FinitePlace F, Real.log (gaussAbs q g) ≤
      Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) +
        ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  intro F _ _ τ g hg I δ hδ h1I ⟨c, hc, hcI⟩ hcoef
  classical
  have hne : g.support.Nonempty := MvPolynomial.support_nonempty.2 hg
  set n := g.support.card
  set e := g.support.equivFin
  have hz : ∀ i : Fin n, ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c • (coeff (e.symm i : τ →₀ ℕ) g / δ) :=
    fun i => Submodule.mem_one.1 (hcI _ (hcoef _))
  choose b hb using hz
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hb' : ∀ i, (b i : F) = (c : F) * (coeff (e.symm i : τ →₀ ℕ) g / δ) := fun i => by
    simpa [Algebra.smul_def] using hb i
  have hcoeff : ∀ i : Fin n, coeff (e.symm i : τ →₀ ℕ) g = δ * ((b i : F) / c) := by
    intro i
    rw [hb' i]
    field_simp
  obtain ⟨m₀, hm₀⟩ := hne
  set i₀ := e ⟨m₀, hm₀⟩
  have hbi₀ : (b i₀ : F) ≠ 0 := by
    rw [hb' i₀]
    refine mul_ne_zero hc' (div_ne_zero ?_ hδ)
    simpa [i₀] using MvPolynomial.mem_support_iff.1 hm₀
  have hb0 : b ≠ 0 := Function.ne_iff.2 ⟨i₀, fun h => hbi₀ (by rw [h]; rfl)⟩
  have hz0 : (fun i => (b i : F) / c) ≠ 0 := Function.ne_iff.2 ⟨i₀, div_ne_zero hbi₀ hc'⟩
  have hloc : ∀ q : FinitePlace F, Real.log (gaussAbs q g) =
      Real.log (q δ) + Real.log (⨆ i, q ((b i : F) / c)) := by
    intro q
    have hpos : 0 < ⨆ i, q ((b i : F) / c) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 (div_ne_zero hbi₀ hc'))
        (le_ciSup (f := fun i => q ((b i : F) / c)) (Set.finite_range _).bddAbove i₀)
    have hqδ : 0 < q δ := FinitePlace.pos_iff.2 hδ
    rw [← Real.log_mul hqδ.ne' hpos.ne', GlobalTheory.HSChoice.BaseChange.gaussAbs_eq_iSup q g g.support subset_rfl ⟨m₀, hm₀⟩,
      ← e.symm.iSup_comp, Real.mul_iSup_of_nonneg hqδ.le]
    congr 1
    refine iSup_congr fun i => ?_
    rw [hcoeff i, map_mul]
  have hs1 : (Function.support fun q : FinitePlace F => Real.log (q δ)).Finite :=
    (FinitePlace.hasFiniteMulSupport hδ).subset (by
      intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one])
  have hs2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz0
  rw [finsum_congr hloc, finsum_add_distrib hs1 hs2, GlobalTheory.HSCore.RankOne.finsum_log_iSup_div hb0 hc,
    GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI]
  have hcN : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  rw [GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI] at hcN
  have hR : (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 := left_ne_zero_of_mul hcN
  have hJ : Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) ≠ 0 := right_ne_zero_of_mul hcN
  have hle : Ideal.span (Set.range b) ≤ GlobalTheory.GaussFrac.scaledIdeal c I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 F) F (b i) ∈ I.map (LinearMap.lsmul (𝓞 F) F c)
    exact ⟨_, hcoef _, (hb i).symm⟩
  have hN : Ideal.absNorm (Ideal.span (Set.range b)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_eq_bot]
    intro h
    exact hbi₀ (by rw [h _ ⟨i₀, rfl⟩]; rfl)
  have hdvd := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Ideal.absNorm_dvd_absNorm_of_le hle)
  push_cast
  rw [Real.log_mul (by exact_mod_cast hR) (by exact_mod_cast hJ)]
  have := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hJ) (show (Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) : ℝ) ≤ Ideal.absNorm (Ideal.span (Set.range b)) by exact_mod_cast hdvd)
  linarith

end GlobalTheory.GaussFrac
