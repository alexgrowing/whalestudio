import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocIntegral

open Polynomial
open scoped WithZero

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}

theorem exists_valued_eq (γ : ℤᵐ⁰) : ∃ c : v.adicCompletion K, Valued.v c = γ := by
  obtain ⟨x, hx⟩ := v.valuation_surjective K γ
  exact ⟨algebraMap K _ x, (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).trans hx⟩

theorem valued_coeff_minpoly_le_one (e : ℕ) (he : 0 < e)
    (f : v.adicCompletion K →+* v'.adicCompletion L)
    (hfv : ∀ y, Valued.v (f y) = Valued.v y ^ e) :
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ x : v'.adicCompletion L, Valued.v x ≤ 1 →
      ∀ n, Valued.v ((minpoly (v.adicCompletion K) x).coeff n) ≤ 1 := by
  letI := f.toAlgebra
  intro hfd x hx n
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰
  haveI : IsUltrametricDist (v.adicCompletion K) :=
    inferInstanceAs (@IsUltrametricDist (v.adicCompletion K)
      (Valued.toNormedField (v.adicCompletion K) ℤᵐ⁰).toDist)
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  choose c hc using (exists_valued_eq (v := v) : ∀ γ : ℤᵐ⁰, ∃ c : v.adicCompletion K, Valued.v c = γ)
  have hmono : ∀ a b : v.adicCompletion K, Valued.v a ≤ Valued.v b → ‖a‖ ≤ ‖b‖ :=
    fun a b h => Valued.toNormedField.norm_le_iff.2 h
  have hnorm : ∀ a b : v.adicCompletion K, Valued.v a = Valued.v b → ‖a‖ = ‖b‖ :=
    fun a b h => le_antisymm (hmono a b h.le) (hmono b a h.ge)
  have he' : (e : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  let ρ : v'.adicCompletion L → ℝ := fun z => ‖c (Valued.v z)‖ ^ ((e : ℝ)⁻¹)
  have ρ_nonneg : ∀ z, 0 ≤ ρ z := fun z => Real.rpow_nonneg (norm_nonneg _) _
  have ρ_mul : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    simp only [ρ]
    rw [← Real.mul_rpow (norm_nonneg _) (norm_nonneg _), ← norm_mul]
    congr 1
    apply hnorm
    rw [hc, Valuation.map_mul, Valuation.map_mul, hc, hc]
  have ρ_le : ∀ a b, Valued.v a ≤ Valued.v b → ρ a ≤ ρ b := by
    intro a b h
    exact Real.rpow_le_rpow (norm_nonneg _) (hmono _ _ (by rw [hc, hc]; exact h))
      (inv_nonneg.2 (Nat.cast_nonneg _))
  have ρ_zero : ρ 0 = 0 := by
    simp only [ρ]
    have : c (Valued.v (0 : v'.adicCompletion L)) = 0 := by
      rw [← Valuation.zero_iff Valued.v, hc, Valuation.map_zero]
    rw [this, norm_zero, Real.zero_rpow he']
  have ρ_eq_zero : ∀ z, ρ z = 0 → z = 0 := by
    intro z hz
    simp only [ρ] at hz
    rw [Real.rpow_eq_zero (norm_nonneg _) he', norm_eq_zero] at hz
    have := hc (Valued.v z)
    rw [hz, Valuation.map_zero] at this
    exact (Valuation.zero_iff _).1 this.symm
  have ρ_f : ∀ a, ρ (f a) = ‖a‖ := by
    intro a
    simp only [ρ]
    rw [hnorm _ (a ^ e) (by rw [hc, hfv, Valuation.map_pow]), norm_pow,
      Real.pow_rpow_inv_natCast (norm_nonneg _) he.ne']
  have ρ_one : ρ 1 = 1 := by
    have := ρ_f 1
    rwa [map_one, norm_one] at this
  let N : AlgebraNorm (v.adicCompletion K) (v'.adicCompletion L) :=
    { toFun := ρ
      map_zero' := ρ_zero
      add_le' := fun a b => by
        rcases le_total (Valued.v a) (Valued.v b) with h | h
        · have := ρ_le (a + b) b ((Valuation.map_add _ a b).trans (max_le h le_rfl))
          linarith [ρ_nonneg a]
        · have := ρ_le (a + b) a ((Valuation.map_add _ a b).trans (max_le le_rfl h))
          linarith [ρ_nonneg b]
      neg' := fun a => by simp only [ρ, Valuation.map_neg]
      mul_le' := fun a b => (ρ_mul a b).le
      eq_zero_of_map_eq_zero' := ρ_eq_zero
      smul' := fun a z => by
        rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, ρ_mul, ρ_f] }
  have hN : ∀ z, N z = ρ z := fun _ => rfl
  have hpm : IsPowMul N := by
    intro a k hk
    clear hk
    rw [hN, hN]
    induction k with
    | zero => simp [ρ_one]
    | succ k ih => rw [pow_succ, ρ_mul, ih, pow_succ]
  have hu := spectralNorm_unique (K := v.adicCompletion K) (L := v'.adicCompletion L) hpm
  have hsx : spectralNorm (v.adicCompletion K) (v'.adicCompletion L) x ≤ 1 := by
    rw [← spectralAlgNorm_def, ← hu, hN, ← ρ_one]
    exact ρ_le x 1 (by rw [Valuation.map_one]; exact hx)
  have hxi : IsIntegral (v.adicCompletion K) x := Algebra.IsIntegral.isIntegral x
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hxi)] at hsx
  exact Valued.toNormedField.norm_le_one_iff.1 (hsx n)

end GlobalTheory.LocIntegral

namespace GlobalTheory.LocIntegral

open Polynomial

theorem isIntegral_iff_isIntegral_map : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ)
    (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e →
    (∀ y, Valued.v (f y) = Valued.v y ^ e) →
    letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) →
    ∀ b₀ : Kbar v ≃+* Kbar v',
      (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) =
        algebraMap (v'.adicCompletion L) (Kbar v') (f x)) →
      ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔
        IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  intro K L _ _ _ _ v v' e f he hfv
  letI := f.toAlgebra
  intro hfd b₀ hb y
  have hle : ∀ a ∈ v.adicCompletionIntegers K, f a ∈ v'.adicCompletionIntegers L := by
    intro a ha
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hfv]
    exact pow_le_one₀ zero_le' ha
  let g : v.adicCompletionIntegers K →+* v'.adicCompletionIntegers L :=
    f.restrict (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) hle
  have hg : ∀ a, ((g a : v'.adicCompletionIntegers L) : v'.adicCompletion L) = f a := fun _ => rfl
  have hcomp : (algebraMap (v'.adicCompletionIntegers L) (Kbar v')).comp g =
      b₀.toRingHom.comp (algebraMap (v.adicCompletionIntegers K) (Kbar v)) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K) (Kbar v),
      IsScalarTower.algebraMap_apply (v'.adicCompletionIntegers L) (v'.adicCompletion L) (Kbar v'),
      hb]
    rfl
  constructor
  · intro hy
    exact IsIntegral.map_of_comp_eq g b₀.toRingHom hcomp hy
  · intro hy
    letI alg1 : Algebra (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := g.toAlgebra
    letI alg2 : Algebra (v'.adicCompletionIntegers L) (Kbar v) :=
      (b₀.symm.toRingHom.comp (algebraMap (v'.adicCompletionIntegers L) (Kbar v'))).toAlgebra
    haveI : IsScalarTower (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) (Kbar v) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      have h := congrArg (fun φ => b₀.symm (φ a)) hcomp
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] at h
      rw [← h]
      rfl
    haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L) := by
      constructor
      intro a
      have ha : Valued.v (a : v'.adicCompletion L) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2
      have hc := valued_coeff_minpoly_le_one e he f hfv hfd (a : v'.adicCompletion L) ha
      have hai : IsIntegral (v.adicCompletion K) (a : v'.adicCompletion L) :=
        Algebra.IsIntegral.isIntegral _
      have hl : minpoly (v.adicCompletion K) (a : v'.adicCompletion L) ∈
          Polynomial.lifts (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        exact ⟨⟨_, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hc n)⟩, rfl⟩
      obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (minpoly.monic hai)
      refine ⟨q, hm, ?_⟩
      apply Subtype.ext
      have e1 := Polynomial.hom_eval₂ q (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L))
        (v'.adicCompletionIntegers L).subtype a
      have e2 : ((v'.adicCompletionIntegers L).subtype).comp
          (algebraMap (v.adicCompletionIntegers K) (v'.adicCompletionIntegers L)) =
          (algebraMap (v.adicCompletion K) (v'.adicCompletion L)).comp
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
        ext; rfl
      rw [e2, ← Polynomial.eval₂_map, hq] at e1
      exact e1.trans (minpoly.aeval (v.adicCompletion K) (a : v'.adicCompletion L))
    have h1 : IsIntegral (v'.adicCompletionIntegers L) y := by
      have := IsIntegral.map_of_comp_eq (RingHom.id (v'.adicCompletionIntegers L)) b₀.symm.toRingHom
        (by ext; rfl) hy
      simpa using this
    exact isIntegral_trans y h1

end GlobalTheory.LocIntegral
