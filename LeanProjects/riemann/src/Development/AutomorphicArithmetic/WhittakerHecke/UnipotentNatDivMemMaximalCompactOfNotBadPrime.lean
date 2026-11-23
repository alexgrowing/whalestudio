import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v 2 := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : H.Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma map_gl_nU {K : Type} [Field K] [NumberField K] (v : H.P K) (z : A K) :
    Matrix.GeneralLinearGroup.map (H.cp v) (gl (nU z)) = H.nL (H.cp v z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact map_one (H.cp v)
  · rfl
  · exact map_zero (H.cp v)
  · exact map_one (H.cp v)

private lemma val_nat_one {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (hL : (L : 𝓞 E) ∉ w.asIdeal) : Valued.v (L : H.Kv w) = 1 := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (L : 𝓞 E)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hL] at h1
  simpa using h1

private lemma val_nat_le {E : Type} [Field E] [NumberField E] (w : H.P E) (a : ℕ) :
    Valued.v (a : H.Kv w) ≤ 1 :=
  show (a : H.Kv w) ∈ w.adicCompletionIntegers E from natCast_mem _ a

private lemma not_mem_of_bad {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (h : ¬ Bad L (w.under (𝓞 ℚ))) : (L : 𝓞 E) ∉ w.asIdeal := by
  intro hm
  apply h
  show (L : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal
  change (L : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact hm

private lemma cp_iota (v : H.P ℚ) (L : ℕ) : H.cp v (iota L) = (L : H.Kv v)⁻¹ := by
  have h := eq_ratCast ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹
  have e : H.cp v (iota L) = ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹ := rfl
  rw [e, h]
  push_cast
  rfl

private lemma completion_adele_natural {E : Type} [Field E] [NumberField E] (w : H.P E) (L a : ℕ) :
    H.cp w (AdeleBaseChange.adeleMap ℚ E ((a : A ℚ) * iota L)) = (a : H.Kv w) * (L : H.Kv w)⁻¹ := by
  have h : ((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w) =
      (a : H.Kv (AdeleBaseChange.below ℚ w)) * (L : H.Kv (AdeleBaseChange.below ℚ w))⁻¹ := by
    have := map_mul (H.cp (AdeleBaseChange.below ℚ w)) (a : A ℚ) (iota L)
    rw [cp_iota, map_natCast] at this
    exact this
  show SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w)) = _
  rw [h, map_mul, map_inv₀, map_natCast, map_natCast]

theorem UpperTheory.unipotent_natDiv_mem_maximalCompact_of_not_badPrime :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ) (w : H.P E), ¬ Bad L (w.under (𝓞 ℚ)) → Valued.v (H.cp w (rt D.θ)) ≤ 1 → H.KAt w (nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a w hL hθ
  have hL1 := val_nat_one w L (not_mem_of_bad w L hL)
  have hz : Valued.v (H.cp w (D.mkE 0 ((a : A ℚ) * iota L))) ≤ 1 := by
    rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, completion_adele_natural, map_mul, map_inv₀, hL1, inv_one, mul_one]
    calc _ ≤ (1 : _) * 1 := mul_le_mul' (val_nat_le w a) hθ
      _ = 1 := mul_one 1
  show Matrix.GeneralLinearGroup.map (H.cp w) (gl (nU (D.mkE 0 ((a : A ℚ) * iota L)))) ∈ GlobalTheory.LFun.KGL w 2
  rw [map_gl_nU]
  exact nL_memK hz
