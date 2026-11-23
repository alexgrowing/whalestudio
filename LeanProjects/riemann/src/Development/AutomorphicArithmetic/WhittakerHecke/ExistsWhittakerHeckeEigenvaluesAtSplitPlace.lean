import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
import Development.AutomorphicArithmetic.WhittakerHecke.RankinSelbergLocalGeneratingSeriesIdentity
import Development.AutomorphicArithmetic.WhittakerHecke.EigAtCmDatumOperatorOfEigAt
import Development.AutomorphicArithmetic.WhittakerHecke.EigenformShintaniFormulaAtPlace
import Development.AutomorphicArithmetic.WhittakerHecke.EigenformCentralUniformizerEqSatakeProduct
import Development.AutomorphicArithmetic.WhittakerHecke.IdeleEmbeddingUniformizerOfSplitPlacePair
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsLocalCharacterOfSplitPairRat
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

private theorem cp_sg_ne {E : Type} [Field E] [NumberField E] {w w' : H.P E} (hne : w ≠ w') (x : H.Kv w') :
    H.cp w (H.sg w' x) = 0 := by
  have h := ((H.sgLaws E w').2.2.2.2.2.2.2.1 x).2 w hne
  show (H.sg w' x).2 w = 0
  exact h

private theorem KAt_aE {E : Type} [Field E] [NumberField E] {w w' : H.P E} (hne : w ≠ w') (x : (H.Kv w')ˣ)
    (g : GL (Fin 2) (A E)) (hg : H.KAt w g) : H.KAt w (aE (H.idl w' x) * g) := by
  have h1 : Matrix.GeneralLinearGroup.map (H.cp w) (aE (H.idl w' x)) = 1 := by
    rw [← (H.lcLaws E w').2.2.2.1 x]
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, (H.sgLaws E w').2.2.2.2.1, map_add, cp_sg_ne hne]
    fin_cases i <;> fin_cases j <;> simp
  unfold H.KAt at hg ⊢
  rw [map_mul, h1, one_mul]
  exact hg

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w w' : H.P E, w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ hχω L N φ hA hG a hIs v hv w w' hne hw hw' hS hS' hall
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, B', hsat', hEig'⟩ := hG.fix w' (by rw [hw']; exact hv)
  obtain ⟨α', β', rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w' B').1 hsat'))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  have hEw' := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w' _ hA.cont hEig'
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_localCharacter_of_split_pair_rat E D v w w' hne hw hw' hS hS' hall (hG.pl v hv)
  obtain ⟨χw', hχ', hχe'⟩ := UpperTheory.exists_localCharacter_of_split_pair_rat E D v w' w hne.symm hw' hw hS' hS
    (fun w'' h => (hall w'' h).symm) (hG.pl v hv)
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  have hnl' : ∀ b h, Wo D φ (H.lc w' (H.nL b) * h) = χw' b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe' b
    rw [(H.lcLaws E w').1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ₁, ϖ₂, hϖ₁, hϖ₂, hz⟩ := UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair E D v w w' hne hw hw' hS hS' hall
    (atFin v (unif v)) (unif_spec v)
  have hz' : ideleEmbedding ℚ E (pv v) = H.idl w ϖ₁ * H.idl w' ϖ₂ := hz
  have hem : ∀ k : ℕ, em E (aE (pv v ^ k)) = aE (H.idl w ϖ₁ ^ k) * aE (H.idl w' ϖ₂ ^ k) := fun k => by
    rw [← UpperTheory.ConvolutionTheory.R2.aE_mul, ← mul_pow, ← hz']
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqw : H.q w = (normV v : ℂ) := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hS.1]
  have hqw' : H.q w' = (normV v : ℂ) := by
    have : H.q w' = (normV w' : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hS'.1]
  set s : ℂ := (normV v : ℂ) ^ (1 / 2 : ℂ) with hs
  have hss : s * s = (normV v : ℂ) := by
    rw [hs, ← Complex.cpow_add _ _ hqv]
    norm_num
  have hs0 : s ≠ 0 := fun h => hqv (by rw [← hss, h, zero_mul])
  refine ⟨fun k => ((s ^ k)⁻¹ * (s ^ k)⁻¹) * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
      (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)), by simp,
    fun k g hg => ?_, ?_⟩
  · have e : H.idl w' ϖ₂ ^ k = H.idl w' (ϖ₂ ^ k) := (map_pow _ _ _).symm
    have hK : H.KAt w (aE (H.idl w' ϖ₂ ^ k) * g) := by
      rw [e]
      exact KAt_aE hne _ g (hg w hw)
    have h1 := UpperTheory.eigenform_shintani_formula_at_place E w ϖ₁ hϖ₁ χw hχ α β _ hEw hnl _ hK k
    have h2 := UpperTheory.eigenform_shintani_formula_at_place E w' ϖ₂ hϖ₂ χw' hχ' α' β' _ hEw' hnl' g (hg w' hw') k
    rw [hqw] at h1
    rw [hqw'] at h2
    rw [hem, mul_assoc]
    have ht : s ^ k ≠ 0 := pow_ne_zero k hs0
    beta_reduce
    field_simp
    linear_combination s ^ k * h1 + (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) * h2
  · rintro ⟨h, hh⟩
    obtain ⟨h₁, hh₁⟩ : ∃ h₁, φ h₁ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hh
      simp [Wo, hcon]
    set c : ℂ := ((χ.val v : ℂˣ) : ℂ) with hc
    have hprod : (α : ℂ) * β * α' * β' * c ^ 2 = 1 := by
      have e1 := UpperTheory.eigenform_central_uniformizer_eq_satake_product E w ϖ₁ hϖ₁ α β φ hEig (Matrix.GeneralLinearGroup.scalar (Fin 2) (H.idl w' ϖ₂) * h₁)
      have e2 := UpperTheory.eigenform_central_uniformizer_eq_satake_product E w' ϖ₂ hϖ₂ α' β' φ hEig' h₁
      have e3 := hA.cen (ideleEmbedding ℚ E (pv v)) h₁
      rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin, hz', map_mul, mul_assoc, e1, e2] at e3
      have e4 : ((ω.1 (pv v) : ℂˣ) : ℂ) ^ 2 = (α : ℂ) * β * α' * β' := by
        have : ((α : ℂ) * β * α' * β' - ((ω.1 (pv v) : ℂˣ) : ℂ) ^ 2) * φ h₁ = 0 := by
          rw [map_pow, Units.val_pow_eq_pow_val] at e3
          linear_combination e3
        rcases mul_eq_zero.1 this with h0 | h0
        · linear_combination -h0
        · exact absurd h0 hh₁
      have e5 := congrArg (fun u : ℂˣ => (u : ℂ)) (hχω (pv v))
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one] at e5
      have e6 : c = ((χ.1 (pv v) : ℂˣ) : ℂ) := rfl
      rw [e6, ← e4]
      linear_combination e5
    have hsp := hIs.split v hv w w' hne hw hw' α β α' β' hsat hsat'
    have h2 := UpperTheory.rankinSelberg_local_generating_series_identity α β α' β' c
    rw [hprod, map_one, one_mul] at h2
    simp only [Units.val_mul, ← hc] at hsp
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * c ^ k *
        (((s ^ k)⁻¹ * (s ^ k)⁻¹) * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)))) =
        PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i)) := by
      congr 1
      funext k
      have ht : s ^ k ≠ 0 := pow_ne_zero k hs0
      have hp : ((normV v ^ k : ℕ) : ℂ) = s ^ k * s ^ k := by
        rw [Nat.cast_pow, ← hss, mul_pow]
      rw [hp]
      field_simp
    rw [h3]
    linear_combination (PowerSeries.mk fun k => a (normV v ^ k)) * (-1 : PowerSeries ℂ) * h2 +
      (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i)) *
          (∑ i ∈ Finset.range (k + 1), (α' : ℂ) ^ i * (β' : ℂ) ^ (k - i))) * hsp
