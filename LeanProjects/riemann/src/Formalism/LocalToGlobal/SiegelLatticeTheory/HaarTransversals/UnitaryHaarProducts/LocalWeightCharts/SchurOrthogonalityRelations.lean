import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed

noncomputable section

namespace WlocSk.Port

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep

section Transport

variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)

def conjPrime₂ (g : UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (P⁻¹ * toM g * P)

lemma conjP_isClosedEmbedding (hP : IsUnit P) : IsClosedEmbedding (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₜ (Fin n → Fin n → ℂ) :=
    { toFun := fun m => Matrix.of.symm (P⁻¹ * m * P)
      invFun := fun x => P * Matrix.of x * P⁻¹
      left_inv := fun m => by
        show P * (P⁻¹ * m * P) * P⁻¹ = m
        calc P * (P⁻¹ * m * P) * P⁻¹ = (P * P⁻¹) * m * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = m := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun x => by
        show P⁻¹ * (P * Matrix.of x * P⁻¹) * P = Matrix.of x
        calc P⁻¹ * (P * Matrix.of x * P⁻¹) * P = (P⁻¹ * P) * Matrix.of x * (P⁻¹ * P) := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.of x := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := by
        show Continuous fun m : Matrix (Fin n) (Fin n) ℂ => P⁻¹ * m * P
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := by
        show Continuous fun x : Fin n → Fin n → ℂ => P * Matrix.of x * P⁻¹
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact e.isClosedEmbedding.comp (isClosedEmbeddingMatrix n ε).1

lemma conjP_measurableEmbedding (hP : IsUnit P) : MeasurableEmbedding (conjPrime₂ ε P) :=
  (conjP_isClosedEmbedding ε P hP).measurableEmbedding

theorem haar_transport (hP : IsUnit P) (μ : Measure (Fin n → Fin n → ℂ)) [SigmaFinite μ] (h0 : μ ≠ 0)
    (hconc : μ {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0)
    (hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μ.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = (c • muG ε).map (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hE := conjP_measurableEmbedding ε P hP
  set ψ := conjPrime₂ ε P with hψdef

  have hrange : {x : Fin n → Fin n → ℂ | Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)} ⊆ Set.range ψ := by
    intro x hx
    have hx' : (Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x = Pᴴ * Jm ε * P := hx
    have hin : inUJ ε (P * Matrix.of x * P⁻¹) := by
      show (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹) = Jm ε
      calc (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹)
          = (P⁻¹)ᴴ * ((Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x) * P⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P⁻¹ := by rw [hx']
        _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Jm ε := by rw [h2]; simp
    have hr := (isClosedEmbeddingMatrix n ε).2
    have hmem : P * Matrix.of x * P⁻¹ ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hr]; exact hin
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    show Matrix.of.symm (P⁻¹ * toM g * P) = x
    have hg' : toM g = P * Matrix.of x * P⁻¹ := hg
    rw [hg']
    calc Matrix.of.symm (P⁻¹ * (P * Matrix.of x * P⁻¹) * P)
        = Matrix.of.symm ((P⁻¹ * P) * Matrix.of x * (P⁻¹ * P)) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h1, Matrix.one_mul, Matrix.mul_one]; rfl

  have hinto : ∀ g : UJ ε, P⁻¹ * toM g * P ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
    intro g
    have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
    show (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P) = Pᴴ * Jm ε * P
    have hPP : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
    calc (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P)
        = Pᴴ * (toM g)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * toM g * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * ((toM g)ᴴ * Jm ε * toM g) * P := by
          rw [hPP, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Pᴴ * Jm ε * P := by rw [hg]

  set ν := μ.comap ψ with hνdef
  have hmapν : ν.map ψ = μ := by
    rw [hνdef, hE.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    refine measure_mono_null ?_ hconc
    intro x hx
    by_contra hc
    have hc' : Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
      by_contra h'
      exact hc h'
    exact hx (hrange hc')
  have hσν : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmapν]; infer_instance)
  have hinj : ∀ a b : Measure (UJ ε), a.map ψ = b.map ψ → a = b := by
    intro a b hab
    rw [← hE.comap_map a, ← hE.comap_map b, hab]
  have hleft : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    apply hinj
    have hcomp : ψ ∘ (fun h : UJ ε => g * h) =
        (fun x => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) ∘ ψ := by
      funext h
      show Matrix.of.symm (P⁻¹ * toM (g * h) * P) =
        Matrix.of.symm ((P⁻¹ * toM g * P) * (P⁻¹ * toM h * P))
      congr 1
      show P⁻¹ * (toM g * toM h) * P = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P)
      calc P⁻¹ * (toM g * toM h) * P = P⁻¹ * toM g * (P * P⁻¹) * toM h * P := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P) := by simp only [Matrix.mul_assoc]
    have hmul : Measurable (fun h : UJ ε => g * h) := measurable_const_mul g
    have hlm : Measurable (fun x : Fin n → Fin n → ℂ => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) := by
      apply Continuous.measurable
      show Continuous fun x : Fin n → Fin n → ℂ => (P⁻¹ * toM g * P) * Matrix.of x
      exact continuous_const.matrix_mul continuous_id
    rw [Measure.map_map hE.measurable hmul, hcomp, ← Measure.map_map hlm hE.measurable, hmapν]
    exact hinv _ (hinto g)

  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : UJ ε)
  have hK0 : muG ε K ≠ 0 := (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne'
  have hKt : muG ε K ≠ ∞ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul ν (muG ε) hK0 hKt
  set c := ν K / muG ε K with hc
  have hcne0 : c ≠ 0 := by
    intro h
    apply h0
    rw [← hmapν, heq, h, zero_smul, Measure.map_zero]
  have hcnetop : c ≠ ∞ := by
    intro h
    have hnull : ∀ i, muG ε (spanningSets ν i) = 0 := by
      intro i
      have hlt := measure_spanningSets_lt_top ν i
      have hS : ν (spanningSets ν i) = (c • muG ε) (spanningSets ν i) :=
        congrArg (fun m : Measure (UJ ε) => m (spanningSets ν i)) heq
      rw [hS, Measure.smul_apply, smul_eq_mul, h] at hlt
      by_contra hne
      rw [ENNReal.top_mul hne] at hlt
      exact lt_irrefl _ hlt
    have : muG ε Set.univ = 0 := by
      rw [← iUnion_spanningSets ν]
      exact measure_iUnion_null hnull
    have hne : muG ε ≠ 0 := NeZero.ne _
    exact hne (Measure.measure_univ_eq_zero.mp this)
  exact ⟨c, hcne0, hcnetop, by rw [← hmapν, ← heq]⟩

end Transport

theorem schur_orthogonality_relations : WlocSk.SchurG := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨_, hσ, _, _, hG, _⟩ := hyp
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, _⟩, hDS⟩ := hσ
  have : Nontrivial H := hDS.2.1
  obtain ⟨d₀, hd₀, hF⟩ := PIW.HCFdeg.formal_degree_abstract_form _ (Formalism.MainNotions.CayleySignature.eps48 k r) H (fun g => σ (P⁻¹ * g * P))
    hDS.2.2.1 hDS.2.2.2.1 hDS.2.2.2.2.1
  have : SigmaFinite μG := hG.1
  have hPJ' : Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P = PI.UpqRep.Hpk k r := hPJ
  have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P)} = 0 := by
    rw [hPJ']; exact hG.2.2.1
  have hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P),
      μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
    rw [hPJ']; intro s hs; exact hG.2.2.2 s hs
  obtain ⟨cc, hc0, hctop, hμ⟩ := haar_transport (Formalism.MainNotions.CayleySignature.eps48 k r) P hPu μG hG.2.1 hconc hinv
  have hE := conjP_measurableEmbedding (Formalism.MainNotions.CayleySignature.eps48 k r) P hPu
  have hct : 0 < cc.toReal := ENNReal.toReal_pos hc0 hctop
  refine ⟨d₀ / cc.toReal, div_pos hd₀ hct, fun v₁ w₁ v₂ w₂ => ?_⟩
  obtain ⟨hI, hV⟩ := hF v₁ w₁ v₂ w₂
  have hfun : (fun g : UJ (Formalism.MainNotions.CayleySignature.eps48 k r) =>
      (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w₁, σ (Matrix.of x) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of x) v₂⟫_ℂ)
        (conjPrime₂ (Formalism.MainNotions.CayleySignature.eps48 k r) P g)) =
      fun g => coefOn (ε := Formalism.MainNotions.CayleySignature.eps48 k r) (fun g => σ (P⁻¹ * g * P)) v₁ w₁ g *
        star (coefOn (ε := Formalism.MainNotions.CayleySignature.eps48 k r) (fun g => σ (P⁻¹ * g * P)) v₂ w₂ g) := rfl
  rw [hμ]
  refine ⟨?_, ?_⟩
  · rw [hE.integrable_map_iff]
    show Integrable ((fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w₁, σ (Matrix.of x) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of x) v₂⟫_ℂ) ∘ conjPrime₂ (Formalism.MainNotions.CayleySignature.eps48 k r) P) _
    rw [Function.comp_def, hfun]
    exact hI.smul_measure hctop
  · rw [hE.integral_map, hfun, integral_smul_measure, hV]
    rw [Complex.real_smul]
    have hd₀' : (d₀ : ℂ) ≠ 0 := by exact_mod_cast hd₀.ne'
    have hc' : (cc.toReal : ℂ) ≠ 0 := by exact_mod_cast hct.ne'
    push_cast
    field_simp

end WlocSk.Port
