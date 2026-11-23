import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem co_mkE (D : Dat F E) (u t : A F) : D.co (D.mkE u t) = ![u, t] := by
  letI : Algebra (A F) (A E) := AdeleBaseChange.algebraAdeleRing
  have h : D.mkE u t = u • AdeleBaseChange.adeleBasis D.b 0 + t • AdeleBaseChange.adeleBasis D.b 1 := by
    rw [AdeleBaseChange.adeleBasis_apply, AdeleBaseChange.adeleBasis_apply, D.b0, D.b1,
      Algebra.smul_def, Algebra.smul_def, map_one, mul_one]
    rfl
  funext i
  unfold Dat.co
  rw [h]
  fin_cases i <;> simp

private theorem sigma_ne (D : Dat F E) : D.σ ≠ 1 := by
  intro h
  have h1 := D.conj
  rw [h] at h1
  have h2 : (2 : E) * D.θ = 0 := by
    have : D.θ = -D.θ := h1
    linear_combination this
  have h3 : D.θ = 0 := by simpa using h2
  exact D.b.ne_zero 1 (by rw [D.b1, h3])

private theorem finrank_two (D : Dat F E) : Module.finrank F E = 2 := by
  simpa using Module.finrank_eq_card_basis D.b

private theorem galois (D : Dat F E) : IsGalois F E := by
  haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
  apply IsGalois.of_card_aut_eq_finrank
  rw [finrank_two D]
  apply le_antisymm
  · rw [← finrank_two D, Nat.card_congr (algEquivEquivAlgHom F E).toEquiv, Nat.card_eq_fintype_card]
    exact AlgHom.card_le
  · have : ({1, D.σ} : Finset (E ≃ₐ[F] E)).card = 2 := Finset.card_pair (Ne.symm (sigma_ne D))
    rw [← this, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ _

private theorem mul_bar (D : Dat F E) (α : (A E)ˣ) :
    AdeleBaseChange.adeleMap F E ((ideleNorm F E α : (A F)ˣ) : A F) = (α : A E) * D.bar α := by
  haveI := galois D
  rw [coe_ideleNorm, AdeleBaseChange.adeleMap_norm]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, D.σ} := by
    haveI : FiniteDimensional F E := Module.Basis.finiteDimensional_of_finite D.b
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair (Ne.symm (sigma_ne D)), Finset.card_univ, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank, finrank_two D]
  rw [hu, Finset.prod_pair (Ne.symm (sigma_ne D))]
  simp [Dat.bar]

end SlopeTestRemainingChoices

section Aux2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem act_aE (D : Dat F E) (α : (A E)ˣ) (y s z₀ z₁ : A F) :
    D.act (aE α)⁻¹ ![y, s, z₀, z₁] =
      ![y, (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  have hinv : (((aE α)⁻¹ : GL (Fin 2) (A E))).val = !![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] := rfl
  have hN : AdeleBaseChange.adeleMap F E (((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) =
      ((α⁻¹ : (A E)ˣ) : A E) * D.bar ((α⁻¹ : (A E)ˣ) : A E) := by
    rw [← map_inv, mul_bar]
  have hz : D.mkE 0 0 = 0 := by simp [Dat.mkE]
  have h00 : ((α⁻¹ : (A E)ˣ) : A E) * D.mkE s 0 * D.bar ((α⁻¹ : (A E)ˣ) : A E) =
      D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0 := by
    simp only [Dat.mkE, map_mul, hN, map_zero, zero_mul, add_zero]
    ring
  unfold Dat.act Dat.unherm
  rw [hinv]
  have hm : (!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] * D.herm ![y, s, z₀, z₁] *
      ((!![((α⁻¹ : (A E)ˣ) : A E), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)).map D.bar)ᵀ) =
      !![D.mkE ((((ideleNorm F E α)⁻¹ : (A F)ˣ) : A F) * s) 0, ((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁;
        D.mkE z₀ (-z₁) * D.bar ((α⁻¹ : (A E)ˣ) : A E), D.mkE y 0] := by
    rw [← h00]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hm]
  simp [co_mkE]

private theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ := by
  simp [ab]

private theorem integral_scale (a : (A F)ˣ) (G : A F → ℂ) :
    ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = (((ab a)⁻¹ : ℝ) : ℂ) * ∫ s, G s ∂(adeleMeasure F) := by
  have hemb : MeasurableEmbedding (fun x : A F => (a : IdeleGroup F) • x) :=
    (Homeomorph.smul (a : IdeleGroup F)).measurableEmbedding
  have h := hemb.integral_map (μ := adeleMeasure F) G
  rw [map_smul_adeleMeasure, integral_smul_measure] at h
  have h2 : ∫ s, G ((a : A F) * s) ∂(adeleMeasure F) = ∫ x, G ((a : IdeleGroup F) • x) ∂(adeleMeasure F) := rfl
  rw [h2, ← h, ENNReal.toReal_ofReal (inv_pos.2 (IdeleGroup.ideleModule F a).2).le, Complex.real_smul]
  rfl

end Aux2

theorem UpperTheory.ConvolutionTheory.R2.D.hatAE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ (α : (A E)ˣ) φ y x z₀ z₁, hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] =
      hat φ.1 ![y, (ideleNorm F E α : (A F)ˣ) * x, D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0,
        D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1] := by
  intro F E _ _ _ _ _ _ _ D W α φ y x z₀ z₁
  have hdet : Matrix.GeneralLinearGroup.det (aE α) = α := by
    ext
    simp [aE, Matrix.GeneralLinearGroup.det, Matrix.det_fin_two]
  have hnu : nu F (aE α) = ideleNorm F E α := by
    rw [nu, hdet]
  have hup : ∀ a b c d s : A F, Function.update ![a, b, c, d] 1 s = ![a, s, c, d] := by
    intro a b c d s
    ext i
    fin_cases i <;> simp
  set N : (A F)ˣ := ideleNorm F E α with hN
  set c₀ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 0
  set c₁ := D.co (((α⁻¹ : (A E)ˣ) : A E) * D.mkE z₀ z₁) 1
  let G : A F → ℂ := fun s => φ.1 ![y, s, c₀, c₁] * ψ (-(s * ((N : A F) * x)))
  have hpt : ∀ s : A F, (W.L (aE α) φ).1 (Function.update ![y, x, z₀, z₁] 1 s) * ψ (-(s * (![y, x, z₀, z₁] : V4 F) 1)) =
      (((ab N)⁻¹ : ℝ) : ℂ) * G (((N⁻¹ : (A F)ˣ) : A F) * s) := by
    intro s
    have hs : ((N⁻¹ : (A F)ˣ) : A F) * s * ((N : A F) * x) = s * x := by
      have : ((N⁻¹ : (A F)ˣ) : A F) * (N : A F) = 1 := Units.inv_mul N
      linear_combination (s * x) * this
    rw [hup, W.L_apply, hnu, act_aE]
    simp only [G, hs]
    exact mul_assoc _ _ _
  have hab : ab N ≠ 0 := (IdeleGroup.ideleModule F N).2.ne'
  have hL : hat (W.L (aE α) φ).1 ![y, x, z₀, z₁] = ∫ s, G s ∂(adeleMeasure F) := by
    unfold hat
    simp_rw [hpt]
    rw [integral_const_mul, integral_scale (N⁻¹) G, ab_inv, inv_inv, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hab]
    simp
  rw [hL]
  unfold hat
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [G, hup]
  rfl
