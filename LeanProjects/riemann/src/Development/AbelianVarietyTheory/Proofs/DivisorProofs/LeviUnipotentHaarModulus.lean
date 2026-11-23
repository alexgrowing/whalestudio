import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureProductGroupsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalHomeomorphHeisenbergStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingLinearEquivUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarCharMulConjEqAbsStatement

noncomputable section

namespace GlobalTheory.LeviModulus

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isLevi_inv {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} (H : Plane E n n₁) {l : (AE F E)ˣ}
    {g₀ : UA σ X₁.J} {m : UA σ X.J} (h : IsLevi H l g₀ m) : IsLevi H l⁻¹ g₀⁻¹ m⁻¹ := by
  obtain ⟨hx, hy, hι⟩ := h
  have hinv : mat m⁻¹ * mat m = 1 := GlobalTheory.StabHaar.mat_inv_mul m
  have hinv₁ : mat g₀ * mat g₀⁻¹ = 1 := GlobalTheory.StabHaar.mat_mul_inv g₀
  have hcl : cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (l : AE F E) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  refine ⟨?_, ?_, ?_⟩
  · calc mat m⁻¹ *ᵥ incV F H.x
        = ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat m⁻¹ *ᵥ ((l : AE F E) • incV F H.x)) := by
          rw [Matrix.mulVec_smul, smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [← hx, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · rw [inv_inv]
    calc mat m⁻¹ *ᵥ incV F H.y
        = cA σ (l : AE F E) • (mat m⁻¹ *ᵥ (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.y)) := by
          rw [Matrix.mulVec_smul, smul_smul, mul_comm, hcl, one_smul]
      _ = _ := by rw [← hy, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * (mat g₀ * mat g₀⁻¹)) := by rw [hinv₁, Matrix.mul_one]
      _ = mat m⁻¹ * (mat m * incM F H.ι) * mat g₀⁻¹ := by rw [hι]; simp only [Matrix.mul_assoc]
      _ = incM F H.ι * mat g₀⁻¹ := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

theorem mul_mem_imA {a z : AE F E} (ha : cA σ a = a) (hz : z ∈ imA σ) : a * z ∈ imA σ := by
  rw [mem_imA] at *
  rw [map_mul, ha, hz, mul_neg]

theorem lintegral_conj_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (r s r₁ s₁ i₀ i₁ : ℕ) (H : Plane E n n₁), B.IsGood σ → X.IsHerm σ B r s →
    X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ m : (AE F E)ˣ → UA σ X₁.J → UA σ X.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ (μN : Measure (unip σ X H)), μN.IsHaarMeasure → ∀ l g₀ (f : UA σ X.J → ENNReal), Measurable f →
      ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - (n : ℝ))) * ∫⁻ u, f u.1 ∂μN := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH m hm μN hμ l g₀ f hf
  obtain ⟨hR, hLC, hSC, hT2⟩ := topAE F E
  haveI := hR; haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTG, hLCU, hSCU, hT2U⟩ := topUA σ X.J
  haveI := hTG; haveI := hLCU; haveI := hSCU; haveI := hT2U
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hx0 : H.x ≠ 0 := fun h0 => by
    have h1 := hH.xy
    rw [h0] at h1
    simp [form] at h1
  have hcl := GlobalTheory.UnipClosed.isClosed_unip F E σ n n₁ X H hx0
  haveI : LocallyCompactSpace (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (unip σ X H) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  obtain ⟨Ψ, ω, hω, hlaw, hconj⟩ := GlobalTheory.T.unipotent_radical_homeomorph_heisenberg F E σ B n n₁ X X₁ r s r₁ s₁ i₀ i₁ H hB hX hX₁ hH
  have hmem : ∀ (l' : (AE F E)ˣ) (g' : UA σ X₁.J) (m' : UA σ X.J), IsLevi H l' g' m' →
      ∀ u ∈ unip σ X H, m' * u * m'⁻¹ ∈ unip σ X H := by
    intro l' g' m' hl' u hu
    obtain ⟨p, hp, -, -⟩ := hconj l' g' m' hl' (Ψ.symm ⟨u, hu⟩).1 (Ψ.symm ⟨u, hu⟩).2
    rw [Prod.mk.eta, Homeomorph.apply_symm_apply] at hp
    rw [hp]
    exact (Ψ p).2
  have hm0 := hm l g₀
  have h₁ := hmem l g₀ (m l g₀) hm0
  have h₂ : ∀ u ∈ unip σ X H, (m l g₀)⁻¹ * u * m l g₀ ∈ unip σ X H := fun u hu => by
    simpa using hmem _ _ _ (isLevi_inv H hm0) u hu
  let φ := conjOn (unip σ X H) (m l g₀) h₁ h₂
  have hσσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hcc : ∀ z : AE F E, cA σ (cA σ z) = z := cA_cA σ hσσ
  have hcu : ∀ u : (AE F E)ˣ, cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (u : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hcu' : ∀ u : (AE F E)ˣ, cA σ (u : AE F E) * cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have hN : ∀ u : (AE F E)ˣ, cA σ ((u : AE F E) * cA σ u) = u * cA σ u := fun u => by
    rw [map_mul, hcc, mul_comm]
  have hmc : Continuous fun a : Fin n₁ → AE F E => a := continuous_id
  let L₁ : (Fin n₁ → AE F E) ≃ₜ+ (Fin n₁ → AE F E) :=
    { toFun := fun a => cA σ (l : AE F E) • (mat g₀ *ᵥ a)
      invFun := fun a => cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) • (mat g₀⁻¹ *ᵥ a)
      left_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu, one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul,
          Matrix.one_mulVec]
      right_inv := fun a => by
        simp only
        rw [Matrix.mulVec_smul, smul_smul, hcu', one_smul, Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_mul_inv,
          Matrix.one_mulVec]
      map_add' := fun a b => by simp only [Matrix.mulVec_add, smul_add]
      continuous_toFun := (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ (l : AE F E))
      continuous_invFun :=
        (continuous_const.matrix_mulVec continuous_id).const_smul (cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E)) }
  let L₂ : imA σ ≃ₜ+ imA σ :=
    { toFun := fun b => ⟨(l : AE F E) * cA σ l * b, mul_mem_imA (hN l) b.2⟩
      invFun := fun b => ⟨((l⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((l⁻¹ : (AE F E)ˣ) : AE F E) * b, mul_mem_imA (hN l⁻¹) b.2⟩
      left_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.inv_mul, hcu, one_mul, one_mul])
      right_inv := fun b => Subtype.ext (by
        simp only
        rw [← mul_assoc, mul_mul_mul_comm, Units.mul_inv, hcu', one_mul, one_mul])
      map_add' := fun a b => Subtype.ext (by simp only [AddSubgroup.coe_add, mul_add])
      continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _ }
  have hφΨ : ∀ a b, φ (Ψ (a, b)) = Ψ (L₁ a, L₂ b) := by
    intro a b
    obtain ⟨p, hp, hp1, hp2⟩ := hconj l g₀ (m l g₀) hm0 a b
    apply Subtype.ext
    rw [conjOn_apply, hp]
    congr 2
    exact Prod.ext hp1 (Subtype.ext hp2)
  letI : MeasurableSpace (Fin n₁ → AE F E) := borel _
  haveI : BorelSpace (Fin n₁ → AE F E) := ⟨rfl⟩
  letI : MeasurableSpace (imA σ) := borel _
  haveI : BorelSpace (imA σ) := ⟨rfl⟩
  haveI : LocallyCompactSpace (imA σ) := (isClosed_imA σ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (imA σ) :=
    (isClosed_imA σ).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  have hchar : mulEquivHaarChar φ = absE F E l ^ n₁ * absE F E l := by
    rw [GlobalTheory.T.haar_measure_product_groups _ _ _ Ψ ω hω hlaw φ L₁ L₂ hφΨ, GlobalTheory.T.haar_scaling_linear_equiv_unit F E σ B n₁ X₁ r₁ s₁ hB hX₁ l g₀ L₁ (fun a => rfl),
      GlobalTheory.T.haar_char_mul_conj_eq_abs F E σ B hB l L₂ (fun b => rfl)]
  haveI : IsTopologicalGroup (unip σ X H) := inferInstance
  haveI : T2Space (unip σ X H) := inferInstance
  haveI : RegularSpace (unip σ X H) := by
    first
    | exact IsTopologicalGroup.regularSpace _
    | exact TopologicalGroup.regularSpace _
    | exact inferInstanceAs (RegularSpace (Subtype _))
  haveI : T1Space (unip σ X H) := T2Space.t1Space
  haveI : T0Space (unip σ X H) := T1Space.t0Space
  haveI : T3Space (unip σ X H) := T3Space.mk
  haveI : TopologicalSpace.MetrizableSpace (unip σ X H) := TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : μN.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hsm := mulEquivHaarChar_smul_map μN φ
  rw [hchar] at hsm
  have hpos : absE F E l ≠ 0 := ((Group.isUnit l).map (absE F E)).ne_zero
  set c : ℝ≥0 := absE F E l ^ n₁ * absE F E l with hc
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hpos) hpos
  have hmap : μN.map φ = c⁻¹ • μN := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 : ∫⁻ u, f (m l g₀ * u.1 * (m l g₀)⁻¹) ∂μN = ∫⁻ u, f u.1 ∂(μN.map φ) :=
    (lintegral_map_equiv (fun v : unip σ X H => f v.1) φ.toHomeomorph.toMeasurableEquiv).symm
  rw [e1, hmap, lintegral_smul_measure]
  have hn : (n : ℝ) = n₁ + 2 := by rw [hH.rank]; push_cast; ring
  have e2 : ((absE F E l : ℝ)) ^ (1 - (n : ℝ)) = ((c⁻¹ : ℝ≥0) : ℝ) := by
    rw [hn, show (1 : ℝ) - (n₁ + 2) = -((n₁ + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg (NNReal.coe_nonneg _),
      Real.rpow_natCast, hc, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow, pow_succ]
  rw [e2, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.LeviModulus

end
