import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergUnipotentCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyCompactGroupFubiniSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingNormAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMeasureMapScalingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviConjHaar

theorem levi_conj_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H (Units.map (cA σ : AE F E →* AE F E) t) 1 m → ∀ μN : Measure (unip σ Y H), μN.IsHaarMeasure → ∀ S : Set (unip σ Y H), ENNReal.ofReal ((absE F E t : ℝ) ^ ((n : ℝ) - 1)) * μN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = μN S := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hB hY hH t m hm μN hμ S
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  letI mE : MeasurableSpace (AE F E) := borel _
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  letI mF : MeasurableSpace (AF F) := borel _
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨hTG, -, -, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n Y.J
  haveI := hTG
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  obtain ⟨Φ, β, hβ, hmul, hconj⟩ := GlobalTheory.T.heisenberg_unipotent_coordinates F E σ B n n₁ Y Y₁ H r s i₀ i₁ hB hY hH
  have hcm := hB.cm
  set lam : (AE F E)ˣ := Units.map (cA σ : AE F E →* AE F E) t with hlam
  have hlam' : absE F E lam = absE F E t := GlobalTheory.Doubling.absE_conjUnit σ t
  set Nt : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) t with hNt
  have h0 : (absE F E t : ENNReal) ≠ 0 := by
    have : absE F E t ≠ 0 := fun h => by
      have := congrArg (absE F E) (mul_inv_cancel t)
      rw [map_mul, map_one, h, zero_mul] at this
      exact zero_ne_one this
    exact_mod_cast this
  have h0l : (absE F E lam : ENNReal) ≠ 0 := by rw [hlam']; exact h0
  let νE : Measure (AE F E) := Measure.addHaar
  let νV : Measure (Fin n₁ → AE F E) := Measure.pi fun _ => νE
  let νZ : Measure (AF F) := Measure.addHaar
  have hE := GlobalTheory.T.haar_scaling_multiplicative F E σ hcm νE inferInstance lam
  have hZ := GlobalTheory.T.haar_scaling_norm_additive F E σ hcm νZ inferInstance t
  have hV := GlobalTheory.T.pi_measure_map_scaling νE (fun x => (lam : AE F E) * x) (continuous_const_mul _).measurable _
    (ENNReal.inv_ne_top.2 h0l) hE n₁
  let A : (Fin n₁ → AE F E) ≃ₜ (Fin n₁ → AE F E) :=
    { toFun := fun v => (lam : AE F E) • v, invFun := fun v => ((lam⁻¹ : (AE F E)ˣ) : AE F E) • v,
      left_inv := fun v => by simp [smul_smul], right_inv := fun v => by simp [smul_smul],
      continuous_toFun := continuous_const_smul _, continuous_invFun := continuous_const_smul _ }
  let C : AF F ≃ₜ AF F :=
    { toFun := fun v => (Nt : AF F) * v, invFun := fun v => ((Nt⁻¹ : (AF F)ˣ) : AF F) * v,
      left_inv := fun v => by simp [← mul_assoc], right_inv := fun v => by simp [← mul_assoc],
      continuous_toFun := continuous_const_mul _, continuous_invFun := continuous_const_mul _ }
  let f : unip σ Y H → unip σ Y H := fun u => ⟨m * u.1 * m⁻¹, (hconj t m hm u).1⟩
  have hf : ∀ u, Φ (f u) = (A (Φ u).1, C (Φ u).2) := fun u => (hconj t m hm u).2
  have hVA : νV.map A = ((absE F E t : ENNReal))⁻¹ ^ n₁ • νV := by
    rw [← hlam']; exact hV
  have hk := GlobalTheory.T.locally_compact_group_fubini_schwartz νV νZ inferInstance inferInstance Φ β hβ hmul f A C _ _
    (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 h0)) (ENNReal.inv_ne_top.2 h0) hVA hZ hf μN hμ S
  have hset : Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S)) = f ⁻¹' S := by
    ext u
    simp only [Set.mem_preimage, Set.mem_image, f]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hsu⟩
      have : s = ⟨m * u.1 * m⁻¹, (hconj t m hm u).1⟩ := by
        apply Subtype.ext; simp [← hsu, mul_assoc]
      rw [← this]; exact hs
    · intro hu
      exact ⟨_, ⟨_, hu, rfl⟩, by simp [mul_assoc]⟩
  rw [hset, hk]
  have hn : (n : ℝ) - 1 = ((n₁ + 1 : ℕ) : ℝ) := by rw [hH.rank]; push_cast; ring
  rw [hn, Real.rpow_natCast]
  have h1 : (absE F E t : ENNReal) ≠ ⊤ := by simp
  rw [ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have key : (absE F E t : ENNReal) ^ (n₁ + 1) * ((absE F E t : ENNReal)⁻¹ ^ n₁ * (absE F E t : ENNReal)⁻¹) = 1 := by
    rw [← pow_succ, ← ENNReal.inv_pow, ENNReal.mul_inv_cancel (pow_ne_zero _ h0) (ENNReal.pow_ne_top h1)]
  rw [← mul_assoc, key, one_mul]

end GlobalTheory.LeviConjHaar
