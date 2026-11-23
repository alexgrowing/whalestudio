import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemFullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneThetaLiftAutomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryCountableDiscreteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalCharactersLinearBarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPolDataAlmostAllPlaces

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKLiftGood

theorem quasi {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (y : G) :
    ∃ m : ℝ, 0 < m ∧ ∀ φ : G → ℂ, (∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h) →
      (IntegrableOn φ 𝓕 μ → IntegrableOn (fun h => φ (h * y)) 𝓕 μ) ∧
        (m : ℂ) * ∫ h in 𝓕, φ (h * y) ∂μ = ∫ h in 𝓕, φ h ∂μ := by
  have hmap : ∀ z : G, Measure.map (· * z) μ = Measure.modularCharacterFun z • μ := fun z =>
    Measure.map_right_mul_eq_modularCharacterFun_smul μ z
  have hpos := Measure.modularCharacterFun_pos y
  have hemb : MeasurableEmbedding fun h : G => h * y := (MeasurableEquiv.mulRight y).measurableEmbedding
  have hq : Measure.QuasiMeasurePreserving (Equiv.mulRight y).symm μ μ := by
    refine ⟨measurable_mul_const y⁻¹, ?_⟩
    have := hmap y⁻¹
    show Measure.map (· * y⁻¹) μ ≪ μ
    rw [this]
    exact Measure.smul_absolutelyContinuous
  have h𝓕' : IsFundamentalDomain Γ (Equiv.mulRight y '' 𝓕) μ :=
    h𝓕.image_of_equiv (Equiv.mulRight y) hq (Equiv.refl _) fun γ h => by
      simp [Subgroup.smul_def, mul_assoc]
  have hpre : (fun h : G => h * y) ⁻¹' (Equiv.mulRight y '' 𝓕) = 𝓕 :=
    Set.preimage_image_eq 𝓕 (Equiv.mulRight y).injective
  refine ⟨(Measure.modularCharacterFun y : ℝ)⁻¹, inv_pos.2 (by exact_mod_cast hpos), fun φ hφ => ⟨fun hi => ?_, ?_⟩⟩
  · have h1 := (h𝓕.integrableOn_iff h𝓕' (f := φ) fun γ h => hφ γ.1 γ.2 h).1 hi
    have h2 : IntegrableOn φ (Equiv.mulRight y '' 𝓕) (Measure.map (· * y) μ) := by
      rw [hmap y, IntegrableOn, Measure.restrict_smul]
      exact Integrable.smul_measure_nnreal h1
    rw [hemb.integrableOn_map_iff, hpre] at h2
    exact h2
  · have h1 := hemb.setIntegral_map (μ := μ) φ (Equiv.mulRight y '' 𝓕)
    rw [hpre, hmap y, Measure.restrict_smul, integral_smul_nnreal_measure,
      ← h𝓕.setIntegral_eq h𝓕' (f := φ) fun γ h => hφ γ.1 γ.2 h] at h1
    rw [← h1, NNReal.smul_def, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      inv_mul_cancel₀ (by exact_mod_cast hpos.ne'), Complex.ofReal_one, one_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem omA_left {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (ν β : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Ψ = GlobalTheory.FullRankCoinv.lact ν (GlobalTheory.SplitFlip.invT g) Ψ := by
  funext Y
  simp [GlobalTheory.SplitFlip.omA, GlobalTheory.FullRankCoinv.lact, GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.apow_inv,
    GlobalTheory.SplitFlip.invT_val, neg_div]

theorem theta_left {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (Ψ : Fn F n d) (x g : UA σ X.J) (h : UA σ W.J) :
    theta om (om (x, 1) Ψ) g h = theta om Ψ (g * x) h := by
  simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_right {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (Ψ : Fn F n d) (g : UA σ X.J) (y h : UA σ W.J) :
    theta om (om (1, y) Ψ) g h = theta om Ψ g (h * y) := by
  simp only [theta, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

def Nice {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) :
    Submodule ℂ (UA σ W.J → ℂ) where
  carrier := {u | (∀ γ ∈ ratU σ W.J, ∀ h, u (γ * h) = u h) ∧ ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ g,
    IntegrableOn (fun h => u h * (starRingEnd ℂ) (theta om Ψ g h)) 𝓕 μ}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => by simp⟩
  add_mem' := fun hu hw => ⟨fun γ hγ h => by simp only [Pi.add_apply, hu.1 γ hγ, hw.1 γ hγ], fun Ψ hΨ g => by
    simp only [Pi.add_apply, add_mul]
    exact Integrable.add (hu.2 Ψ hΨ g) (hw.2 Ψ hΨ g)⟩
  smul_mem' := fun c u hu => ⟨fun γ hγ h => by simp only [Pi.smul_apply, hu.1 γ hγ], fun Ψ hΨ g => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact Integrable.const_mul (hu.2 Ψ hΨ g) c⟩

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.ThKLiftGood
