import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperMapBumpFunctionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPartialFourierIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeATripleFourthStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

namespace GlobalTheory.BumpMult

theorem exists_multiplier : ∀ (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W)
    (hCfg : CfgA B G G₁ H H') (hT : IsTriple B G X om om') (hT₁ : IsTriple B G₁ X om₁ om₁')
    (e : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a')) (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e)
    (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (hei : ei ≠ 0) (hev : ∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _)
    (hpure : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v))
    (K : Subgroup (UA σ G.V.J)) (hK : IsStab B K) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
    (hμK : IsNormK K (evI F) μK) (hμ : μ.IsHaarMeasure)
    (l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ) (hl : l ≠ 0)
    (hinv : ∀ g ∈ UAt σ G₁.V (evI F), ∀ f f₁ : SInf F (Fin b × Fin (b + a')), Acts (evI F) (om₁ (g, 1)) f f₁ → l f₁ = l f) (f₀ : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (O : Set (KAt K (evI F) × idelesAt E (evI F)))
    (hO : IsOpen O) (hSig : ∀ (k : KAt K (evI F)) (t : idelesAt E (evI F)),
      mat k.1⁻¹ *ᵥ ((t.1 : AE F E) • incV F H.x) = incV F H.x → (k, t) ∈ O),
    ∃ (f : SInf F (Fin (b + 2) × Fin (b + 2 + a'))) (Ψ : KAt K (evI F) × idelesAt E (evI F) → ℝ)
      (C : Set (KAt K (evI F) × idelesAt E (evI F))), Continuous Ψ ∧ (∀ p, 0 ≤ Ψ p) ∧ 0 < Ψ (1, 1) ∧ IsCompact C ∧
      C ⊆ O ∧ (∀ p ∉ C, Ψ p = 0) ∧
      ∀ p : KAt K (evI F) × idelesAt E (evI F), coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f p.1.1 p.2.1 = (Ψ p : ℂ) • coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f₀ p.1.1 p.2.1 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK μK μ hμK hμ l hl hinv f₀ O hO hSig
  obtain ⟨m, Λ₁, Λ₂, π, W', hπc, hW'o, h1W, hprop, hSg, hℓ⟩ :=
    GlobalTheory.T.seesaw_type_a_triple_fourth hKP F E σ B b a' G G₁ H H' X om om' om₁ om₁' hCfg hT hT₁ e he ei ev hei hev hpure K hK f₀
  obtain ⟨φ, C, hφr, hφ1, hC, hCO, hCz⟩ := GlobalTheory.T.proper_map_bump_function_exists π hπc W' hW'o hprop (1, 1) h1W O hO (by
    intro p hp
    exact hSig p.1 p.2 (hSg p hp))
  obtain ⟨f, hf⟩ := GlobalTheory.T.schrodinger_partial_fourier_intertwine (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
    (GlobalTheory.ArchUniq.Coord.isPairing_trP _) Λ₁ Λ₂ φ f₀
  refine ⟨f, fun p => (φ (π p)).re, C, Complex.continuous_re.comp (φ.continuous.comp hπc),
    fun p => (hφr _).2, hφ1, hC, hCO, fun p hp => by simp [hCz p hp], fun p => ?_⟩
  ext y
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hℓ p y
  have key := hf ℓ (π p) hℓ2
  rw [hℓ1, hℓ1] at key
  have hre : (((φ (π p)).re : ℝ) : ℂ) = φ (π p) := Complex.ext (by simp) (by simp [(hφr _).1])
  simp only [coneInfInt, SchwartzMap.smul_apply, smul_eq_mul, hre]
  rw [key]
  ring

end GlobalTheory.BumpMult
