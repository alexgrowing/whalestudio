import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipAugLeJacKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviActionLocalGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalVectorSplitStatement

noncomputable section

namespace GlobalTheory.JacquetLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

theorem firstBlockScalar_coeff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ ℓ : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om v ≤ LinearMap.ker ℓ → (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ₀ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, u)) φ₀ φ₁ → ℓ φ₁ = ℓ φ₀) → ∃ p q : ℂ, ∀ (x : (w.adicCompletion E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := W₁) H' (locIdele F w x) 1 m → m ∈ UAt σ G.W (evFin F v) → ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, m)) φ φ₁ → ℓ φ₁ = p * ((GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) + q * ((GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x) : ℂˣ) : ℂ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v hv w hw φ hφ ℓ hℓ hN
  obtain ⟨φa, ha, φb, hb, hsum, hA, hB⟩ :=
    GlobalTheory.T.unramified_local_vector_split hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v hv w hw φ hφ
  have hker := jacKer_le_ker om H' v ℓ hℓ hN
  refine ⟨ℓ φa, ℓ φb, ?_⟩
  intro x m hm hmU φ₁ hφ₁ hact
  obtain ⟨ψ₁, hψ₁, ψ₁', hψ₁', hA1, hB1, hrel⟩ :=
    GlobalTheory.T.levi_action_local_good_place hKP F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH v hv _ m hm hmU φ hφ φa ha φb hb hsum φ₁ hφ₁ hact
  have e0 := hker hrel
  have e1 := hker (hA x m hm hmU ψ₁ hψ₁ hA1)
  have e2 := hker (hB x m hm hmU ψ₁' hψ₁' hB1)
  simp only [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at e0 e1 e2
  linear_combination e0 + e1 + e2

end GlobalTheory.JacquetLine
