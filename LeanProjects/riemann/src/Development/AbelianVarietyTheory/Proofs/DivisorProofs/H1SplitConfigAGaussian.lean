import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParaSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAMatchedDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLineDerivativeExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieDerivativePolynomialFockSeesawStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

theorem frobInf_eq_of_lowPart : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ φ φ' : R.Pi →ₗ[ℂ] R₁.Pi, IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ →
        IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) φ' →
        ∀ c : ℂ, (∀ x ∈ lowPartInf B G.M R.p, φ' x = c • φ x) → φ' = c • φ := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ φ φ' hφ hφ' c hc
  have htop := GlobalTheory.T.config_a_matched_descent hK F E σ B b a' G G₁ H H' hC X om om' R Rf hM
  suffices h : paraSpan B G.M om G₁.W H' R.p ≤ LinearMap.ker (φ' - c • φ) by
    ext x
    have hx : x ∈ LinearMap.ker (φ' - c • φ) := h (htop ▸ Submodule.mem_top)
    simpa [sub_eq_zero] using hx
  refine sInf_le ⟨fun x hx => ?_, ?_⟩
  · simp [sub_eq_zero, hc x hx]
  rintro γ hγ hP f hf f₁ hd hpf
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hpf ⊢
  rcases hP with hu | ⟨γ₁, hγ₁, t, ht⟩
  · rw [hφ'.unip γ hγ hu f hf f₁ hd, hφ.unip γ hγ hu f hf f₁ hd, smul_zero]
  · obtain ⟨δ₁, hδ₁⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G₁ X om₁ om₁' hM₁.triple γ₁ hγ₁
    have hx0 : H'.x ≠ 0 := fun h0 => by simpa [h0, form] using hC.hH'.xy
    obtain ⟨cX, hcX⟩ := GlobalTheory.T.hecke_line_derivative_exists G.W G₁.W H' hx0 γ hγ γ₁ hγ₁ t ht X.α hM.triple.chars.heckeα ((a' : ℝ) / 2)
    have hmem : φ (R.p f) ∈ (G₁.M.Pol B.ψ B.emb).map R₁.p := by rw [hM₁.real.quot.onto]; trivial
    obtain ⟨g, hg, hpg⟩ := hmem
    have e1 := hφ.lie γ hγ γ₁ hγ₁ t ht f hf f₁ hd g hg (δ₁ g) (hδ₁ g hg).2 hpg.symm cX hcX
    have hcg : c • g ∈ G₁.M.Pol B.ψ B.emb := Submodule.smul_mem _ c hg
    have e2 := hφ'.lie γ hγ γ₁ hγ₁ t ht f hf f₁ hd (c • g) hcg (δ₁ (c • g)) (hδ₁ _ hcg).2
      (by rw [hpf, map_smul, hpg]) cX hcX
    rw [e2, e1, hpf, map_smul, map_smul, smul_add, smul_comm c cX]

end GlobalTheory.IndLine
