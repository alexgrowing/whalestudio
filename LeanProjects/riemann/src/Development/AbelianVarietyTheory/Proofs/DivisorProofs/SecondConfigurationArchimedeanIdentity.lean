import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleConfigBThetaIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleConfigBThetaUnfoldingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.ConeInt

theorem setLIntegral_le_of_cover {Γ α : Type*} [Group Γ] [MulAction Γ α] [MeasurableSpace α] {μ : Measure α}
    [MeasurableConstSMul Γ α] [SMulInvariantMeasure Γ α μ] [Countable Γ] {D S : Set α}
    (hD : IsFundamentalDomain Γ D μ) (hS : ∀ x, ∃ g : Γ, g • x ∈ S) (f : α → ℝ≥0∞)
    (hf : ∀ (g : Γ) x, f (g • x) = f x) : ∫⁻ x in D, f x ∂μ ≤ ∫⁻ x in S, f x ∂μ := by
  have hsub : D ⊆ ⋃ g : Γ, (g • S ∩ D) := by
    intro x hx
    obtain ⟨g, hg⟩ := hS x
    refine Set.mem_iUnion.2 ⟨g⁻¹, ⟨g • x, hg, by simp⟩, hx⟩
  calc ∫⁻ x in D, f x ∂μ ≤ ∫⁻ x in ⋃ g : Γ, (g • S ∩ D), f x ∂μ := lintegral_mono_set hsub
    _ ≤ ∑' g : Γ, ∫⁻ x in g • S ∩ D, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : Γ, ∫⁻ x in g • S ∩ D, f (g⁻¹ • x) ∂μ := by simp only [hf]
    _ = ∫⁻ x in S, f x ∂μ := (hD.setLIntegral_eq_tsum' f S).symm

theorem countable_of_le_ratU {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (Q : Subgroup (UA σ J)) (hQ : ∀ q ∈ Q, q ∈ ratU σ J) : Countable Q := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) fun x y hxy => Units.ext hxy
  have hmem : ∀ q : Q, ∃ γ : GL (Fin n) E,
      Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) γ = (q.1 : GL (Fin n) (AE F E)) := by
    intro q
    have := hQ q.1 q.2
    simpa [ratU, Subgroup.mem_subgroupOf] using this
  choose f hf using hmem
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  have : (x.1 : GL (Fin n) (AE F E)) = y.1 := by rw [← hf x, ← hf y, hxy]
  exact Subtype.ext (Subtype.ext this)

theorem lintegral_lt_top : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ Φ ∈ PolData B G.M, ∀ h, ∀ Q : Subgroup (UA σ G.V.J), (∀ q, q ∈ Q ↔ q ∈ ratU σ G.V.J ∧ mat q *ᵥ incV F H₀.x = incV F H₀.x) → ∀ D : Set (UA σ G.V.J), IsFundamentalDomain Q D G.M.μ → ∫⁻ g in D, ‖thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ)))‖ₑ ∂G.M.μ < ⊤ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ D hD
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI : G.M.μ.IsHaarMeasure := hT.geo.hM.haar
  haveI : MeasurableConstSMul Q (UA σ G.V.J) :=
    ⟨fun q => (continuous_const.mul continuous_id : Continuous fun x : UA σ G.V.J => (q : UA σ G.V.J) * x).measurable⟩
  haveI : SMulInvariantMeasure Q (UA σ G.V.J) G.M.μ :=
    ⟨fun q s _ => measure_preimage_mul G.M.μ (q : UA σ G.V.J) s⟩
  haveI : Countable Q := countable_of_le_ratU Q fun q hq => ((hQ q).1 hq).1
  obtain ⟨S, hS, hfin⟩ := GlobalTheory.T.triple_config_b_theta_unfolding hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ
  have hinv := GlobalTheory.T.triple_config_b_theta_integral hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ hev Φ hΦ h Q hQ
  refine lt_of_le_of_lt (setLIntegral_le_of_cover hD (fun g => ?_) _ (fun q g => ?_)) hfin
  · obtain ⟨q, hq, hqg⟩ := hS g
    exact ⟨⟨q, hq⟩, hqg⟩
  · exact hinv q.1 q.2 g

end GlobalTheory.ConeInt

end
