import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainSubgroupMeasureConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainIndependentIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureConjugationInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentClosedFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarLeviConjMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainTranslateStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LeviModulus

theorem integral_levi_translate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ d₂ : ℕ) (W₂ : Spc F E d₂) (M₂ : Model σ X₁ W₂), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ (Units.map (cA σ : AE F E →* AE F E) t) 1 m₀ → ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}) 𝓓 G.M.μ → ∀ φ : UA σ G.V.J → ENNReal, AEMeasurable φ G.M.μ → (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}, ∀ g, φ (q * g) = φ g) → (∀ n ∈ unip σ G.V H₀, ∀ g, φ (n * g) = φ g) → ENNReal.ofReal ((absE F E t : ℝ) ^ ((a : ℝ) - 1)) * ∫⁻ g in 𝓓, φ (m₀⁻¹ * g) ∂G.M.μ = ∫⁻ g in 𝓓, φ g ∂G.M.μ := by
  intro F E _ _ _ _ _ σ B a b G X om om' hT V₂ n₁ X₁ H₀ j₀ j₁ d₂ W₂ M₂ hV₂ hH₀ hM₂ t m₀ hm₀ 𝓓 h𝓓 φ hφ hφQ hφN
  classical
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ a G.V.J
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hT.geo.hM.haar
  haveI : SFinite G.M.μ :=
    @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts G.M.μ)
  set Q : Subgroup (UA σ G.V.J) :=
    ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x} with hQdef
  set N : Subgroup (UA σ G.V.J) := unip σ G.V H₀ with hNdef
  haveI : Countable ↥(ratU σ G.V.J) := GlobalTheory.QDom.countable_ratU σ G.V.J
  haveI hQc : Countable Q := (Subgroup.inclusion_injective (inf_le_left : Q ≤ ratU σ G.V.J)).countable
  obtain ⟨hNcl, hfd⟩ := GlobalTheory.T.unipotent_closed_fundamental_domain F E σ B a n₁ (reS G.V V₂) X₁ H₀ (a - G.p) G.p j₀ j₁ hT.base hV₂ hH₀
  have hNcl' : IsClosed (N : Set (UA σ G.V.J)) := hNcl
  haveI : LocallyCompactSpace N := hNcl'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μN : Measure N := Measure.haar
  have hμN : μN.IsHaarMeasure := by dsimp only [μN]; infer_instance
  obtain ⟨E₀, hE₀, hE₀0, hE₀top⟩ : ∃ E₀ : Set N, IsFundamentalDomain ((ratU σ G.V.J).subgroupOf N) E₀ μN ∧
      μN E₀ ≠ 0 ∧ μN E₀ ≠ ⊤ := hfd μN hμN
  have hNQ : N ≤ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x} :=
    Subgroup.closure_mono fun u hu => hu.1
  have hsub : Q.subgroupOf N = (ratU σ G.V.J).subgroupOf N := by
    ext n
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Q]
    exact ⟨fun h => h.1, fun h => ⟨h, hNQ n.2⟩⟩
  have hE₀' : IsFundamentalDomain (Q.subgroupOf N) E₀ μN := by rw [hsub]; exact hE₀
  have hmN := GlobalTheory.T.levi_normalizes_unipotent' F E σ a n₁ (reS G.V V₂) X₁ H₀ _ m₀ hm₀
  have hQf := GlobalTheory.T.unipotent_normalizer_rational F E σ B a n₁ (reS G.V V₂) X₁ H₀ (a - G.p) G.p j₀ j₁ hV₂ hH₀ _ m₀ hm₀
  have hmod := GlobalTheory.T.unipotent_haar_levi_conj_measure F E σ B a n₁ (reS G.V V₂) X₁ H₀ (a - G.p) G.p j₀ j₁ hT.base hV₂ hH₀ t m₀ hm₀ μN hμN
  have habs : 0 < (absE F E t : ℝ) := by
    have h1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 (left_ne_zero_of_mul_eq_one h1))
  have hc0 : ENNReal.ofReal ((absE F E t : ℝ) ^ ((a : ℝ) - 1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos habs _)).ne'
  obtain ⟨hQ₂le, ν, hνs, hνinv, hνQ, hνQ₂, E₁, E₂, hE₁, hE₂, hE12, hE₁0, hE₁top⟩ :=
    GlobalTheory.T.quotient_measure_conjugation_invariant N Q m₀ hNcl' (fun q hq => (hQf q hq).1) hmN (fun q hq => (hQf q hq).2) μN hμN E₀ hE₀' hE₀0
      hE₀top _ hc0 ENNReal.ofReal_ne_top hmod
  obtain ⟨h𝓓₂, hint⟩ := GlobalTheory.T.fundamental_domain_translate G.M.μ Q 𝓓 m₀ h𝓓
  haveI : SFinite ν := hνs
  haveI : Countable ↥(Q.map (MulAut.conj m₀⁻¹).toMonoidHom) :=
    ((MulAut.conj m₀⁻¹).toMonoidHom.subgroupMap_surjective Q).countable
  have s₁ := GlobalTheory.T.fundamental_domain_subgroup_measure_const G.M.μ (Q ⊔ N) ν Q le_sup_left hνQ 𝓓 h𝓓 E₁ hE₁
  have s₂ := GlobalTheory.T.fundamental_domain_subgroup_measure_const G.M.μ (Q ⊔ N) ν _ hQ₂le hνQ₂ _ h𝓓₂ E₂ hE₂
  let S : Subgroup (UA σ G.V.J) :=
    { carrier := {p | ∀ g, φ (p * g) = φ g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx (x⁻¹ * g), mul_inv_cancel_left] }
  have hQNS : Q ⊔ N ≤ S := sup_le (fun q hq => hφQ q hq) (fun n hn => hφN n hn)
  have r := GlobalTheory.T.fundamental_domain_independent_integral G.M.μ (Q ⊔ N) ν hνinv 𝓓 _ h𝓓.nullMeasurableSet h𝓓₂.nullMeasurableSet _ _ s₁ s₂ φ hφ
    (fun p hp => hQNS hp)
  rw [hint]
  have hE₂0 : ν E₂ ≠ 0 := by
    intro h0; apply hE₁0; rw [← hE12, h0, mul_zero]
  have hE₂top : ν E₂ ≠ ⊤ := by
    intro h1; apply hE₁top; rw [← hE12, h1, ENNReal.mul_top hc0]
  rw [← hE12, mul_comm (ENNReal.ofReal _) (ν E₂), mul_assoc] at r
  exact ((ENNReal.mul_right_inj hE₂0 hE₂top).1 r).symm

end GlobalTheory.ThK.LeviModulus
