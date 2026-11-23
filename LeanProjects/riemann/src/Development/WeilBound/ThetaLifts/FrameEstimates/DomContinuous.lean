import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem dom_continuous (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hp : IsPair B M χX χW om r s r' s') {𝓕}
    (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) (hsb : φ ∈ SB _) (f : SInf F (Fin n × Fin d)) :
    Continuous (M.I om (pureA F f φ)) := by
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨i1, i2, -, -, -, -, -, hb⟩ := hT F E σ hp.base.cm d W.J hJ'
  obtain ⟨p, k, G, -, hG, hfin, hbd⟩ := hD φ hφ
  have hc := ((hB F E σ B n d X W M χX χW om r s r' s' hp).1 _ (pureA_mem f hsb)).1
  haveI : FirstCountableTopology (UA σ W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i2
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds h₀
  obtain ⟨C, hC⟩ := hb K hK
  have hpf : 0 ≤ p f := apply_nonneg p f
  refine continuousAt_of_dominated (bound := fun g => p f * (C : ℝ) ^ k * (G g).toReal)
    (Eventually.of_forall fun h => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable) ?_
    ((integrable_toReal_of_lintegral_ne_top hG.aemeasurable hfin.ne).const_mul _)
    (Eventually.of_forall fun g => (hc.comp (continuous_const.prodMk continuous_id)).continuousAt)
  filter_upwards [hK0] with h hh
  filter_upwards [ae_lt_top hG hfin.ne] with g hg
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.ne) (hbd f g h)
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at e
  refine e.trans ?_
  have : (ht h : ℝ) ≤ C := hC h hh
  gcongr

theorem dom_bound (hp : IsPair B M χX χW om r s r' s') {𝓕} (hD : Dom M om 𝓕) {φ} (hφ : φ ∈ 𝓕) :
    ∃ k : ℕ, ∀ f : SInf F (Fin n × Fin d), ∃ C : ℝ, ∀ h, ‖M.I om (pureA F f φ) h‖ ≤ C * (ht h : ℝ) ^ k := by
  obtain ⟨p, k, G, -, hG, hfin, hb⟩ := hD φ hφ
  refine ⟨k, fun f => ⟨p f * (∫⁻ g in M.dom, G g ∂M.μ).toReal, fun h => ?_⟩⟩
  have h1 : ‖M.I om (pureA F f φ) h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * ∫⁻ g in M.dom, G g ∂M.μ := by
    rw [← lintegral_const_mul _ hG]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun g => hb f g h)
  have e := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) h1
  rw [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (apply_nonneg p f) (by positivity))] at e
  exact e.trans (le_of_eq (by ring))

end

theorem iUMG_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hD : IDer) (hL : Level) (hI : IInv) : IUMG := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f hf
  obtain ⟨k, hk⟩ := dom_bound hp hdom hφ
  refine ⟨⟨k, {u | ∃ f₁ ∈ M.Pol B.ψ B.emb, u = M.I om (pureA F f₁ φ)}, ⟨f, hf, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f₁, hf₁, rfl⟩
    refine ⟨dom_continuous hB hT hE hp hdom hφ hsb f₁, hk f₁, fun γ hγ => ?_⟩
    obtain ⟨f₂, hf₂, -, hd⟩ := (hD F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hdom φ hφ hsb f₁ hf₁).1 γ hγ
    exact ⟨_, ⟨f₂, hf₂, rfl⟩, hd⟩
  · obtain ⟨U, hU, hu⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp φ hsb
    refine ⟨U, hU, fun u huU h1 h => ?_⟩
    rw [← (hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem f hsb)).2.2 h u, hu u huU h1]

end PositivityTheory.ThKEst

end
