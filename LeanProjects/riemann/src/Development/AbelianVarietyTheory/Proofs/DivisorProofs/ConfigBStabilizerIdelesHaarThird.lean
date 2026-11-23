import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfolding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBHaarMeasureIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBHaarMeasureUnfoldingStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section
namespace GlobalTheory.ConeJBPass

theorem integral_lin4 {α V : Type} [MeasurableSpace α] {ρ : Measure α} (L : V → α → ℂ) (hL : ∀ v, Integrable (L v) ρ)
    (x₁ x₂ x₃ x₄ : V) (A A' : ℂ) :
    (∫ q, L x₁ q ∂ρ) - A' * (∫ q, L x₂ q ∂ρ) - A * (∫ q, L x₃ q ∂ρ) + A * A' * (∫ q, L x₄ q ∂ρ) =
      ∫ q, (L x₁ q - A' * L x₂ q - A * L x₃ q + A * A' * L x₄ q) ∂ρ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (show Integrable (fun q => L x₁ q) ρ from hL x₁) (show Integrable (fun q => A' * L x₂ q) ρ from (hL x₂).const_mul A'),
    ← integral_sub (show Integrable (fun q => L x₁ q - A' * L x₂ q) ρ from (hL x₁).sub ((hL x₂).const_mul A'))
      (show Integrable (fun q => A * L x₃ q) ρ from (hL x₃).const_mul A),
    ← integral_add (show Integrable (fun q => L x₁ q - A' * L x₂ q - A * L x₃ q) ρ from ((hL x₁).sub ((hL x₂).const_mul A')).sub ((hL x₃).const_mul A))
      (show Integrable (fun q => A * A' * L x₄ q) ρ from (hL x₄).const_mul (A * A'))]

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in

theorem pass : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∀ g : UA σ G.W.J,
      (∀ (k : K) (l : (AE F E)ˣ), ∃ c : UA σ G₁.W.J → ℂ, IsCT H₂ (G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ')))) c ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) c ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) c) →
      ∃ C : UA σ G₁.W.J → ℂ, IsCT H₂ (fun v => ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ'))) v * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2) ∂μ ∂μK) C ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) C ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) C := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂ e W₂ H₂ i₀ i₁ hH₂
  obtain ⟨s₁, hs₁⟩ := GlobalTheory.T.configuration_b_haar_measure_unfolding hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂ e W₂ H₂ i₀ i₁ hH₂
  refine ⟨s₁, fun s hs g hc => ?_⟩
  obtain ⟨_, _, _⟩ := GlobalTheory.UnfoldQ.ideles_lcsc F E
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) :=
    GlobalTheory.StabCpt.isCompact_of_isStab hKP F E σ B (b + 2) G.V' G.q (b + 2 - G.q) K hT.base hT.geo.hV' hK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : IsFiniteMeasure μK := inferInstance
  haveI : SFinite μK := inferInstance
  haveI : SFinite (μK.prod μ) := inferInstance
  set z : ℂ := s + ((a : ℂ) + 1) / 2 with hz
  have hint : ∀ (μ' : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ' → μ' 𝓕 = 1 → ∀ v : UA σ G₁.W.J,
      Integrable (fun p : unip σ G₁.W H₂ × (K × (AE F E)ˣ) => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, g) Φ'))) (p.1.1 * v) * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ z)
        ((μ'.restrict 𝓕).prod (μK.prod μ)) :=
    fun μ' 𝓕 h1 h2 h3 v => ⟨GlobalTheory.T.configuration_b_haar_measure_integral hKP F E σ B a b G G₁ H H' hC e' he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' V V' W₁' hT₂ e W₂ H₂ i₀ i₁ hH₂ s g v μ' 𝓕 h1, hs₁ s hs g v μ' 𝓕 h1 h2 h3⟩
  choose c hcCT hcJ1 hcJ2 using hc
  by_cases hex : ∃ (μ₀ : Measure (unip σ G₁.W H₂)) (𝓕₀ : Set (unip σ G₁.W H₂)), μ₀.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕₀ μ₀ ∧ μ₀ 𝓕₀ = 1
  swap
  · refine ⟨0, fun μ' 𝓕 h1 h2 h3 => absurd ⟨μ', 𝓕, h1, h2, h3⟩ hex, ?_, ?_⟩ <;> exact fun _ _ _ _ _ _ _ => by simp
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h1₀⟩ := hex
  have hfin : ∀ (μ' : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ' 𝓕 = 1 → IsFiniteMeasure (μ'.restrict 𝓕) :=
    fun μ' 𝓕 h3 => ⟨by rw [Measure.restrict_apply_univ, h3]; exact ENNReal.one_lt_top⟩
  have hslice : ∀ (μ' : Measure (unip σ G₁.W H₂)) (𝓕 : Set (unip σ G₁.W H₂)), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G₁.W.J).subgroupOf (unip σ G₁.W H₂)) 𝓕 μ' → μ' 𝓕 = 1 → ∀ (v : UA σ G₁.W.J) (q : K × (AE F E)ˣ),
      c q.1 q.2 v * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z = ∫ u in 𝓕, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' q.2) (om' (q.1.1, g) Φ'))) (u.1 * v) * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z ∂μ' := by
    intro μ' 𝓕 h1 h2 h3 v q
    rw [hcCT q.1 q.2 μ' 𝓕 h1 h2 h3 v, integral_mul_const, integral_mul_const]
  have hcint : ∀ v : UA σ G₁.W.J, Integrable (fun q : K × (AE F E)ˣ => c q.1 q.2 v * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) (μK.prod μ) := by
    intro v
    haveI := hfin μ₀ 𝓕₀ h1₀
    refine (hint μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀ v).integral_prod_right.congr (Eventually.of_forall fun q => ?_)
    exact (hslice μ₀ 𝓕₀ hμ₀ h𝓕₀ h1₀ v q).symm
  have hCq : ∀ v : UA σ G₁.W.J, (∫ k, ∫ l, c k l v * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK) =
      ∫ q, c q.1 q.2 v * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z ∂(μK.prod μ) := fun v =>
    (integral_prod (fun q : K × (AE F E)ˣ => c q.1 q.2 v * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) (hcint v)).symm
  refine ⟨fun v => ∫ k, ∫ l, c k l v * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK, ?_, ?_, ?_⟩
  · intro μ' 𝓕 h1 h2 h3 v
    haveI := hfin μ' 𝓕 h3
    have hI := hint μ' 𝓕 h1 h2 h3 v
    have e1 : (fun u : unip σ G₁.W H₂ => ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ'))) (u.1 * v) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ ∂μK) =ᵐ[μ'.restrict 𝓕]
        fun u => ∫ q, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' q.2) (om' (q.1.1, g) Φ'))) (u.1 * v) * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z ∂(μK.prod μ) := by
      filter_upwards [hI.prod_right_ae] with u hu
      exact (integral_prod (fun q : K × (AE F E)ˣ => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' q.2) (om' (q.1.1, g) Φ'))) (u.1 * v) * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) hu).symm
    beta_reduce
    rw [hCq v, integral_congr_ae e1,
      integral_integral_swap (f := fun (u : unip σ G₁.W H₂) (q : K × (AE F E)ˣ) => G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' q.2) (om' (q.1.1, g) Φ'))) (u.1 * v) * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) hI]
    exact integral_congr_ae (Eventually.of_forall fun q => hslice μ' 𝓕 h1 h2 h3 v q)
  all_goals
    intro t t' m m' hm hm' v
    beta_reduce
    rw [hCq, hCq, hCq, hCq]
    refine (integral_lin4 (fun v (q : K × (AE F E)ˣ) => c q.1 q.2 v * (X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) hcint _ _ _ _ _ _).trans ?_
    refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (integral_zero _ _)
    first
      | have hj := hcJ1 q.1 q.2 t t' m m' hm hm' v
        linear_combination ((X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) * hj
      | have hj := hcJ2 q.1 q.2 t t' m m' hm hm' v
        linear_combination ((X.ν q.2 : ℂ) * ((absE F E q.2 : ℝ) : ℂ) ^ z) * hj

end GlobalTheory.ConeJBPass
end
