import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarNonarchimedean
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawEvaluationHaarArchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTripleCompatibilityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTripleIntegralEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeriesRepresentativesSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeriesLocallyUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDoubleSeriesInterchangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConstantTermIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReconfiguredTripleLocalIdentity
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

theorem ctMid_unfold : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ → ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      ∀ Gf : UA σ G.W.J → ℂ, (∀ g, IsCT H₂ (fun h₁ => (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (emb h₁ * g)) (fun h₁ => Gf (emb h₁ * g))) →
      ∃ (T₁ : Set (UA σ G₁.W.J)) (κ : ℂ) (ν : @Measure (AE F E) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
        IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T))
          (fun h => κ * ∑' γ : T₁, ∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν) ∧
        (∀ h, Summable fun γ : T₁ => ‖∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν‖) ∧
        ∀ h (γ : T₁), Integrable (fun c => Gf (w * nn c * emb γ.1 * h)) ν := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ V V' W₁' hT' e
    W₂ H₂ i₀ i₁ hH₂ emb hemb w hw nn hnn
  refine ⟨0, fun T hTr s _ hL Gf hG => ?_⟩
  set f := GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) with hfdef
  have hf : Measurable f := GlobalTheory.ConeSmallSerInt.measurable_coneI hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X
    om om' om₁ om₁' hT hT₁ Φ' hΦ _
  have hinv : ∀ p ∈ ratU σ G.W.J, GlobalTheory.ConeSmallSer.StabLn H'.x p → ∀ h, f (p * h) = f h := fun p hp hs h =>
    GlobalTheory.T.seesaw_evaluation_haar_nonarchimedean hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ _ p hp hs h
  have hun : ∀ u ∈ unip σ G.W H', ∀ h, f (u * h) = f h := fun u hu h =>
    GlobalTheory.T.seesaw_evaluation_haar_archimedean hK F E σ B a b G G₁ H H' hC e' he K μK μ hKs hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ _ u hu h
  clear_value f
  obtain ⟨R, hR⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ G.W G₁.W H' _ _ _ _ hT.base hT.geo.hW hC.hH'
  obtain ⟨hembr, hwr, hwinj, hwsh⟩ := GlobalTheory.T.reconfigured_triple_compatibility F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT' e W₂ H₂ i₀ i₁
    hH₂ emb hemb w hw nn hnn
  obtain ⟨T₁, hT₁r, ε, hε⟩ := GlobalTheory.T.reconfigured_triple_integral_equality F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT' e W₂ H₂ i₀ i₁
    hH₂ emb hemb w hw nn hnn T hTr
  have hsb := GlobalTheory.T.cone_series_locally_uniform F E σ _ _ G.W H' R hR T hTr f hinv hL
  have hbc : ∀ g, ∃ C : ℝ, ∀ u ∈ unip σ G.W H', Summable (fun c : E => ‖f (w * nn (inclR (F := F) (AF F) c) * u * g)‖) ∧
      ∑' c : E, ‖f (w * nn (inclR (F := F) (AF F) c) * u * g)‖ ≤ C := by
    intro g
    obtain ⟨C, hCb⟩ := hsb g
    refine ⟨C, fun u hu => ?_⟩
    have h1 := GlobalTheory.T.cone_series_representatives_sum F E σ _ G.W.J H'.x T hTr f hinv E (fun c => w * nn (inclR (F := F) (AF F) c)) hwr hwinj (u * g) C
      (hCb u hu).1 (hCb u hu).2
    simpa only [mul_assoc] using h1
  obtain ⟨κ, ν, hκ, hν, hcore⟩ := GlobalTheory.T.reconfigured_triple_local_identity F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V V' W₁' hT' e W₂ H₂ i₀ i₁
    hH₂ emb hemb w hw nn hnn f hf hinv hun hbc Gf hG
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.UnipCT.topFacts (F := F) σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI := GlobalTheory.UnipCT.countable_ratU (σ := σ) G₁.W.J
  haveI : Countable T₁ := Function.Injective.countable (f := fun t : T₁ => (⟨t.1, hT₁r t.2⟩ : ratU σ G₁.W.J))
    fun x y hxy => Subtype.ext (congrArg (fun z : ratU σ G₁.W.J => z.1) hxy)
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hfε : ∀ (t : GlobalTheory.ConeSmallSer.midSet H'.x T) (v : UA σ G.W.J),
      f (t.1 * v) = f (w * nn (inclR (F := F) (AF F) (ε t).2) * emb (ε t).1.1 * v) := by
    intro t v
    have hp : w * nn (inclR (F := F) (AF F) (ε t).2) * emb (ε t).1.1 * t.1⁻¹ ∈ ratU σ G.W.J :=
      mul_mem (mul_mem (hwr _) (hembr _ (hT₁r (ε t).1.2))) (inv_mem (hTr.1 t.2.1))
    rw [← hinv _ hp (hε t) (t.1 * v)]
    congr 1
    group

  have hsumε : ∀ v : UA σ G.W.J, Summable (fun t : T => ‖f (t.1 * v)‖) →
      Summable (fun p : T₁ × E => ‖f (w * nn (inclR (F := F) (AF F) p.2) * emb p.1.1 * v)‖) ∧
      ∑' p : T₁ × E, ‖f (w * nn (inclR (F := F) (AF F) p.2) * emb p.1.1 * v)‖ ≤ ∑' t : T, ‖f (t.1 * v)‖ := by
    intro v hs
    have hfun : (fun p : T₁ × E => ‖f (w * nn (inclR (F := F) (AF F) p.2) * emb p.1.1 * v)‖) =
        (fun t : GlobalTheory.ConeSmallSer.midSet H'.x T => ‖f (t.1 * v)‖) ∘ ε.symm := by
      funext p
      simp only [Function.comp_apply, hfε, Equiv.apply_symm_apply]
    let ι : GlobalTheory.ConeSmallSer.midSet H'.x T → T := fun t => ⟨t.1, t.2.1⟩
    have hι : Function.Injective ι := fun x y hxy => Subtype.ext (congrArg (fun z : T => z.1) hxy)
    have hs' : Summable (fun t : GlobalTheory.ConeSmallSer.midSet H'.x T => ‖f (t.1 * v)‖) := by
      have h0 := hs.comp_injective hι
      exact h0
    rw [hfun]
    refine ⟨ε.symm.summable_iff.2 hs', ?_⟩
    exact (ε.symm.tsum_eq (fun t : GlobalTheory.ConeSmallSer.midSet H'.x T => ‖f (t.1 * v)‖)).le.trans
      (hs'.tsum_le_tsum_of_inj ι hι (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hs)

  have key : ∀ (μ' : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ' → μ' 𝓕 = 1 → ∀ h,
      (∫ u in 𝓕, GlobalTheory.ConeSmallSer.partSum f (GlobalTheory.ConeSmallSer.midSet H'.x T) (u.1 * h) ∂μ' =
        ∑' γ : T₁, ∫ u in 𝓕, ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * emb γ.1 * (u.1 * h)) ∂μ') ∧
      Summable (fun γ : T₁ => ‖∫ u in 𝓕, ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * emb γ.1 * (u.1 * h)) ∂μ'‖) ∧
      ∀ γ : T₁, ∫ u in 𝓕, ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * emb γ.1 * (u.1 * h)) ∂μ' =
        κ * ∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν := by
    intro μ' 𝓕 hμ' h𝓕 h1 h
    obtain ⟨Ch, hCh⟩ := hsb h
    let Φ : T₁ → E → unip σ G.W H' → ℂ := fun γ c u => f (w * nn (inclR (F := F) (AF F) c) * emb γ.1 * (u.1 * h))
    have hΦm : ∀ γ c, Measurable (Φ γ c) := fun γ c =>
      hf.comp ((continuous_const.mul (continuous_subtype_val.mul continuous_const))).measurable
    have hΦb : ∀ u, Summable (fun p : T₁ × E => ‖Φ p.1 p.2 u‖) ∧ ∑' p : T₁ × E, ‖Φ p.1 p.2 u‖ ≤ Ch := by
      intro u
      obtain ⟨hs1, hs2⟩ := hsumε (u.1 * h) (hCh u.1 u.2).1
      exact ⟨hs1, hs2.trans (hCh u.1 u.2).2⟩
    obtain ⟨hF1, hF2⟩ := GlobalTheory.T.integral_double_series_interchange (unip σ G.W H') μ' 𝓕 (by rw [h1]; exact ENNReal.one_ne_top) T₁ E Φ hΦm Ch hΦb
    refine ⟨?_, hF2, fun γ => ?_⟩
    · rw [← hF1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      show ∑' t : GlobalTheory.ConeSmallSer.midSet H'.x T, f (t.1 * (u.1 * h)) = _
      rw [← ε.symm.tsum_eq]
      refine tsum_congr fun p => ?_
      rw [hfε, Equiv.apply_symm_apply]
    · let Ψ : UA σ G.W.J → ℂ := fun v => ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * v * (emb γ.1 * h))
      have hΨ : ∀ δ ∈ ratU σ G.W.J ⊓ unip σ G.W H', ∀ u ∈ unip σ G.W H', Ψ (δ * u) = Ψ u := by
        intro δ hδ u _
        obtain ⟨a₀, ha₀⟩ := hwsh δ hδ
        have e1 : ∀ c : E, f (w * nn (inclR (F := F) (AF F) c) * (δ * u) * (emb γ.1 * h)) =
            f (w * nn (inclR (F := F) (AF F) (c + a₀)) * u * (emb γ.1 * h)) := by
          intro c
          have hp : w * nn (inclR (F := F) (AF F) c) * δ * (w * nn (inclR (F := F) (AF F) (c + a₀)))⁻¹ ∈ ratU σ G.W.J :=
            mul_mem (mul_mem (hwr c) hδ.1) (inv_mem (hwr (c + a₀)))
          calc f (w * nn (inclR (F := F) (AF F) c) * (δ * u) * (emb γ.1 * h))
              = f ((w * nn (inclR (F := F) (AF F) c) * δ * (w * nn (inclR (F := F) (AF F) (c + a₀)))⁻¹) *
                  (w * nn (inclR (F := F) (AF F) (c + a₀)) * u * (emb γ.1 * h))) := by congr 1; group
            _ = _ := hinv _ hp (ha₀ c) _
        show ∑' c : E, _ = ∑' c : E, _
        simp only [e1]
        exact (Equiv.addRight a₀).tsum_eq (fun c => f (w * nn (inclR (F := F) (AF F) c) * u * (emb γ.1 * h)))
      have hc := GlobalTheory.T.levi_constant_term_integral F E σ _ _ G.W G₁.W H' γ.1 (emb γ.1) (hembr _ (hT₁r γ.2)) (hemb γ.1) Ψ hΨ μ' 𝓕 hμ' h𝓕 h1
      have e2 : ∀ u : unip σ G.W H', Ψ (emb γ.1 * u.1 * (emb γ.1)⁻¹) = ∑' c : E, Φ γ c u := by
        intro u
        refine tsum_congr fun c => ?_
        show f _ = f _
        congr 1
        group
      have e3 := (hcore μ' 𝓕 hμ' h𝓕 h1 (emb γ.1 * h)).2
      simp only [e2] at hc
      rw [hc, e3]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
      simp only [mul_assoc]
  obtain ⟨μ₀, 𝓕₀, hμ₀, h𝓕₀, h₀⟩ := GlobalTheory.T.exists_fundamental_domain_unipotent F E σ B _ _ G.W G₁.W H' _ _ _ _ hT.base hT.geo.hW hC.hH'
  refine ⟨T₁, κ, ν, hν, ?_, fun h => ?_, fun h γ => ?_⟩
  · intro μ' 𝓕 hμ' h𝓕 h1 h
    obtain ⟨k1, -, k3⟩ := key μ' 𝓕 hμ' h𝓕 h1 h
    rw [k1]
    beta_reduce
    rw [← tsum_mul_left]
    exact tsum_congr fun γ => (k3 γ).symm
  · obtain ⟨-, k2, k3⟩ := key μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ h
    have e4 : ∀ γ : T₁, ‖∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν‖ =
        ‖κ‖⁻¹ * ‖∫ u in 𝓕₀, ∑' c : E, f (w * nn (inclR (F := F) (AF F) c) * emb γ.1 * (u.1 * h)) ∂μ₀‖ := by
      intro γ
      rw [k3 γ, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hκ), one_mul]
    simp only [e4]
    exact k2.mul_left _
  · have h5 := (hcore μ₀ 𝓕₀ hμ₀ h𝓕₀ h₀ (emb γ.1 * h)).1
    simpa only [mul_assoc] using h5

end GlobalTheory.ConeSmallMidJB

end
