import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorRationalOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleVanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.ConeV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro Φ ⟨f, -, φ, hSB, hvac, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hvac.and hM.std).mono fun v hv => hv.1.trans hv.2)

theorem hasLaw_mul {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ : Chr F E} {z : ℝ}
    {T : UA σ W.J → ℂ} (hT : HasLaw W₁ H' χ z T) (c : ℂ) : HasLaw W₁ H' χ z (fun h => c * T h) := by
  intro t m hm h
  simp only [hT t m hm h]; ring

theorem coneV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ ∈ PolData B G.M, ∃ (c : UA σ G.V.J → UA σ G.W.J → ℂ) (A₁ : UA σ G.W.J → ℂ), (∀ g, IsCT H' (theta om Φ g) (c g)) ∧ HasLaw G₁.W H' X.α (((b + 2 : ℕ) : ℝ) / 2) A₁ ∧ ∀ h, IntegrableOn (fun g => c g h - C₀ * thetaSum F (e (om (g, h) Φ))) G.M.dom G.M.μ ∧ ∫ g in G.M.dom, (c g h - C₀ * thetaSum F (e (om (g, h) Φ))) ∂G.M.μ = A₁ h := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e he
  classical
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain rfl : V₁ = G.V := hC.eV
  by_cases hex : ∃ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G.V W₁) (om₁' : Rep σ V₁' W₁),
      IsTriple B G X om om' ∧ IsTriple B (⟨p₁, q₁, G.V, V₁', W₁, M₁, M₁'⟩ : Geo σ a b) X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' hT hT₁ => (hex ⟨X, om, om', om₁, om₁', hT, hT₁⟩).elim⟩
  obtain ⟨X₀, om₀, om₀', om₁₀, om₁₀', hT₀, hT₁₀⟩ := hex
  have hM₁ : M₁.IsGood B.ψ := hT₁₀.geo.hM
  have hH' : H'.IsAdapted σ B G.W W₁ a (a + b + 1) := hC.hH'
  by_cases hiso : ∃ x : Fin a → E, x ≠ 0 ∧ form σ G.V.J x x = 0
  · obtain ⟨V₂, n₁, X₁, H₀, j₀, j₁, M₂, e₂, hV₂, hH₀, hM₂, he₂⟩ :=
      GlobalTheory.T.config_b_triple_constant_term hKP F E σ B a b G _ H H' hC X₀ om₀ om₀' om₁₀ om₁₀' hT₀ hT₁₀ hiso
    let M' : Model σ (reS G.V V₂) G.W := ⟨G.M.co, G.M.vac, G.M.μ, G.M.dom⟩
    let M₁'' : Model σ (reS G.V V₂) W₁ := ⟨M₁.co, M₁.vac, M₁.μ, M₁.dom⟩
    have hM₁'' : M₁''.IsGood B.ψ := ⟨hM₁.rat, hM₁.vac, hM₁.std, hM₁.haar, hM₁.dom⟩
    have he' : IsEv B M' M₁'' 1 H'.ι (iso0 a H') e := ⟨he.maps, he.Heisenberg₂, he.inv, he.loc⟩
    have he₂' : IsEv B M' M₂ H₀.ι H'.ι (isoA H₀ H') e₂ := ⟨he₂.maps, he₂.Heisenberg₂, he₂.inv, he₂.loc⟩
    have hH'' : H'.IsAdapted σ B G.W W₁ a (a + b + 1) := hH'
    obtain ⟨C₀, hC₀, -, h2⟩ := GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B a (a + (b + 2)) (a + b) (reS G.V V₂) G.W W₁ M' M₁'' H' a (a + b + 1)
      hH'' hM₁'' e he'
    obtain ⟨C₁, -, h3⟩ := h2 n₁ X₁ H₀ j₀ j₁ M₂ hH₀ hM₂ e₂ he₂'
    refine ⟨C₀, hC₀, fun X om om' om₁ om₁' hT hT₁ Φ hΦ => ?_⟩
    have hw : ∀ x : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0}, ∃ γ : UA σ G.V.J,
        γ ∈ ratU σ G.V.J ∧ mat γ *ᵥ incV F x.1 = incV F H₀.x := fun x =>
      GlobalTheory.T.isotropic_vector_rational_orbit F E σ B a n₁ (reS G.V V₂) X₁ H₀ j₀ j₁ (a - G.p) G.p hT.base hV₂ hH₀ x.1 x.2.1 x.2.2
    choose γ hγ using hw
    have hP0 := GlobalTheory.ThK.Inhab.pairV hT
    have hP : IsPair B M' X.β (X.β / X.α) om (a - G.p) G.p (a + (b + 2) - (G.p + G.q)) (G.p + G.q) :=
      { base := hP0.base, herm := hV₂, skew := hP0.skew,
        good := ⟨hP0.good.rat, hP0.good.vac, hP0.good.std, hP0.good.haar, hP0.good.dom⟩,
        hX := hP0.hX, hW := hP0.hW, resX := hP0.resX, resW := hP0.resW, weil := hP0.weil }
    have h4 := h3 γ (fun x => ⟨(hγ x).1, (hγ x).2⟩) X.β (X.β / X.α) om _ _ _ _ hP Φ
      (polData_le_schA B G.M hT.geo.hM hΦ)
    have hI := GlobalTheory.T.config_b_triple_integral hKP F E σ B a b G _ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he₂ γ hγ Φ hΦ
    have hL := GlobalTheory.T.config_b_triple_vanishing hKP F E σ B a b G _ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he₂ γ hγ Φ hΦ
    refine ⟨fun g h => C₀ * thetaSum F (e (om (g, h) Φ)) +
        C₁ * ∑' x, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (γ x * g, h) Φ))),
      fun h => C₁ * ∫ g in G.M.dom, ∑' x, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ,
      fun g => (h4 g).2, hasLaw_mul hL C₁, fun h => ⟨?_, ?_⟩⟩
    · simp only [add_sub_cancel_left]
      exact (hI h).const_mul C₁
    · simp only [add_sub_cancel_left]
      exact integral_const_mul C₁ _
  · push_neg at hiso
    have han : ∀ x, form σ G.V.J x x = 0 → x = 0 := fun x hx => by
      by_contra hne
      exact hiso x hne hx
    obtain ⟨C₀, hC₀, h1, -⟩ := GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ G.M M₁ H' a (a + b + 1)
      hH' hM₁ e he
    refine ⟨C₀, hC₀, fun X om om' om₁ om₁' hT hT₁ Φ hΦ => ?_⟩
    refine ⟨fun g h => C₀ * thetaSum F (e (om (g, h) Φ)), 0,
      fun g => h1 han X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT) Φ (polData_le_schA B G.M hT.geo.hM hΦ) g,
      fun t m _ h => by simp, fun h => ⟨?_, ?_⟩⟩
    · simp
    · simp

end GlobalTheory.ThK.ConeV

end
