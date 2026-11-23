import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralSmoothAlongRealLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

noncomputable section

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives

namespace GlobalTheory.ThK.ZFinHasDer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem exists_der_both (hKP : GlobalTheory.ThK.KP) (hT : IsTriple B G X om om') {γ} (hγ : γ ∈ Lines σ G.W) :
    ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M,
      (∀ y, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ y) (Φ₁ y) 0) ∧ ∀ g h,
      HasDerivAt (fun s : ℝ => theta om Φ g (h * γ (Multiplicative.ofAdd s))) (theta om Φ₁ g h) 0 := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_lieDerivative_polynomialFock_seesaw B G X om om' hT γ hγ
  have hle := GlobalTheory.ThKDer.polData_le (B := B) hT.geo.hM
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, hf, φ, hSB, hvac, rfl⟩ := hx
    refine ⟨pure (δ f) φ, Submodule.subset_span ⟨δ f, (hδ f hf).1, φ, hSB, hvac, rfl⟩, fun y => ?_,
      fun g h => GlobalTheory.ThKDer.kerDer F E σ B a a' G X om om' hKP hT γ hγ f hf (δ f) (hδ f hf).2 φ hSB hvac g h⟩
    have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hvac.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    exact (hδ f hf).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd) y
  | zero =>
    exact ⟨0, zero_mem _, fun y => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ),
      fun g h => by simpa [GlobalTheory.ThKDer.theta_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨x₁, hx₁, px, ex⟩ := ihx
    obtain ⟨y₁, hy₁, py, ey⟩ := ihy
    refine ⟨x₁ + y₁, add_mem hx₁ hy₁, fun z => ?_, fun g h => ?_⟩
    · simp only [map_add, Pi.add_apply]
      exact (px z).add (py z)
    · rw [GlobalTheory.ThKDer.theta_add hT (hle hx₁) (hle hy₁)]
      simp only [GlobalTheory.ThKDer.theta_add hT (hle hx) (hle hy)]
      exact (ex g h).add (ey g h)
  | smul c x hx ihx =>
    obtain ⟨x₁, hx₁, px, ex⟩ := ihx
    refine ⟨c • x₁, Submodule.smul_mem _ c hx₁, fun z => ?_, fun g h => ?_⟩
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (px z).const_mul c
    · simp only [GlobalTheory.ThKDer.theta_smul]
      exact (ex g h).const_mul c

theorem I_translate (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (k h : UA σ G.W.J) :
    G.M.I om (om (1, k) Φ) h = G.M.I om Φ (h * k) := by
  simp only [Model.I, theta]
  congr 1
  funext g
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem hasDerivAt_I_derR : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ γ : ℝ → GAd σ (c • G.W.J.map σ), IsRealLine σ (c • G.W.J.map σ) γ →
      ∀ h, HasDerivAt (fun t : ℝ => G.M.I om (om (1, back hσ G.W.J hc γ t) Φ) h) (G.M.I om (derR om (back hσ G.W.J hc γ) Φ) h) 0 := by
  intro F E _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc _ Φ hΦ γ hγ h
  obtain ⟨γL, hγL, eγ⟩ := GlobalTheory.ThKDer.lineA F E σ hσ hT.base.cm G.W c hc γ hγ
  have eb : back hσ G.W.J hc γ = fun t => γL (Multiplicative.ofAdd t) := funext eγ
  obtain ⟨Φ₁, h1, p1, d1⟩ := exists_der_both hKP hT hγL Φ hΦ
  obtain ⟨Φ₂, h2, -, d2⟩ := exists_der_both hKP hT hγL Φ₁ h1
  have e1 : derR om (back hσ G.W.J hc γ) Φ = Φ₁ := by
    rw [eb]; exact funext fun y => (p1 y).deriv
  rw [e1, eb]
  simp only [I_translate]
  exact GlobalTheory.ThKDer.hasDerivAt_I hKP hT hγL hΦ h1 h2 d1 d2 h

end GlobalTheory.ThK.ZFinHasDer

end
