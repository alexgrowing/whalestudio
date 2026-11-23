import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WStableSSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleCharacterTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalNormIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLiftEquality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleThetaEquality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThetaProjectionLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem linT (hKP : KP) (hT : IsTriple B G X om om') : ∀ Ψ₁ ∈ PolData B G.M, ∀ Ψ₂ ∈ PolData B G.M, ∀ c : ℂ,
    G.M.I om (Ψ₁ + Ψ₂) = G.M.I om Ψ₁ + G.M.I om Ψ₂ ∧ G.M.I om (c • Ψ₁) = c • G.M.I om Ψ₁ := by
  intro Φ hΦ Ψ hΨ c
  have hP := GlobalTheory.ThK.Inhab.pairV hT
  have hcond : a + a' + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    left
    omega
  have hconv := (GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ hP hcond).1
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin a × Fin (a + a')), om x Φ ∈ schA F (Fin a × Fin (a + a')) :=
    fun x Φ hΦ => (IsUWeilPair.isUSplitting hT.weil).pres x Φ hΦ
  have hPol : PolData B G.M ≤ schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2)
  have hΦS := hPol hΦ
  have hΨS := hPol hΨ
  refine ⟨?_, ?_⟩
  · funext h
    have e : ∀ g, theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := fun g => by
      simp only [theta, map_add]
      exact thetaSum_add F (pres _ Φ hΦS) (pres _ Ψ hΨS)
    have iΦ := (hconv Φ hΦS).1 h
    have iΨ := (hconv Ψ hΨS).1 h
    simp only [Model.I, Pi.add_apply]
    rw [show (fun g => theta om (Φ + Ψ) g h) = fun g => theta om Φ g h + theta om Ψ g h from funext e,
      MeasureTheory.integral_add iΦ iΨ]
  · funext h
    have e : ∀ g, theta om (c • Φ) g h = c * theta om Φ g h := fun g => by
      simp only [theta, map_smul]
      exact thetaSum_smul F c _
    simp only [Model.I, Pi.smul_apply, smul_eq_mul]
    rw [show (fun g => theta om (c • Φ) g h) = fun g => c * theta om Φ g h from funext e, MeasureTheory.integral_const_mul]

theorem invVT (hK : KP) (hT : IsTriple B G X om om') : ∀ Φ ∈ PolData B G.M,
    (∀ v : Pl F, ∀ g ∈ UAt σ G.V (evFin F v), G.M.I om (om (g, 1) Φ) = G.M.I om Φ) ∧
    ∀ k ∈ KInf σ G.V B.emb, G.M.I om (om (k, 1) Φ) = G.M.I om Φ := by
  intro Φ hΦ
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  have hS : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) := by
    refine (Submodule.span_le.2 ?_) hΦ
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hp.good.std).mono fun v hv => hv.1.trans hv.2)
  exact ⟨fun v g _ => GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp g Φ hS,
    fun k _ => GlobalTheory.ThetaIntegralInv.integral_translate hK.base hp k Φ hS⟩

theorem lieVT (hK : KP) (hT : IsTriple B G X om om') : ∀ γ ∈ Lines σ G.V, ∀ Φ ∈ PolData B G.M, ∀ Φ₁ ∈ PolData B G.M,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → G.M.I om Φ₁ = 0 := by
  intro γ hγ Φ hΦ Φ₁ _ hd
  have hp := GlobalTheory.ThK.Inhab.pairV hT
  have hPol : PolData B G.M ≤ schA F (Fin a × Fin (a + a')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, -, φ, hSB, hev, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hp.good.std).mono fun v hv => hv.1.trans hv.2)
  have hw : a + a' + 2 * min (a - G.p) G.p < 2 * a := by
    have h1 := hT.geo.eBig
    have h2 := min_le_right (a - G.p) G.p
    omega
  obtain ⟨Ψ, -, hΨ, hI⟩ := GlobalTheory.ThetaLieInt.exists_deriv_I_eq_zero hK hp (Or.inl hw) hγ (hPol hΦ)
  rw [show Φ₁ = Ψ from funext fun x => (hd x).unique (hΨ x), hI]

theorem lieWT (hK : KP) (hT : IsTriple B G X om om') : ∀ γ ∈ Lines σ G.W, ∀ Φ ∈ PolData B G.M, ∀ Φ₁ ∈ PolData B G.M,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) →
    ∀ h, HasDerivAt (fun t : ℝ => G.M.I om Φ (h * γ (Multiplicative.ofAdd t))) (G.M.I om Φ₁ h) 0 := by
  intro γ hγ Φ hΦ Φ₁ _ hd h
  have hineq : (a + a') + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    left
    have := min_le_right (a - G.p) G.p
    omega
  obtain ⟨hc, hcont⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 hineq
  obtain ⟨Ψ, -, hΨ, hI⟩ := GlobalTheory.ThetaIntegralLine.exists_deriv hK.base G.M B.ψ _ _ om hT.base.cm hT.base.std hT.weil
    (fun Φ hΦ => (hc Φ hΦ).1) hcont hγ (GlobalTheory.ThetaIntegralLine.polData_le_schA hT.geo.hM hΦ)
  have e : Φ₁ = Ψ := funext fun x => (hd x).unique (hΨ x)
  rw [e]
  exact hI h

end GlobalTheory.ThetaProjectionLie

namespace GlobalTheory.ThetaProjectionLie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

end GlobalTheory.ThetaProjectionLie

end
