import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK.PureNonzero

theorem exists_pure_ne : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → (∃ Φ ∈ PolData B G.M, G.M.I om Φ ≠ 0) →
    ∃ f ∈ G.M.Pol B.ψ B.emb, ∃ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ,
      (∀ v, φ v ∈ SB _) ∧ (∀ᶠ v in cofinite, φ v = G.M.vac v) ∧ ∃ h, G.M.I om (pure f φ) h ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT hex
  obtain ⟨Φ, hΦ, hI⟩ := hex
  have hV := GlobalTheory.T.weil_convergence_of_kernel hKP F E σ B a (a + a') G.V G.W G.M X.β (X.β / X.α) om _ _ _ _ (GlobalTheory.ThK.Inhab.pairV hT)
    (Or.inl (by have := hT.geo.eBig; have := hT.geo.lt; omega))
  have hconv : ∀ Ψ ∈ schA F (Fin a × Fin (a + a')), G.M.Conv om Ψ := fun Ψ hΨ => (hV.1 Ψ hΨ).1
  have hsch : PolData B G.M ≤ schA F _ := GlobalTheory.ConeMeasV.polData_le_schA hT.geo.hM
  have hpres := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).pres
  by_contra hne
  push_neg at hne
  apply hI
  have key : ∀ Ψ ∈ PolData B G.M, ∀ h, G.M.I om Ψ h = 0 := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, φ, h1, h2, rfl⟩ := hx
      exact hne f hf φ h1 h2
    | zero =>
      intro h
      simp [Model.I, theta, thetaSum]
    | add x y hx hy ihx ihy =>
      intro h
      have e : ∀ g, theta om (x + y) g h = theta om x g h + theta om y g h := fun g => by
        simp only [theta, map_add]
        exact GlobalTheory.WeilM.thetaSum_add F (hpres _ _ (hsch hx)) (hpres _ _ (hsch hy))
      simp only [Model.I, e]
      rw [integral_add (hconv x (hsch hx) h) (hconv y (hsch hy) h)]
      exact (congrArg₂ (· + ·) (ihx h) (ihy h)).trans (add_zero 0)
    | smul c x hx ih =>
      intro h
      have e : ∀ g, theta om (c • x) g h = c * theta om x g h := fun g => by
        simp only [theta, map_smul]
        exact GlobalTheory.WeilM.thetaSum_smul F c _
      simp only [Model.I, e]
      rw [integral_const_mul]
      have := ih h
      simp only [Model.I] at this
      rw [this, mul_zero]
  funext h
  exact key Φ hΦ h

end GlobalTheory.ThK.PureNonzero
