import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharInducedJacquetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaUnfoldingStatement

noncomputable section

namespace GlobalTheory.IndLineSplitA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) → IndLineFin v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v hv A A' hA hA'
  obtain ⟨π, σ₁, α₀, β₀, ξ₁, ξ₂, e, Θ, hα, hβ, hαu, hβu, hπ, hπe, hσ, hΘ, hInd⟩ :=
    GlobalTheory.T.config_a_theta_unfolding hKP F E σ B b a' G G₁ H H' hC X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ v hv
  have hlt : a' < b + 2 := hM.triple.geo.lt
  rcases GlobalTheory.T.unitary_char_induced_jacquet hKP (Fv F v) (b + 2) a' (b + a') (by omega) hlt α₀ β₀ hα hβ hαu hβu (Rf.Pi v) (Rf₁.Pi v) π σ₁
      hπ hπe hσ e ξ₁ ξ₂ _ _ (hInd A hA) (hInd A' hA') with h0 | ⟨c, hc⟩
  · left
    intro x h hh
    obtain ⟨g, rfl⟩ := hΘ h hh
    have := congrFun (LinearMap.congr_fun h0 x) g
    simpa using this
  · right
    refine ⟨c, fun x h hh => ?_⟩
    obtain ⟨g, rfl⟩ := hΘ h hh
    have := congrFun (LinearMap.congr_fun hc x) g
    simpa using this

end GlobalTheory.IndLineSplitA
