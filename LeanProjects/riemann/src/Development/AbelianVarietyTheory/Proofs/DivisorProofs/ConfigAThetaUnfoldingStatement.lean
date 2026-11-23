import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_theta_unfolding : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
      ∃ (π : Representation ℂ (GL (Fin (b + 2 + a')) (Fv F v)) (Rf.Pi v))
        (σ₁ : Representation ℂ (GL (Fin (b + a')) (Fv F v)) (Rf₁.Pi v)) (α₀ β₀ ξ₁ ξ₂ : (Fv F v)ˣ →* ℂˣ)
        (e : (Σ i : Fin 3, Fin (blk3 (b + a') i)) ≃ Fin (b + 2 + a'))
        (Θ : GL (Fin (b + 2 + a')) (Fv F v) → UA σ G.W.J),
        IsSmoothChar α₀ ∧ IsSmoothChar β₀ ∧ (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) ∧
        IsSmooth π ∧ Nonempty (π.Equiv (prod₂ (detRep (Fin (b + 2)) α₀) (detRep (Fin a') β₀))) ∧
        σ₁.IsIrreducible ∧ (∀ h ∈ UAt σ G.W (evFin F v), ∃ g, Θ g = h) ∧
        ∀ A : Rf.Pi v →ₗ[ℂ] (UA σ G.W.J → Rf₁.Pi v),
          IsIndMap v om om₁ (Rf.p v) (Rf₁.p v) H' X.α ((a' : ℝ) / 2) A →
          IsGLIndMap e π σ₁ ξ₁ ξ₂ ((LinearMap.funLeft ℂ (Rf₁.Pi v) Θ).comp A) := by
  first | exact @GlobalTheory.IndLineGLBridge.isGLIndMap_of_isIndMap | exact GlobalTheory.IndLineGLBridge.isGLIndMap_of_isIndMap | (intros; apply GlobalTheory.IndLineGLBridge.isGLIndMap_of_isIndMap <;> assumption)
