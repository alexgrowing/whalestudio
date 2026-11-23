import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_theta_descent_identity : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ (c : GL (Fin (a + (b + 2))) (Fv F v)) (c₁ : GL (Fin (a + b)) (Fv F v)),
        GlobalTheory.KSplit.IsSmU (chrW X.α t) ∧ GlobalTheory.KSplit.IsSmU (chrW X.β t) ∧
        ∀ (eB : Rf.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a (b + 2) (chrW X.α t) (chrW X.β t))
          (eS : Rf₁.Pi v ≃ₗ[ℂ] GlobalTheory.KSplit.indSp a b (chrW X.α t) (chrW X.β t)),
          (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
            ∀ φ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, h)) φ φ₁ →
            ∀ g : GL (Fin (a + (b + 2))) (Fv F v), (eB (Rf.p v φ₁) : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) g =
              (eB (Rf.p v φ) : GL (Fin (a + (b + 2))) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c h)) →
          (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + b) → Fv F v),
            ∀ φ₁ ∈ SB (Fin a × Fin (a + b) → Fv F v), Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
            ∀ g : GL (Fin (a + b)) (Fv F v), (eS (Rf₁.p v φ₁) : GL (Fin (a + b)) (Fv F v) → ℂ) g =
              (eS (Rf₁.p v φ) : GL (Fin (a + b)) (Fv F v) → ℂ) (g * GlobalTheory.KSplit.locMat t c₁ h)) →
          ∀ φ : Rf.Pi v →ₗ[ℂ] Rf₁.Pi v,
            (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ ψ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
              ∀ ψ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, u)) ψ ψ₁ →
                φ (Rf.p v ψ₁) = φ (Rf.p v ψ)) →
            (∀ (s : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' s h₁ m → m ∈ UAt σ G.W (evFin F v) →
              h₁ ∈ UAt σ G₁.W (evFin F v) → ∀ ψ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v),
              ∀ ψ₁ ∈ SB (Fin a × Fin (a + (b + 2)) → Fv F v), Acts (evFin F v) (om (1, m)) ψ ψ₁ →
              ∀ θ ∈ SB (Fin a × Fin (a + b) → Fv F v), ∀ θ₁ ∈ SB (Fin a × Fin (a + b) → Fv F v),
              Acts (evFin F v) (om₁ (1, h₁)) θ θ₁ → φ (Rf.p v ψ) = Rf₁.p v θ →
                φ (Rf.p v ψ₁) = ((X.β s : ℂ) * (((absE F E s : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)) • Rf₁.p v θ₁) →
            GlobalTheory.JacLine.IsJacMap a b (chrW X.α t) (chrW X.β t)
              (fun x => (chrW X.β t x : ℂ) * GlobalTheory.SplitFlip.apow x ((a : ℂ) / 2))
              (fun y => (chrW X.β t y : ℂ) * GlobalTheory.SplitFlip.apow y (-(a : ℂ) / 2))
              (eS.toLinearMap ∘ₗ φ ∘ₗ eB.symm.toLinearMap) := by
  first | exact @GlobalTheory.JacGeom.isJacMap_of_equivariant | exact GlobalTheory.JacGeom.isJacMap_of_equivariant | (intros; apply GlobalTheory.JacGeom.isJacMap_of_equivariant <;> assumption)
