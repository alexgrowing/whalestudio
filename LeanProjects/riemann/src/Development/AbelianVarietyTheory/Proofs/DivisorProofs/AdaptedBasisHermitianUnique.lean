import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLatticeImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeImageOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantVectorLocalSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumVectorIffLatticeEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueIndependentOfThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeElementDecompositionAlongPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionAdaptedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionDarbouxStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacResX

theorem vac_restrict_eq_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∀ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
        Function.Injective j →
        (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) →
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0) →
        ∀ (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ), (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v φ →
          ∃ c : ℂ, c ≠ 0 ∧ (fun y => φ (Function.extend j y 0)) = c • M₁.vac v := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ hX₁ hH hM₁ j co hj ha hb hc v φ hφ
  obtain ⟨-, hφ0, θ, hθ, hφe⟩ := (GlobalTheory.T.vacuum_vector_iff_lattice_eigen _ B.ψ v φ).1 hφ
  have hf0 : (fun y => φ (Function.extend j y 0)) ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hφ0
    have := GlobalTheory.T.lattice_coordinate_injection_adapted F E σ B n d n₁ X W X₁ H j₀ j₁ M₁ hH j co hj ha hb hc v (GlobalTheory.T.lattice_element_decomposition_along_plane F E σ B n d n₁ X W X₁ H j₀ j₁ hH v)
      (fun w hw => GlobalTheory.T.lattice_invariant_vector_local_support F E σ B n d X W r s r' s' hB hX hW co v w hw) φ θ hφe x hx
    exact fun h => this (congrFun h (x ∘ j))
  have hfe := GlobalTheory.T.lattice_coordinate_injection_darboux F E σ B n d n₁ X W X₁ H j₀ j₁ M₁ hH j co hj ha v φ θ hφe
  obtain ⟨-, hv0, θ₁, hθ₁, hve⟩ := (GlobalTheory.T.vacuum_vector_iff_lattice_eigen M₁ B.ψ v (M₁.vac v)).1 (hM₁.vac v)
  obtain ⟨oc, ooc⟩ := GlobalTheory.T.local_lattice_image_open σ B X₁ W r₁ s₁ r' s' hX₁ hW M₁.co v
  obtain ⟨c, hc'⟩ := GlobalTheory.T.compact_open_lattice_image v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) (GlobalTheory.LatVac.locCo M₁.co v) (latAtV X₁ W v) oc ooc
    (fun w hw => GlobalTheory.T.lattice_invariant_vector_local_support F E σ B n₁ d X₁ W r₁ s₁ r' s' hB hX₁ hW M₁.co v w hw)
    (fun γ => B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ₁ : E)) (incM F X₁.J) (incM F W.J) γ γ))
    (M₁.vac v) (fun y => φ (Function.extend j y 0)) hv0 hve
    (fun γ hγ => by rw [hfe γ hγ, GlobalTheory.T.vacuum_eigenvalue_independent_of_theta F E σ B n₁ d X₁ W r₁ s₁ r' s' hB hX₁ hW v θ θ₁ hθ hθ₁ γ hγ])
  refine ⟨c, ?_, hc'⟩
  rintro rfl
  exact hf0 (by rw [hc', zero_smul])

end GlobalTheory.VacResX
