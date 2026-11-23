import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.SchrodingerFunctionalEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open scoped Classical

theorem UpperTheory.model_embedding_good_compat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
        (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
        (I : Set (Matrix (Fin n) (Fin d) (AE F E))), IsStd B.ψ → M.IsGood B.ψ → M₁.IsGood B.ψ →
        ∀ e, IsEv B M M₁ ι ι' I e → ∀ ei ev, IsLocPart M M₁ e ei ev →
        ∀ l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ, l ≠ 0 → ∃ f : SInf F (Fin n × Fin d), l (ei f) ≠ 0 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I hψ hM hM₁ e he ei ev hL l hl
  by_contra hcon
  push Not at hcon
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    obtain ⟨f, hf⟩ := DFunLike.ne_iff.mp hL.1
    exact ⟨f, by simpa using hf⟩
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hSB₁ : ∀ v, M₁.vac v ∈ SB _ := fun v => (hM₁.vac v).1
  have hei : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac := fun f => by
    rw [hL.2.2 f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hL.2.1 v).1)
  have hp := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have hp₁ := GlobalTheory.TensUniq.pure_mem_schA (ei f) _ hSB₁ hM₁.std
  have key : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      ei (locOpInf (M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ))) f) =
        locOpInf (M₁.co.rho B.ψ (partInf F z)) (ei f) := fun z => by
    have h1 : M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ)) (pure f M.vac) =
        pure (locOpInf (M.co.rho B.ψ (partInf F (incM F ι * z * (incM F ι')ᵀ))) f) M.vac :=
      (locOpInf_rho M.co hψ _ f).1 _ ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, hp⟩
    have h2 : M₁.co.rho B.ψ (partInf F z) (pure (ei f) M₁.vac) =
        pure (locOpInf (M₁.co.rho B.ψ (partInf F z)) (ei f)) M₁.vac :=
      (locOpInf_rho M₁.co hψ _ (ei f)).1 _ ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, hp₁⟩
    have h3 : partInf F (incM F ι * z * (incM F ι')ᵀ) = incM F ι * partInf F z * (incM F ι')ᵀ := by
      rw [partInf, partInf, Matrix.mul_smul, Matrix.smul_mul]
    refine GlobalTheory.EvZeroInf.eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std _ _ ?_
    rw [← hei, ← h1, ← h2, ← hei, h3]
    exact he.Heisenberg₂ _ _ hp
  refine hl (UpperTheory.schrodinger_functional_eq_zero _ (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n₁ × Fin d₁)) (ei f) hf l fun w g hg => ?_)
  obtain ⟨z, rfl⟩ : ∃ z, GlobalTheory.ArchUniq.Coord.coordI M₁ z = w := ⟨_, GlobalTheory.ArchUniq.Coord.coordI_lift M₁ w⟩
  have hgz : g = locOpInf (M₁.co.rho B.ψ (partInf F z)) (ei f) :=
    DFunLike.coe_injective (hg.trans (locOpInf_rho M₁.co hψ z (ei f)).2.symm)
  rw [hgz, ← key]
  exact hcon _
