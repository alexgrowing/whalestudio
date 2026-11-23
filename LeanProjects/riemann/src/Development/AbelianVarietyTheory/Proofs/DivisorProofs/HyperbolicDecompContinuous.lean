import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviCont

theorem levi_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z : Fin n → AE F E, ∃ (a b : AE F E) (w : Fin n₁ → AE F E), z = a • incV F x + incM F ι *ᵥ w + b • incV F y) →
    ∀ f : (AE F E)ˣ × UA σ J₁ → Matrix (Fin n) (Fin n) (AE F E),
      (∀ p, f p *ᵥ incV F x = (p.1 : AE F E) • incV F x ∧ f p *ᵥ incV F y = cA σ ((p.1⁻¹ : (AE F E)ˣ) : AE F E) • incV F y ∧
        f p * incM F ι = incM F ι * mat p.2) → Continuous f := by
  intro F E _ _ _ _ _ σ n n₁ J J₁ x y ι hspan f hf
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hcA : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hu : Continuous fun p : (AE F E)ˣ × UA σ J₁ => ((p.1 : (AE F E)ˣ) : AE F E) :=
    Units.continuous_val.comp continuous_fst
  have hui : Continuous fun p : (AE F E)ˣ × UA σ J₁ => (((p.1⁻¹ : (AE F E)ˣ)) : AE F E) :=
    Units.continuous_val.comp (continuous_inv.comp continuous_fst)
  have hm : Continuous fun p : (AE F E)ˣ × UA σ J₁ => mat p.2 :=
    (Units.continuous_val.comp continuous_subtype_val).comp continuous_snd
  have hcol : ∀ i, Continuous fun p => f p *ᵥ Pi.single i 1 := by
    intro i
    obtain ⟨a, b, w, hw⟩ := hspan (Pi.single i 1)
    have heq : ∀ p, f p *ᵥ Pi.single i 1 = a • ((p.1 : AE F E) • incV F x) + incM F ι *ᵥ (mat p.2 *ᵥ w)
        + b • (cA σ ((p.1⁻¹ : (AE F E)ˣ) : AE F E) • incV F y) := by
      intro p
      obtain ⟨h1, h2, h3⟩ := hf p
      rw [hw, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2,
        Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec]
    simp_rw [heq]
    have c1 : Continuous fun p : (AE F E)ˣ × UA σ J₁ => a • ((p.1 : AE F E) • incV F x) :=
      (continuous_const (y := a)).smul (hu.smul (continuous_const (y := incV F x)))
    have c2a : Continuous fun p : (AE F E)ˣ × UA σ J₁ => mat p.2 *ᵥ w :=
      Continuous.matrix_mulVec hm (continuous_const : Continuous fun _ : (AE F E)ˣ × UA σ J₁ => w)
    have c2 : Continuous fun p : (AE F E)ˣ × UA σ J₁ => incM F ι *ᵥ (mat p.2 *ᵥ w) :=
      Continuous.matrix_mulVec (continuous_const : Continuous fun _ : (AE F E)ˣ × UA σ J₁ => incM F ι) c2a
    have c3 : Continuous fun p : (AE F E)ˣ × UA σ J₁ => b • (cA σ ((p.1⁻¹ : (AE F E)ˣ) : AE F E) • incV F y) :=
      (continuous_const (y := b)).smul ((hcA.comp hui).smul (continuous_const (y := incV F y)))
    exact (c1.add c2).add c3
  refine continuous_pi fun r => continuous_pi fun i => ?_
  have : ∀ p, f p r i = (f p *ᵥ Pi.single i 1) r := fun p => by simp [Matrix.mulVec_single_one]
  simp_rw [this]
  exact (continuous_apply r).comp (hcol i)

end GlobalTheory.LeviCont
