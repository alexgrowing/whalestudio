import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hform_mulVec {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ x y : Fin m → A, hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [key, key, hs]
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  congr 1
  change cT σ g *ᵥ (J *ᵥ (g *ᵥ y)) = J *ᵥ y
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

theorem isClosed_HR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) _) := by
    refine ((Continuous.matrix_transpose (Continuous.matrix_map hv hs)).matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

end

theorem topH_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3, h4, hs, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl := isClosed_HR R σ hs J
  haveI g1 : IsTopologicalGroup (HR R σ J) := inferInstance
  haveI g2 : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI g3 : SecondCountableTopology (HR R σ J) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI g4 : T2Space (HR R σ J) := inferInstance
  refine ⟨g1, g2, g3, g4, ⟨rfl⟩, fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) =>
        ((HA.mat R σ J p.1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    exact continuous_pi fun a => hm.matrix_mulVec ((continuous_apply a).comp continuous_snd)
  · intro X
    funext a
    exact Matrix.one_mulVec (X a)
  · intro g h X
    funext a
    change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (HA.mat R σ J h : Matrix (Fin M) (Fin M) _)) *ᵥ X a = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  · intro h X
    funext a b
    exact hform_mulVec (sigR R σ) (JR R J) _ h.2 (X a) (X b)

end GlobalTheory.CompanionTheory.SW.TopH
