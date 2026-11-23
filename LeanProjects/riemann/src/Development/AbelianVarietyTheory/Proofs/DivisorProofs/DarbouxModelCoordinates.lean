import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelConvRat

open GlobalTheory.SiegelConv

theorem diagonalEmbedding_add {F : Type} [Field F] [NumberField F] {κ : Type} (p q : (κ → F) × (κ → F)) :
    ratP (p + q) = ratP p + ratP q := by
  ext i <;> simp [ratP]

theorem diagonalEmbedding_smul {F : Type} [Field F] [NumberField F] {κ : Type} (c : F) (p : (κ → F) × (κ → F)) :
    ratP (c • p) = algebraMap F (AF F) c • ratP p := by
  ext i <;> simp [ratP, Algebra.smul_def]

theorem diagonalEmbedding_injective {F : Type} [Field F] [NumberField F] {κ : Type} :
    Function.Injective (ratP (F := F) (κ := κ)) := by
  intro p q h
  have hi := NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F)
  simp only [ratP, Prod.mk.injEq] at h
  ext i
  · exact hi (congrFun h.1 i)
  · exact hi (congrFun h.2 i)

theorem incM_add {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : Type}
    (u v : Matrix a b E) : incM F (u + v) = incM F u + incM F v := by
  ext i j; simp [incM]

theorem incM_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : Type}
    (c : F) (u : Matrix a b E) : incM F (c • u) = algebraMap F (AF F) c • incM F u := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]
  exact (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E).map_smul_of_tower c (u i j)

theorem incM_transpose {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : Type}
    (u : Matrix a b E) : (incM F u)ᵀ = incM F uᵀ := by
  ext i j; rfl

theorem ratCoord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d)),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
      IsDblCoord (cA σ) (-1) (incM F W.J) (incM F X.J) d' dd →
    ∃ D : Matrix (Fin d) (Fin n ⊕ Fin n) E →ₗ[F]
        ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → F),
      Function.Injective D ∧ ∀ u, dd.e (incM F u) = GlobalTheory.SiegelConv.ratP (D u) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d' hd' dd hdd
  have hd'rat : ∀ a : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F a) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro a
    obtain ⟨y, z, h⟩ := hP.good.rat aᵀ
    refine ⟨y, z, ?_⟩
    rw [← h, ← hd', incM_transpose, Matrix.transpose_transpose]
  have key : ∀ u : Matrix (Fin d) (Fin n ⊕ Fin n) E, ∃ p, dd.e (incM F u) = ratP p := by
    intro u
    obtain ⟨y₁, z₁, h₁⟩ := hd'rat (u.submatrix id Sum.inl)
    obtain ⟨y₂, z₂, h₂⟩ := hd'rat (u.submatrix id Sum.inr)
    have hu : incM F u = Matrix.fromCols (incM F (u.submatrix id Sum.inl)) (incM F (u.submatrix id Sum.inr)) := by
      ext i (j | j) <;> rfl
    refine ⟨(Sum.elim y₁ y₂, Sum.elim z₁ (-z₂)), ?_⟩
    rw [hu, hdd _ _, h₁, h₂]
    ext (j | j) <;> simp [ratP]
  choose D0 hD0 using key
  have hadd : ∀ u v, D0 (u + v) = D0 u + D0 v := fun u v => diagonalEmbedding_injective (by
    rw [diagonalEmbedding_add, ← hD0, ← hD0, ← hD0, incM_add, map_add])
  have hsmul : ∀ (c : F) u, D0 (c • u) = (RingHom.id F) c • D0 u := fun c u => diagonalEmbedding_injective (by
    rw [RingHom.id_apply, diagonalEmbedding_smul, ← hD0, ← hD0, incM_smul, map_smul])
  refine ⟨{ toFun := D0, map_add' := hadd, map_smul' := hsmul }, ?_, fun u => hD0 u⟩
  intro u v h
  have h0 : D0 u = D0 v := h
  have h' : dd.e (incM F u) = dd.e (incM F v) := by rw [hD0, hD0, h0]
  have h'' := dd.e.injective h'
  have hi : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F))
  ext i j
  exact hi (congrFun (congrFun h'' i) j)

end GlobalTheory.SiegelConvRat

end
