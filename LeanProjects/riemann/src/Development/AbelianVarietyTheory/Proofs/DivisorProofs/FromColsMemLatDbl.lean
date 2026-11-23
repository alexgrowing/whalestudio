import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVacEigen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) : AddSubgroup (Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) where
  carrier := {z | z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v}
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem (latAtV X W v), zero_mem (latAtV X W v)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, neg_mem ha.2⟩

theorem mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) (z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)) :
    z ∈ latDbl X W v ↔ z.toCols₁ ∈ latAtV X W v ∧ z.toCols₂ ∈ latAtV X W v := Iff.rfl

theorem fromCols_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {γ₁ γ₂ : Matrix (Fin n) (Fin d) (AE F E)}
    (h₁ : γ₁ ∈ latAtV X W v) (h₂ : γ₂ ∈ latAtV X W v) : Matrix.fromCols γ₁ γ₂ ∈ latDbl X W v := by
  rw [mem_latDbl, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
  exact ⟨h₁, h₂⟩

theorem at_of_mem_latDbl {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl F) {z : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E)}
    (hz : z ∈ latDbl X W v) : At (evFin F v) z := by
  intro u hu
  have h1 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.1 u hu
  have h2 := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 _ hz.2 u hu
  ext i (j | j)
  · simpa using congrFun (congrFun h1 i) j
  · simpa using congrFun (congrFun h2 i) j

end GlobalTheory.DblVacEigen
