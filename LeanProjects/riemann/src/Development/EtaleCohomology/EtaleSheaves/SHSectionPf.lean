import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SHSectionPf

def SHAlgSec : Prop := ∀ (A R : CommRingCat.{0}) (f : A ⟶ R), SH A → f.hom.Etale →
  (∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal) → ∃ σ : R ⟶ A, f ≫ σ = 𝟙 A

def EtAffNbhd : Prop := ∀ (A : CommRingCat.{0}) [Nontrivial A] {V : Scheme.{0}} (g : V ⟶ Spec A) [Etale g] [Surjective g],
  ∃ (R : CommRingCat.{0}) (f : A ⟶ R) (ι : Spec R ⟶ V), f.hom.Etale ∧ ι ≫ g = Spec.map f ∧
    ∃ Q : Ideal R, Q.IsPrime ∧ (Q.comap f.hom).IsMaximal

theorem SHSection_of (h1 : SHAlgSec) (h2 : EtAffNbhd) : LateralTheory.E.t_E3Cut.SHSection := by
  intro A hA V g _ _
  have : Nontrivial A := by obtain ⟨hH, -⟩ := hA; infer_instance
  obtain ⟨R, f, ι, hf, hι, hQ⟩ := h2 A g
  obtain ⟨σ, hσ⟩ := h1 A R f hA hf hQ
  refine ⟨Spec.map σ ≫ ι, ?_⟩
  rw [Category.assoc, hι, ← Spec.map_comp, hσ, Spec.map_id]

end LateralTheory.E.SHSectionPf
