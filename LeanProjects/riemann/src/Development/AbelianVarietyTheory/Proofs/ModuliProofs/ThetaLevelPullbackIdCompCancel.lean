import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

theorem lbIso_pull_comp {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {φ : X' ⟶ X}
    (H : LBIso L' (L.pull φ)) (φ' : X'' ⟶ X') : LBIso (L'.pull φ') (L.pull (φ' ≫ φ)) :=
  LBIso.chartPull (chartPullPull L' φ' φ' rfl) (chartPullSame L _ _ _ φ' fun _ => rfl) H

theorem TMap.refl (t : TObj g k J b s) : TMap t t (𝟙 S) := by
  refine ⟨𝟙 _, ?_, ?_, fun i => by simp, fun j => by simp⟩
  · have : IsMonHom (Iso.refl t.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
    exact isGrpPullback_of_iso (Iso.refl t.A)
  · exact LBIso.chartPull (chartPullId t.L) (chartPullPull t.L _ _ rfl) (GlobalTheory.PolBaseChange.lbIso_refl t.isLB)

theorem TMap.comp {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨φ', k₁, k₂, k₃, k₄⟩ := h'
  refine ⟨φ' ≫ φ, k₁.comp h₁, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) k₂ (lbIso_pull_comp h₂ φ')
  · rw [← Category.assoc, k₃, Category.assoc, h₃, Category.assoc]
  · rw [← Category.assoc, k₄, Category.assoc, h₄, Category.assoc]

theorem TMap.cancel {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h₁, h₂, h₃, h₄⟩ := h
  obtain ⟨ψ, k₁, k₂, k₃, k₄⟩ := n
  have hp := h₁.1
  obtain ⟨F, hF, hw⟩ : ∃ F : t''.A.left ⟶ t'.A.left, F ≫ φ = ψ ∧ F ≫ t'.A.hom = t''.A.hom ≫ f' :=
    ⟨hp.lift ψ (t''.A.hom ≫ f') (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  subst hF
  refine ⟨F, h₁.cancel k₁ hw, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (pull_isLB t.isLB _) (pull_isLB t'.isLB _) k₂ (lbIso_pull_comp h₂ F).symm
  · apply hp.hom_ext
    · rw [Category.assoc, k₃, Category.assoc, Category.assoc, h₃]
    · have a₁ : (t''.pt i).left ≫ t''.A.hom = 𝟙 S'' := Over.w (t''.pt i)
      have a₂ : (t'.pt i).left ≫ t'.A.hom = 𝟙 S' := Over.w (t'.pt i)
      rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tmap_id_comp_cancel : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (s'' : S'' ⟶ Sp o) (t : TObj g k J b s) (t' : TObj g k J b s') (t'' : TObj g k J b s''), TMap t t (𝟙 S) ∧ ∀ (f : S' ⟶ S) (f' : S'' ⟶ S'), TMap t' t f → (TMap t'' t' f' ↔ TMap t'' t (f' ≫ f)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ t _ _ => ⟨TMap.refl t, fun _ _ h => ⟨fun h' => h'.comp h, fun n => h.cancel n⟩⟩

end GlobalTheory.ZM
end
