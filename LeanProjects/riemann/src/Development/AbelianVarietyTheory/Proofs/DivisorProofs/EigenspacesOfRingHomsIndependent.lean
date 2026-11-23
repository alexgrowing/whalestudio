import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSupIndep_eig : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type)
    [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) →
    iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  intro C _ O _ _ Λ _ h ρ hinj
  let T : Λ → Module.End C (Fin h → C) := fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))
  have hT : ∀ a b, T a * T b = T (a * b) := by
    intro a b
    simp only [T, map_mul, Matrix.map_mul]
    rw [Matrix.toLin'_mul]
    rfl
  have hc : ∀ a b, Commute (T a) (T b) := by
    intro a b
    show T a * T b = T b * T a
    rw [hT, hT, mul_comm]
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ)
  let g : (Λ →+* O) → (Λ → C) := fun σ a => algebraMap O C (σ a)
  have hg : Function.Injective g := by
    intro σ τ hστ
    ext a
    exact hinj (congrFun hστ a)
  refine (hind.comp hg).mono ?_
  intro σ
  exact iInf_mono fun a => Module.End.eigenspace_le_maxGenEigenspace

end GlobalTheory
