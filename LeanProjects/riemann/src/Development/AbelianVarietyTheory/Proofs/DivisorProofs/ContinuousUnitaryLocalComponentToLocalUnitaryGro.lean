import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUnStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem cLoc_fin_continuous {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E) :
    Continuous (fun x : finU E n => cLoc w (x : UA E n)) := by
  have hf : Continuous ((pLoc E w).comp (pFin E)) := by
    show Continuous (fun x => pLoc E w (pFin E x))
    exact (RestrictedProduct.continuous_eval w).comp continuous_snd
  have hm : Continuous (((pLoc E w).comp (pFin E)).mapMatrix : Matrix (Fin n) (Fin n) (Ad E) →+* _) :=
    continuous_id.matrix_map hf
  exact (Continuous.units_map _ hm).comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_toSub {X G : Type} [TopologicalSpace X] [Group G] [TopologicalSpace G] (H : Subgroup G) {f : X → G}
    (hf : Continuous f) (hH : ∀ x, f x ∈ H) : Continuous (fun x => toSub H (f x)) := by
  have : (fun x => toSub H (f x)) = fun x => (⟨f x, hH x⟩ : H) := by
    funext x; simp [toSub, hH x]
  rw [this]
  exact hf.subtype_mk _

theorem toSub_cLoc_continuous_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (hmem : ∀ x : finU E n, cLoc w (x : UA E n) ∈ UL n w) :
    Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) :=
  continuous_toSub _ (cLoc_fin_continuous w) hmem

theorem toSub_cLoc_fin_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ w : Pl E, Continuous (fun x : finU E n => toSub (UL n w) (cLoc w (x : UA E n))) := by
  intro E _ _ _ hE n w
  exact toSub_cLoc_continuous_of_mem w (GlobalTheory.T.finiteAdelicUnitaryPoint_localComponent_mem_localUnitary E hE n w)

end GlobalTheory.BCT
