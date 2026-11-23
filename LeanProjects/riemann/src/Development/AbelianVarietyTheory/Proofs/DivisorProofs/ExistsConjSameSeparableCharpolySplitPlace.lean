import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitConj

theorem exists_conj_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n,
    ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P →
      ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  intro E _ _ _ n P hP w hw γ γ' h h'
  have hs : (atPl w P).Separable := hP.2.2.1.map
  obtain ⟨g, hg⟩ := GlobalTheory.BCT.ClsFin.conj_of_charpoly γ.1 γ'.1 (by rw [h]; exact hs) (h.trans h'.symm)
  have hmem : g ∈ UL n w := by
    rw [UL, if_pos hw]
    exact Subgroup.mem_top g
  exact ⟨⟨g, hmem⟩, Subtype.ext hg⟩

end GlobalTheory.BCT.SplitConj
