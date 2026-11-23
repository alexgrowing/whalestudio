import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.DiaFun

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

theorem smul_comm_OE {E : Type} [Field E] [NumberField E] {n : ℕ} (t : E) (m : 𝓞 E) (w : Fin n → E) :
    t • (m • w) = m • (t • w) := by
  exact smul_comm t m w

theorem localization_LshKer_eq_localization_sup {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    (L : Submodule R W) (y : W) (s : R) (hs : s ∉ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ Submodule.span R {s • y}) = Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ Submodule.span R {y}) := by
  have hS : s ∈ P.primeCompl := hs
  ext x
  change (∃ t ∈ P.primeCompl, t • x ∈ L ⊔ Submodule.span R {s • y}) ↔
    ∃ t ∈ P.primeCompl, t • x ∈ L ⊔ Submodule.span R {y}
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, (sup_le_sup_left ?_ L) hx⟩
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self y)
  · rintro ⟨t, ht, hx⟩
    refine ⟨s * t, P.primeCompl.mul_mem hS ht, ?_⟩
    obtain ⟨l, hl, z, hz, he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [mul_smul, ← he, smul_add, smul_comm s c y]
    exact Submodule.add_mem_sup (L.smul_mem s hl)
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

end SameDiaZero

end
