import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_padicAlgCl {l : ℕ} [Fact l.Prime] {z : ℂ_[l]} (hz : IsAlgebraic ℚ_[l] z) :
    ∃ y : PadicAlgCl l, algebraMap (PadicAlgCl l) ℂ_[l] y = z := by

  have hsplit : ((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).Splits :=
    IsAlgClosed.splits _
  have hne : (minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l)) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hz.isIntegral)
  have hroot : (((minpoly ℚ_[l] z).map (algebraMap ℚ_[l] (PadicAlgCl l))).map
      (algebraMap (PadicAlgCl l) ℂ_[l])).IsRoot z := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact (Polynomial.eval_map_algebraMap _ _).trans (minpoly.aeval _ _)
  obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot hne hroot
  exact ⟨y, hy⟩

theorem isAlgebraic_padic_map {l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) {x : ℂ}
    (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ_[l] (ι x) := by
  have h : IsAlgebraic ℚ (ι x) := hx.algHom (ι : ℂ →+* ℂ_[l]).toRatAlgHom
  exact h.tower_top ℚ_[l]

theorem locEmb (d l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) :
    ∃ e : Om d →+* PadicAlgCl l, ∀ x : Om d, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = ι (x : ℂ) := by
  set j : PadicAlgCl l →+* ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] with hj

  let J : PadicAlgCl l ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => j.injective (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  have hmem : ∀ x : Om d, (ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ) x ∈ j.range := by
    intro x
    obtain ⟨y, hy⟩ := exists_padicAlgCl (isAlgebraic_padic_map ι (Om_isAlgebraic d x))
    exact ⟨y, hy⟩
  refine ⟨J.symm.toRingHom.comp (((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem),
    fun x => ?_⟩
  have h := congrArg Subtype.val (J.apply_symm_apply
    ((((ι : ℂ →+* ℂ_[l]).comp (algebraMap (Om d) ℂ)).codRestrict j.range hmem) x))
  exact h

end ReciprocityTheory.ChartRestriction.L1
