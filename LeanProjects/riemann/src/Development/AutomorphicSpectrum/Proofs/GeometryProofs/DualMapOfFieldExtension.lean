import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.DualExt

theorem dual_ext : ∀ (Ω Ω' : Type) [Field Ω] [Field Ω'] (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V'), IsExtOver i j → Submodule.span Ω' (Set.range j) = ⊤ → ∃ jd : Module.Dual Ω V →+ Module.Dual Ω' V', ∀ w e, jd w (j e) = i (w e) := by
  intro Ω Ω' _ _ i V V' _ _ _ _ j hext hspan
  let b := Module.Basis.ofVectorSpace Ω V
  have hj : ∀ e : V, j e = (b.repr e).sum fun k a => i a • j (b k) := by
    intro e
    conv_lhs => rw [← b.linearCombination_repr e]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => hext.1 _ _
  have hli : LinearIndependent Ω' fun k => j (b k) := by
    rw [linearIndependent_iff_finset_linearIndependent]
    intro s
    have h := hext.2 s.card (fun m => b (s.equivFin.symm m))
      (b.linearIndependent.comp (fun m => (s.equivFin.symm m : _))
        (Subtype.val_injective.comp s.equivFin.symm.injective))
    have h2 := h.comp s.equivFin s.equivFin.injective
    convert h2 using 1
    funext x
    simp
  have hsp : ⊤ ≤ Submodule.span Ω' (Set.range fun k => j (b k)) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨e, rfl⟩
    rw [hj e, Finsupp.sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let b' := Module.Basis.mk hli hsp
  refine ⟨AddMonoidHom.mk' (fun w => b'.constr Ω' fun k => i (w (b k))) fun w₁ w₂ => ?_, fun w e => ?_⟩
  · rw [← map_add]
    congr 1
    funext k
    simp
  · show b'.constr Ω' (fun k => i (w (b k))) (j e) = i (w e)
    rw [hj e, Finsupp.sum, map_sum]
    conv_rhs => rw [← b.linearCombination_repr e, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, show j (b k) = b' k from (Module.Basis.mk_apply hli hsp k).symm, Module.Basis.constr_basis,
      map_smul, smul_eq_mul, smul_eq_mul, map_mul]

end GlobalTheory.CompanionTheory.Ar.DualExt
