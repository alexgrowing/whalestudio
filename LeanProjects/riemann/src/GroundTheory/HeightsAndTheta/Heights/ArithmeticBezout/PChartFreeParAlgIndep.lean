import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartPointSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFreeParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

noncomputable section

theorem ChartFreeParAlgIndep.proof (h : ChartParAlgebraic.Statement) : ChartFreeParAlgIndep.Statement := by
  intro F _ n e K L _ _ _ _ _ _ u t η hu hK hL hrel hchart j₀ hj₀ htr
  have halg := h F n e K L u t η hK hL hrel hchart j₀ hj₀
  set A₀ := Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹) with hA₀
  set w : Fin e × {j : Fin n // j ≠ j₀} → L := fun p => algebraMap K L (u (p.1, p.2.1)) with hw

  have hinj : Function.Injective (Sum.elim (fun i : Fin e => ((i, j₀) : Fin e × Fin n))
      (fun p : Fin e × {j : Fin n // j ≠ j₀} => ((p.1, p.2.1) : Fin e × Fin n))) := by
    rintro (i | ⟨i, j, hj⟩) (i' | ⟨i', j', hj'⟩) hij <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
        reduceCtorEq, Subtype.mk.injEq] at hij ⊢
    · exact hij.1
    · exact absurd hij.2.symm hj'
    · exact absurd hij.2 hj
    · exact hij
  have hcount : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ #(Fin e × Fin n) := by
    calc (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})
        = #(Fin e ⊕ (Fin e × {j : Fin n // j ≠ j₀})) := by simp
      _ ≤ #(Fin e × Fin n) := Cardinal.mk_le_of_injective hinj
  have huL : AlgebraicIndependent F (fun q => algebraMap K L (u q)) :=
    hu.map' (f := IsScalarTower.toAlgHom F K L) (algebraMap K L).injective
  have hK_le : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ Algebra.trdeg F K :=
    hcount.trans hu.cardinalMk_le_trdeg
  have hL_le : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) ≤ Algebra.trdeg F L :=
    hcount.trans huL.cardinalMk_le_trdeg

  have hind : AlgebraicIndependent A₀ w :=
    Vertical.FreeParAlgIndep.algebraicIndependent_of_trdeg A₀ w htr hL_le
  refine ⟨IntermediateField.algebraicIndependent_adjoin_iff.2 hind, ?_⟩
  have hbasis : IsTranscendenceBasis A₀ w := hind.isTranscendenceBasis_iff_isAlgebraic.2 halg
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective F A₀).2 (algebraMap F A₀).injective
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective A₀ L).2 Subtype.val_injective
  have : FaithfulSMul F K :=
    (faithfulSMul_iff_algebraMap_injective F K).2 (algebraMap F K).injective
  have : FaithfulSMul K L :=
    (faithfulSMul_iff_algebraMap_injective K L).2 (algebraMap K L).injective
  have hA₀L := trdeg_add_eq F A₀ (A := L)
  have hKL := trdeg_add_eq F K (A := L)
  rw [← hbasis.cardinalMk_eq_trdeg] at hA₀L

  have hup : Algebra.trdeg F L ≤ (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) := by
    rw [← hA₀L]
    gcongr
  have hfin : (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) < ℵ₀ :=
    Cardinal.add_lt_aleph0 (Cardinal.natCast_lt_aleph0) (Cardinal.lt_aleph0_of_finite _)
  have h0 : Algebra.trdeg K L + ((e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})) ≤
      0 + ((e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀})) := by
    rw [zero_add, add_comm]
    calc (e : Cardinal) + #(Fin e × {j : Fin n // j ≠ j₀}) + Algebra.trdeg K L
        ≤ Algebra.trdeg F K + Algebra.trdeg K L := by gcongr
      _ = Algebra.trdeg F L := hKL
      _ ≤ _ := hup
  have hz : Algebra.trdeg K L = 0 :=
    nonpos_iff_eq_zero.1 ((Cardinal.add_le_add_iff_of_lt_aleph0 hfin).1 h0)
  exact trdeg_eq_zero_iff.1 hz

end

end GroundTheory.Heights₂.Heights
