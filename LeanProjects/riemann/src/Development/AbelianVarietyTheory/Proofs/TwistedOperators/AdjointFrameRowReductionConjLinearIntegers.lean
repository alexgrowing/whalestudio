import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLin

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (starRingEnd D.host.E x) := by
  simp [cA, incA, sigR, inclR]
  rfl

theorem toEAf_incA_bar (c : 𝓞 D.host.E) :
    toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) =
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
  simp [toEAf, finPart, incA, inclR, Formalism.L2.DIV.oToS, Formalism.UG.inclE]
  rfl

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

variable {D : D7}

theorem tmul_smul_add (p : AF D.host.F) (c x y : D.host.E) :
    p ⊗ₜ[D.host.F] (c * x + y) = (p ⊗ₜ[D.host.F] x) * incA D c + p ⊗ₜ[D.host.F] y := by
  rw [TensorProduct.tmul_add]
  congr 1
  simp only [incA, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [mul_comm x c]

theorem rowAdj_smul_add (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D)
    (u v : Fin T.rank → D.host.E) (c : D.host.E) :
    GlobalTheory.LiftDat.rowAdj T βT a e (c • u + v) =
      toEAf D (incA D (starRingEnd D.host.E c)) • GlobalTheory.LiftDat.rowAdj T βT a e u + GlobalTheory.LiftDat.rowAdj T βT a e v := by
  have hM : (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (c • u + v) k) * incA D (T.gram k l)) =
      incA D (starRingEnd D.host.E c) • (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] u k) * incA D (T.gram k l)) +
      (Matrix.of fun (_ : Fin 1) (l : Fin T.rank) =>
      ∑ k, cA D (cA D e * (pairA D.host.F 0 1) ⊗ₜ[D.host.F] v k) * incA D (T.gram k l)) := by
    ext i l
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      tmul_smul_add, mul_add, map_add, map_mul, cA_incA, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  unfold GlobalTheory.LiftDat.rowAdj
  rw [hM]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply,
    map_add, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.RowLin

namespace GlobalTheory.RowLin

theorem rowRed_smul_add : ∀ (D : D7) (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (a e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (u v : Fin T.rank → D.host.E), IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e u) → IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) → ∀ c : 𝓞 D.host.E, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) ∧ GlobalTheory.LiftDat.rowRed T βT a e PP ((c : D.host.E) • u + v) = fun j => Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) * GlobalTheory.LiftDat.rowRed T βT a e PP u j + GlobalTheory.LiftDat.rowRed T βT a e PP v j := by
  intro D T βT a e PP u v hu hv c
  have hz := toEAf_incA_bar (D := D) c
  have hrow := rowAdj_smul_add T βT a e u v (c : D.host.E)
  have hzi : toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [hz]; exact Subtype.property _
  have hent : ∀ j, GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j =
      toEAf D (incA D (starRingEnd D.host.E (c : D.host.E))) * GlobalTheory.LiftDat.rowAdj T βT a e u 0 j + GlobalTheory.LiftDat.rowAdj T βT a e v 0 j := by
    intro j; rw [hrow]; simp [Matrix.add_apply, Matrix.smul_apply]
  have hint : IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v)) := by
    intro i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hent]
    exact Subring.add_mem _ (Subring.mul_mem _ hzi (hu 0 j)) (hv 0 j)
  refine ⟨hint, ?_⟩
  funext j
  simp only [GlobalTheory.LiftDat.rowRed, redM, dif_pos (hint 0 j), dif_pos (hu 0 j), dif_pos (hv 0 j)]
  have hsub : (⟨GlobalTheory.LiftDat.rowAdj T βT a e ((c : D.host.E) • u + v) 0 j, hint 0 j⟩ :
      Formalism.L2.Herm.intAf D.host.F D.host.E) =
      Formalism.L2.DIV.oToS D.host.F D.host.E (GlobalTheory.SW.Lev.bar c) * ⟨_, hu 0 j⟩ + ⟨_, hv 0 j⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, ← hz, hent]
  rw [hsub, map_add, map_mul, Formalism.L2.DIV.resS_oToS]

end GlobalTheory.RowLin
