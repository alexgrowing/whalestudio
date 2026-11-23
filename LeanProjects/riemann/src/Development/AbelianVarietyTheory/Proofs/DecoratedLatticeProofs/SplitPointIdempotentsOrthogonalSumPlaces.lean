import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

theorem orth_and_eq_eSum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (J : List ι) (P : Pl D → Prop), Places p J P → ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset → (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) → (∀ i j, i ≠ j → (p i).e * (p j).e = 0) ∧ e = GlobalTheory.FinPl.PutIn.eSum p J := by
  intro D k _ _ _ _ ι p J P hP Pset e he hq
  classical
  obtain ⟨q, hq⟩ := hq
  refine ⟨fun i j hij => ?_, ?_⟩
  · refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (p i).split (p j).split).resolve_left fun h => hij ?_
    exact q.injective (Subtype.ext (GlobalTheory.PlaceVec.isIdemAt_inj (hq i) (h ▸ hq j)))
  · obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    haveI : Fintype ι := Fintype.ofList J hP.all
    have h1 : ∀ i, es (q i).1 = (p i).e := fun i =>
      GlobalTheory.SplitHeckeAdj.idem_unique D.sp.X' (hq i) (hes _ (q i).2)
    have h2 : J.toFinset = Finset.univ := Finset.eq_univ_of_forall fun i => List.mem_toFinset.2 (hP.all i)
    rw [eSum, ← List.sum_toFinset _ hP.nodup, h2, ← Finset.sum_coe_sort Pset es, ← Equiv.sum_comp q]
    exact Finset.sum_congr rfl fun i _ => h1 i

end GlobalTheory.FinPl.PutIn

end
