import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.IsotInLeOfIntw
import Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.RepCls

theorem reps_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y Φ rep hR
  let f : Φ → principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0) :=
    fun π => Quotient.mk _ ⟨rep π, hR.mem π⟩
  have hinj : Function.Injective f := by
    intro π π' h
    exact hR.inj π π' (Quotient.exact h)
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨π, hπ⟩ := hR.all (Formalism.L2.Col.finTypRep _ c) (Formalism.L2.Col.finTypRep_mem _ c)
    refine ⟨π, ?_⟩
    rw [← Quotient.out_eq c]
    exact Quotient.sound hπ
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun π => ?_⟩
  have hiso : (principalLevelFrame.rowRepR R.θ (Equiv.ofBijective f ⟨hinj, hsurj⟩ π)).Iso (rep π) :=
    Formalism.L2.Col.finTypRep_mk_iso ⟨rep π, hR.mem π⟩
  refine ⟨hiso, fun b => ?_, fun i => ?_, ?_⟩
  · unfold Hd.prtE principalLevelFrame.isotE
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ (principalLevelFrame.conjT_iso hiso)]
  · unfold Hd.prtW
    rw [principalLevelFrame.isotL_iso _ _ _ _ _ _ hiso]
  · obtain ⟨b, hb⟩ := hR.mem π
    refine ⟨b, ?_, ?_⟩
    · intro h
      apply hb
      unfold Hd.prtE at h
      rw [eq_bot_iff] at h ⊢
      intro x hx
      have h0 := h (Submodule.mem_map_of_mem hx)
      rw [Submodule.mem_bot] at h0 ⊢
      exact (LinearEquiv.map_eq_zero_iff _).1 h0
    · exact Submodule.map_mono inf_le_left

end GlobalTheory.Mem.R3.Rw.RepCls
