import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Tr

theorem rowPsi_eq_of_psi {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (P Q : principalLevelFrame.RowPsi V n) (h : P.ψ = Q.ψ) : P = Q := by
  cases P; cases Q; cases h; rfl

theorem reps_parts_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → (∀ (Φ : Type) (rep : Φ → _), Reps y F rep → @Reps b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by exact rep))) ∧ (∀ bb π, HEq (@Hd.prtE b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb ((by exact π))) (y.prtE F bb π)) ∧ ∀ i π, HEq (@Hd.prtW b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) ((by exact i)) ((by exact π))) (y.prtW F i π) := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hs
  letI := alg b iK
  have hY0 : (rowPsi a y'.PY).ψ = y.PY.ψ := (by with_unfolding_all exact ((eq_of_heq hs.PY) :))
  have hY : rowPsi a y'.PY = y.PY := rowPsi_eq_of_psi _ _ hY0
  have hW0 : (fun i => (rowPsi a (y'.PW i)).ψ) = (fun i => (y.PW i).ψ) := (by with_unfolding_all exact ((eq_of_heq hs.PW) :))
  have hW : ∀ i, rowPsi a (y'.PW i) = y.PW i := fun i => rowPsi_eq_of_psi _ _ (congrFun hW0 i)
  have hocc : HEq (y'.occ (face b F)) (y.occ F) := by
    unfold Hd.occ principalLevelFrame.OccRows principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.occ F)) :))
  have e : y'.occ (face b F) = y.occ F := (by with_unfolding_all exact ((eq_of_heq hocc) :))
  refine ⟨?_, ?_, ?_⟩
  · intro Φ rep h
    exact ⟨h.fin, fun π => by rw [e]; exact h.mem π, fun π π' hi => h.inj π π' hi, fun ρ hρ => h.all ρ (by rw [e] at hρ; exact hρ)⟩
  · intro bb π
    unfold Hd.prtE principalLevelFrame.isotE
    rw [isotL_eq a b]
    delta isotLB
    rw [hY]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtE F bb π)) :))
  · intro i π
    unfold Hd.prtW
    rw [isotL_eq a b]
    delta isotLB
    rw [hW i]
    exact (by with_unfolding_all exact ((HEq.refl (y.prtW F i π)) :))

end GlobalTheory.Mem.R3.Tr

end
