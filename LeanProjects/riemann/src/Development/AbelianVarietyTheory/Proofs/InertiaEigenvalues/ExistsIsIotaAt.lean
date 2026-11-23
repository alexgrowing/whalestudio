import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousComplEquivSymm
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DivPtLocal

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def locDiv (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, (N : w.adicCompletion E) * X i j ∈ w.adicCompletionIntegers E}
  add_mem' := by
    intro X Y hX hY i j
    simpa [mul_add] using add_mem (hX i j) (hY i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro X hX i j
    simpa [mul_neg] using neg_mem (hX i j)

def locInt (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, X i j ∈ w.adicCompletionIntegers E}
  add_mem' := by
    intro X Y hX hY i j
    simpa using add_mem (hX i j) (hY i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro X hX i j
    simpa using neg_mem (hX i j)

theorem mem_locDiv {N m n : ℕ} {X : Matrix (Fin m) (Fin n) (w.adicCompletion E)} :
    X ∈ locDiv w N m n ↔ ∀ i j, (N : w.adicCompletion E) * X i j ∈ w.adicCompletionIntegers E := Iff.rfl

theorem mem_locInt {m n : ℕ} {X : Matrix (Fin m) (Fin n) (w.adicCompletion E)} :
    X ∈ locInt w m n ↔ ∀ i j, X i j ∈ w.adicCompletionIntegers E := Iff.rfl

abbrev LocQ (N m n : ℕ) : Type :=
  ↥(locDiv w N m n) ⧸ (locInt w m n).addSubgroupOf (locDiv w N m n)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta in

def IsIotaAt {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (ι : w.adicCompletion D.host.E →+ AE D) : Prop :=
  Continuous ι ∧ (∀ x, GlobalTheory.Core.Rk.SWQ.cw h (ι x) = x) ∧ (∀ x, GlobalTheory.Core.Rk.SWQ.cw h (cA D (ι x)) = 0) ∧
    (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) * ι x = ι x) ∧
    (∀ a x, a * ι x = ι (GlobalTheory.Core.Rk.SWQ.cw h a * x)) ∧
    (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) * a =
      ι (GlobalTheory.Core.Rk.SWQ.cw h a) + cA D (ι (GlobalTheory.Core.Rk.SWQ.cw h (cA D a)))) ∧
    IsSplitIdem D (ι 1) ∧ Continuous (GlobalTheory.Core.Rk.SWQ.cw h)

theorem exists_isIotaAt {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q) :
    ∃ ι : w.adicCompletion D.host.E →+ Formalism.L2.Theta.AE D, IsIotaAt h ι :=
  GlobalTheory.Core.Rk.SplitIota.exists_iota D q w h hs

end GlobalTheory.DivPtLocal

end
