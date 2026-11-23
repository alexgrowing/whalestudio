import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.GKLocalProof

theorem invT_eq_invTranspose {A : Type} [CommRing A] (N : ℕ) :
    (invT : GL (Fin N) A →* GL (Fin N) A) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N A :=
  MonoidHom.ext fun _ => Units.ext rfl

theorem gkLocal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k := by
  intro k _ _ _ _ hA N V _ _ π hs hi
  rw [invT_eq_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k N V π (hA k N V π hs hi) hi

end GlobalTheory.CompanionTheory.GKLocalProof
