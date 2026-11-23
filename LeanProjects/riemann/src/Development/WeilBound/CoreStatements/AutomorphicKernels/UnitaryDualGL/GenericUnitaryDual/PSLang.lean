import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Gud.Symm.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isL_of_noPrec {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL k) (hL : ∀ j, IsLSeg (Γ j) (x j).rep)
    (hp : ∀ i j, ¬ (Γ i).Precedes (Γ j)) (hd : ∑ j, (x j).1 = N) :
    (prodIrr x hd).IsIrreducible ∧ ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W),
      Nonempty ((prodIrr x hd).Equiv σ) → IsL (Finset.univ.val.map Γ) σ := by
  have hirr : (prodIrr x hd).IsIrreducible :=
    PositivityTheory.Exh.lUnlinkedIrr_of_seg PositivityTheory.RgGu.segmentRepresentation k h N Γ x hd
      (fun i j hl => (GlobalTheory.SmGL.Segment.linked_iff_precedes.mp hl).elim (hp i j) (hp j i)) hL
  refine ⟨hirr, ?_⟩
  intro W _ _ σ e
  obtain ⟨e⟩ := e
  exact ⟨h, x, hd, ⟨Γ, ⟨rfl, fun i j _ => hp i j⟩, hL⟩,
    GlobalTheory.LocGL.IsCosocle.of_equiv (GlobalTheory.LocGL.isCosocle_self hirr) e (Representation.Equiv.refl _)⟩

theorem multiset_of_equiv [CharZero k] {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL k) (t t' : Fin h → ℝ)
    (hL : ∀ j, IsLSeg (Γ j) (y j).rep)
    (hp : ∀ i j, ¬ ((Γ i).nu (t i : ℂ)).Precedes ((Γ j).nu (t j : ℂ)))
    (hp' : ∀ i j, ¬ ((Γ i).nu (t' i : ℂ)).Precedes ((Γ j).nu (t' j : ℂ)))
    (hd : ∑ j, ((y j).nu (t j)).1 = N) (hd' : ∑ j, ((y j).nu (t' j)).1 = N)
    (e : Nonempty ((prodIrr (fun j => (y j).nu (t j)) hd).Equiv (prodIrr (fun j => (y j).nu (t' j)) hd'))) :
    (Finset.univ.val.map fun j => (Γ j).nu (t j : ℂ)) = Finset.univ.val.map fun j => (Γ j).nu (t' j : ℂ) := by
  obtain ⟨e⟩ := e
  obtain ⟨hi, hA⟩ := isL_of_noPrec (fun j => (Γ j).nu (t j : ℂ)) (fun j => (y j).nu (t j))
    (fun j => GlobalTheory.isLSeg_nu (hL j) _) hp hd
  obtain ⟨-, hB⟩ := isL_of_noPrec (fun j => (Γ j).nu (t' j : ℂ)) (fun j => (y j).nu (t' j))
    (fun j => GlobalTheory.isLSeg_nu (hL j) _) hp' hd'
  let z := IrrGL.of _ (isSmooth_prodIrr _ hd) hi
  have a : (prodIrr (fun j => (y j).nu (t j)) hd).Equiv z.rep := IrrGL.equivOf _ (isSmooth_prodIrr _ hd) hi
  exact (PositivityTheory.Exh.langlandsMultisegments_holds k).1 _ _ z (hA _ ⟨a⟩) (hB _ ⟨e.symm.trans a⟩)

end PositivityTheory.Gud.Symm.Pf

end
