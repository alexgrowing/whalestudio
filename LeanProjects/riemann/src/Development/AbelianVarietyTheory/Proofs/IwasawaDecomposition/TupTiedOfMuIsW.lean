import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIs

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTieW

theorem tupTied_of_muIsW : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E), V4.MuIsW X f T Wt xi → (∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt) ∧ Wt.Finite ∧ (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) ∧ ∀ nch : NChoice X.toD7, (∀ w ∈ Wt, nch.Q w = T.Q w) → ∃ tp : TupTied X.toD7 (Fr.at X f) nch, tp.xi = xi ∧ tp.psi = T.psi := by
  intro X f T Wt xi h
  have key : ∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt := by
    intro w
    constructor
    · intro hw
      by_contra hn
      exact hw (h.off w hn)
    · intro hw he
      have he' : X.W.muAt w = X.C.mu0 := he
      rw [h.on w hw] at he'
      have h1 := h.tw w
      rw [he', h.mu0] at h1
      exact (TwFin.tw_fin X.B f T).2.1 w h1.symm
  have hfin : Wt.Finite :=
    Set.Finite.subset (TwFin.tw_fin X.B f T).2.2.2 fun w hw => h.sub w hw
  have hconj : ∀ w ∈ Wt, X.B.places.conj w ∈ Wt := by
    intro w hw
    refine (key _).1 ?_
    have hc : X.toD7.what₂.muAt (X.toD7.what₂.places.conj w) = X.toD7.what₂.muAt w :=
      X.toD7.what₂.muAt_conj w
    intro he
    exact (key w).2 hw (hc.symm.trans he)
  refine ⟨key, hfin, hconj, fun nch hQ => ?_⟩
  have hg : ∀ μ, TupTie.Good X.B.host.F (xi μ) :=
    fun μ => TupTie.good_set f T (h.range ▸ Set.mem_range_self μ)
  refine ⟨⟨xi, h.inj, fun μ => (hg μ).1, fun μ => (hg μ).2.1, fun μ => (hg μ).2.2, T.psi, h.mu0, h.star, h.star', h.tw,
    fun w hw => ?_, fun w hw => ?_⟩, rfl, rfl⟩
  · rw [hQ w ((key w).1 hw)]
    exact T.psi_is w
  · exact h.supp w fun hn => (key w).2 hn hw

end GlobalTheory.Mem.Top.TupTieW
