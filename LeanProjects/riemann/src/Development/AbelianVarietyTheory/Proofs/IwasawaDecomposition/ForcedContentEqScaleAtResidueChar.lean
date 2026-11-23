import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem fvalP_eq_FK (D : D7) (L : SizeData₂ D) (j p : ℕ) :
    FvalP L j p = FK L.sc D j p := by
  have hg : (p ∈ L.gTypes) ↔ ∃ i, p = D.host.g i := by
    simp only [Formalism.BasicNotions.SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  unfold FvalP FK
  by_cases h : ∃ i, p = D.host.g i
  · rw [if_pos (hg.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hg.mp h')), if_neg h]

theorem Fval_eq_FK : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl),
    Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  intro D L j v
  exact fvalP_eq_FK D L j _

theorem resChar_eq_plc (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  have hp : (D.what₂.places.resChar w).Prime := D.what₂.places.resChar_prime w
  have hmem := Formalism.L2.Col.att_resChar_mem D.what₂.places D.plEq D.val_eq w
  haveI : Nontrivial (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 (D.plEq w).isPrime.ne_top
  have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have hdvd : ringChar (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) ∣ D.what₂.places.resChar w :=
    ringChar.dvd h0
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1.symm

theorem ofRecord_Fj_succ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (hK : DV.KapDef D)
    (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    (Formalism.L2.DIV.ofRecord D L Del h0).Fj ((j : ℕ) + 1) y = F0K L.sc D y j := by
  have h := Formalism.L2.DIV.ofRecord_Fval D L Del h0 hK (j := (j : ℕ) + 1) (Nat.le_add_left 1 _)
    (Nat.succ_le_of_lt j.isLt) (D.plEq.symm y)
  rw [Fval_eq_FK] at h
  have hc : D.what₂.places.resChar (D.plEq.symm y) = Formalism.EigenvalueLevelCeiling.plc y := by
    rw [resChar_eq_plc, Equiv.apply_symm_apply]
  unfold F0K Formalism.L2.DIV.NumDatum.Fj
  rw [h, hc]

end GlobalTheory.Mem.Top.Bl
