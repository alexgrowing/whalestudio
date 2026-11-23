import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.GaussianCaseFreeExponents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField MvPowerSeries Formalism.MainNotions.GradedPowerSeriesLemmas

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} {V : VData D}
variable {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}

structure Comparison₂ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1) where

  v : T.P.lPl
  pt : Ideal (T.P.RV v).C
  hpt : Formalism.MainNotions.UnitaryThreeHeightBounds.IsRt T v pt

  Jh : Ideal (MvPowerSeries (Fin P.a) (V.Ol l))
  Jh_closed : Formalism.MainNotions.UnusedSlot38.IsClosedAdic Jh
  Jh_hom : Formalism.MainNotions.UnusedSlot38.IsHomog (W P.wt) Jh
  ideal_constantCoeff_zero : ∀ f ∈ Jh, constantCoeff f = 0
  h𝔓 : P.𝔓 = PofJ P.wt Jh

  b : ℕ
  wz : Fin b → ℤ
  eA : (MvPowerSeries (Fin P.a) (V.Ol l) ⧸ Jh) ≃+* MvPowerSeries (Fin b) ((T.P.RV v).C ⧸ pt)
  eA_O : ∀ x : T.P.O, eA (Ideal.Quotient.mk Jh (C (T.eO x))) =
    C (Ideal.Quotient.mk pt (algebraMap T.P.O (T.P.RV v).C x))

  generator_mem_weight_ideal : ∀ i, eA.symm (X i) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj (wz i))
  eA_R : ∀ (j : ℤ) (x : (T.P.RV v).C), Formalism.BasicNotions.V1.IsEigen (T.P.coV v) (fun _ => j) x →
    eA.symm (C (Ideal.Quotient.mk pt x)) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj j)

  generator_constantCoeff_zero : ∀ i, Ideal.Quotient.lift Jh (constantCoeff (σ := Fin P.a) (R := V.Ol l)) ideal_constantCoeff_zero (eA.symm (X i)) = 0
  constantCoeff_at_reduced_point : ∀ φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O, Formalism.MainNotions.UnitaryThreeHeightBounds.IsInitialPoint T v φ₀ → ∀ x : (T.P.RV v).C,
    Ideal.Quotient.lift Jh (constantCoeff (σ := Fin P.a) (R := V.Ol l)) ideal_constantCoeff_zero
      (eA.symm (C (Ideal.Quotient.mk pt x))) = T.eO (φ₀ x)

  toS : (MvPowerSeries (Fin P.a) (V.Ol l) ⧸ Jh) →+* V.S3hat l e χ K g1
  toS_surj : Function.Surjective toS
  toS_ker : RingHom.ker toS = Ideal.span ((fun f : PT (V.Ol l) P.wt => Ideal.Quotient.mk Jh (f : MvPowerSeries (Fin P.a) (V.Ol l))) ''
    (Set.range P.F ∪ Set.range P.G ∪ Set.range P.E1 ∪ Set.range P.E2 ∪ Set.range P.Z))
  toS_S : ∀ f : PT (V.Ol l) P.wt, toS (Ideal.Quotient.mk Jh (f : MvPowerSeries (Fin P.a) (V.Ol l))) =
    V.S3emb l e χ K g1 (P.eS (mkS P.𝔓 P.F P.G P.E1 P.E2 P.Z f))

  toS_loc : ∀ x : (T.P.RV v).C, toS (eA.symm (C (Ideal.Quotient.mk pt x))) =
    T.eS (T.Q.q (Formalism.MainNotions.UnusedSlot38.resMap T.P v x))

  card_weight_neg_two_eq : P.s = 1 + Fintype.card {i // wz i = -2}
  cnt_r : P.r = 2 + Fintype.card {i // wz i = -1}
  cnt_m : P.m = 3 + Fintype.card {i // wz i = 0}
  cnt_r' : P.r' + 1 = 4 + Fintype.card {i // wz i = 1}
  card_weight_two_eq : P.s' + 1 = 2 + Fintype.card {i // wz i = 2}

variable (V)

def StepPresT : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1, ∃ P : Pres V l e χ K g1,
      Nonempty (Comparison₂ T P) ∧ DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z

def FirstModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1), Comparison₂ T P →
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z → M1 P.𝔓 P.F P.G P.Z P.r' P.s' l

def StepSha : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1), Comparison₂ T P →
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z → V.Vlen l e χ ≤ VPrime P.𝔓 P.F

theorem stepA_of (h1 : StepPresT V) (h2 : FirstModuleCondition V) (h3 : StepSha V) : StepA V := by
  intro hG l _ e χ K _ g1 dat
  obtain ⟨T⟩ := hG.1.1 l e χ K dat.data g1 dat.norm
  obtain ⟨P, ⟨tie⟩, hD⟩ := h1 hG l e χ K g1 dat T
  exact ⟨P, hD, h2 hG l e χ K g1 dat T P tie hD, h3 hG l e χ K g1 dat T P tie hD⟩

end Formalism.MainNotions.V.Pf.V3
