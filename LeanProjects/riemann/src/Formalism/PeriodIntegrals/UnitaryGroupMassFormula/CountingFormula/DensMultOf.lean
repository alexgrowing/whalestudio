import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) →
          ∃ C : ℝ, ∀ᶠ p in Filter.cofinite,
            |densP L δ ϖ (Tn u) (Tn u') Z p - 1| ≤ C * (1 / ((p.asIdeal.absNorm : ℝ) ^ 2))

def PrimeZeta2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Summable (fun p : HeightOneSpectrum (𝓞 K) => 1 / ((p.asIdeal.absNorm : ℝ) ^ 2))

theorem densMult_of (hG : DensGood) (hZ : PrimeZeta2) : DensMult := by
  intro D δ M hA L u u' hc F0 what₂ hr ϖ hϖ Z hpos
  obtain ⟨C, hC⟩ := hG D δ M hA L u u' hc F0 what₂ hr ϖ hϖ Z hpos
  have hs : Summable (fun p => ‖densP L δ ϖ (Tn u) (Tn u') Z p - 1‖) := by
    refine Summable.of_norm_bounded_eventually (g := fun p : PlF D => C * (1 / ((p.asIdeal.absNorm : ℝ) ^ 2))) ?_ ?_
    · exact (hZ _).mul_left C
    · filter_upwards [hC] with p hp
      simpa [Real.norm_eq_abs] using hp
  have hm := multipliable_one_add_of_summable hs
  simpa using hm

end PI.UnitaryGroupMassFormula.CntFormula
