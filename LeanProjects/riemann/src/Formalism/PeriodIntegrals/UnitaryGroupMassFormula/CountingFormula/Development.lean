import Mathlib
import Formalism.PeriodIntegrals.CntLocalParts

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def OrbitFinite : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (_L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ → ∀ Z : MatZ D, ∀ Λ ∈ what₂, cntE (Tn u') F0 Λ Z ≠ ⊤

def DensIndep : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ ϖ' : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → (∀ p, Irreducible (ϖ' p)) →
        ∀ Z : MatZ D, densP L δ ϖ (Tn u) (Tn u') Z = densP L δ ϖ' (Tn u) (Tn u') Z

def DensMult : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)

def MassAtUnif : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∃ c : ℝ, 0 < c ∧ ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) →
          nu (Tn u') F0 what₂ Z = c * sqrtAbsNormOfScaledGram (Tn u) (Tn u') Z ^ (D.R.k - 1) * ∏' p, densP L δ ϖ (Tn u) (Tn u') Z p

theorem cntFormula_of (h1 : OrbitFinite) (h2 : DensIndep) (h3 : DensMult) (h4 : MassAtUnif) :
    PI.CntLocalParts.FormulaAll := by
  unfold PI.CntLocalParts.FormulaAll
  intro D δ M hA L u u' hc F0 what₂ hr
  by_cases hex : ∃ ϖ₀ : (∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), ∀ p, Irreducible (ϖ₀ p)
  · obtain ⟨ϖ₀, hϖ₀⟩ := hex
    obtain ⟨c, hc0, hcf⟩ := h4 D δ M hA L u u' hc F0 what₂ hr ϖ₀ hϖ₀
    refine ⟨c, ?_⟩
    unfold Formula
    refine ⟨hc0, fun ϖ hϖ Z => ⟨fun Λ hΛ => h1 D δ M hA L u u' hc F0 what₂ hr Z Λ hΛ, fun hpos => ?_⟩⟩
    refine ⟨h3 D δ M hA L u u' hc F0 what₂ hr ϖ hϖ Z hpos, ?_⟩
    rw [h2 D δ M hA L u u' hc F0 what₂ hr ϖ ϖ₀ hϖ hϖ₀ Z]
    exact hcf Z hpos
  · refine ⟨1, ?_⟩
    unfold Formula
    exact ⟨one_pos, fun ϖ hϖ _ => (hex ⟨ϖ, hϖ⟩).elim⟩

end PI.UnitaryGroupMassFormula.CntFormula
