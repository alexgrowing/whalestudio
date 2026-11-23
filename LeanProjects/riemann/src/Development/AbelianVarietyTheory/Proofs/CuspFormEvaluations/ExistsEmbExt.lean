import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinearStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in

theorem _root_.GlobalTheory.FieldBC.exists_emb_ext {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} (hle : c.F ≤ c'.F) (σ : c.F →+* ℂ) :
    ∃ σ' : c'.F →+* ℂ, σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle) = σ := by
  letI : Algebra c.F c'.F := (_root_.Formalism.L2.Pj.incF c c' hle).toAlgebra
  letI : Algebra c.F ℂ := σ.toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic ℚ c'.F := Algebra.IsAlgebraic.of_finite ℚ c'.F
  haveI : Algebra.IsAlgebraic c.F c'.F := Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let τ : c'.F →ₐ[c.F] ℂ := IsAlgClosed.lift
  refine ⟨τ.toRingHom, ?_⟩
  ext x
  exact τ.commutes x

set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory NumberField in

theorem _root_.GlobalTheory.FieldBC.rulBC_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c c' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)
    (hle : c.F ≤ c'.F) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, _root_.Formalism.L2.Pj.Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ)
    (n : ℕ), ∀ f ∈ _root_.Formalism.L2.Pj.sec Xo c a n,
    (∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f) ∧
    (_root_.GlobalTheory.FieldBC.rulBC hle f ∈ _root_.Formalism.L2.Pj.cusp Xo c' (_root_.Formalism.L2.Pj.unfBC hle U) a n ↔ f ∈ _root_.Formalism.L2.Pj.cusp Xo c U a n) := by
  intro E _ _ _ H Dw l Xo c c' hle r U a n f hf
  obtain ⟨hsec, hval⟩ := (_root_.GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf
  have hread : ∀ σ' : c'.F →+* ℂ, _root_.Formalism.L2.Pj.rdU (_root_.Formalism.L2.Pj.unfBC hle U σ') (_root_.GlobalTheory.FieldBC.rulBC hle f) =
      _root_.Formalism.L2.Pj.rdU (U (σ'.comp (_root_.Formalism.L2.Pj.incF c c' hle))) f := by
    intro σ'
    have hbc : _root_.Formalism.L2.Pj.IsBC hle (_root_.GlobalTheory.FieldBC.rulBC hle f) ![1] ![f] := by
      unfold _root_.Formalism.L2.Pj.IsBC
      intro S _ _ _ h y
      simp [hval S h y]
    rw [_root_.Formalism.L2.Pj.rdU_unfBC hle U σ' hbc, Fin.sum_univ_one]
    simp only [Matrix.cons_val_zero, map_one]
    exact one_smul ℂ _
  refine ⟨hread, ?_⟩
  rw [_root_.Formalism.L2.Pj.mem_cusp, _root_.Formalism.L2.Pj.mem_cusp]
  constructor
  · rintro ⟨-, hcusp⟩
    refine ⟨hf, fun σ hσ => ?_⟩
    obtain ⟨σ', rfl⟩ := _root_.GlobalTheory.FieldBC.exists_emb_ext hle σ
    have hmem := hcusp σ' (_root_.Formalism.L2.Pj.goodEmb_ext hle hσ rfl)
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC] at hmem
    exact hmem
  · rintro ⟨-, hcusp⟩
    refine ⟨hsec, fun σ' hσ' => ?_⟩
    rw [hread, _root_.Formalism.L2.Pj.laU_unfBC]
    exact hcusp _ (by unfold _root_.Formalism.L2.Pj.GoodEmb at hσ' ⊢; exact hσ')

end GlobalTheory.FieldBC
