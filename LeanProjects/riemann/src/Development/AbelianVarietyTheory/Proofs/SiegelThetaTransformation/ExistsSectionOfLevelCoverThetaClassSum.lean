import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EvRSumSmulFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescendsStatement

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

theorem GlobalTheory.exists_sec_isThClsD : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), (∀ j, DatEq d ψ (w j)) → LatsOK d.l₂.M La Nc → (∀ j, io (xs j) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d w La Nc gam vol ep io xs f := by
  intro hCI E _ _ _ H Dw l Xo c n d hlev hA hN ψ hψ Cl _ w La Nc gam vol ep Vs _ _ io xs a hw hL hio
  choose f hf hth using fun j : Cl => GlobalTheory.T.exists_section_oneClass_series_descends hCI E H Dw l Xo c n d hlev hA hN ψ hψ (w j) (hw j) (La j) (Nc j)
    (hL j).1 (hL j).2.1 (hL j).2.2 a (io (xs j)) (hio j)
  refine ⟨∑ j, (vol * ((gam j : c.F))⁻¹ * ep j) • f j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hf j), ?_⟩
  intro k _ _ _ _ hk y y₂ hy
  choose vc hvc hev using fun j => hth j k hk y y₂ hy
  refine ⟨fun j => vc j (), fun j => hvc j (), ?_⟩
  rw [GlobalTheory.evR_sum_smul_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hev j]
  simp only [Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, mul_one, map_one, one_mul]
  ring
