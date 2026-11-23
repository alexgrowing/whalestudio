import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FgOfSmulLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover

open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.ClsVal

theorem evR_eq_clsSum : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A : AnFib X bas idx e x L y₂), FrOver d y₂ y → IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (q0 : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → ∀ (θ : (Fin g → ℂ) → ℂ) (v : TF n g) (κ : ℂ), A.Reads 1 y₂.s θ → IsVac X bas (H.w0 : E) (tens (stdL E n) L) v → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ L mk → A.Marked mk → ∀ (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (xs : Cl → Vs) (a : (E →+* ℂ) × ℕ → ℕ), LatsOK d.l₂.M La Nc → (∀ k, io (xs k) ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → ∀ Y : Cl → (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, (∀ k, IsRoots d.l₂ L mk (Nc k) (Y k)) → ∀ f : Rul Xo c, IsThClsD Xo c d w La Nc gam vol ep io xs f → evR Xo c f y = evR d.Xo₂ d.c₂ d.cδ y₂ * κ * clsSum (algebraMap c.F ℂ) X hr bas idx eL w La Nc gam vol ep (fun k => io (xs k)) L v Y x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hF ⟨inst, hnab⟩ r g X bas idx e x L y y₂ A hov hs hx hL q0 hr eL hr' hn
    hlet θ v κ hread hvac hκ mk hmk hA Cl _ w La Nc gam vol ep Vs _ _ io xs a hLa hH Y hY f hf
  obtain ⟨vc, hvc, hev⟩ := hf ℂ hF y y₂ hov
  have hcomp : (algebraMap d.c₂.F ℂ).comp (d.eF : c.F →+* d.c₂.F) = algebraMap c.F ℂ :=
    RingHom.ext fun t => hF t
  rw [hev, mul_assoc, clsSum, Finset.mul_sum _ _ κ]
  refine congrArg (fun t => evR d.Xo₂ d.c₂ d.cδ y₂ * t) (Finset.sum_congr rfl fun k _ => ?_)
  obtain ⟨h1, h2, h3⟩ := hLa k
  have hV : (La k).La ∈ Vset E n d.l₂.M :=
    (GlobalTheory.Dict.GenLatCmp.genLat_vset E n (La k).La).2.1 _ (Nc k) d.l₂.odd.pos h1 h2 h3
  have hP := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a _ (hH k)
  have h := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X bas idx e x L y₂ A hs hx hL q0 n hr eL hr' hn hlet
    d.nab₂ hnab θ v κ hread hvac hκ mk hmk hA (La k).La hV (Nc k) h3 (Y k) (hY k) a _ hP _ 1 (vc k) (hvc k)
  rw [h, MvPolynomial.map_map, hcomp]
  simp only [hF, map_mul, map_inv₀, map_natCast, inv_one, map_one]
  ring

end GlobalTheory.ClsVal
