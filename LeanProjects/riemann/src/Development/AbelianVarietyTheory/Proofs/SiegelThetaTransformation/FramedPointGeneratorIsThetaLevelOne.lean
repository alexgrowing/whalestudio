import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ReadsExistsUniqueTheta
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibrePrincipalBundleSignEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem thetaSignExpEF_inv_of_selfDual_lattice {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (L : Lt E r) (hL : SelfD X L) (w : 𝓞 E) (v : Fin r → E) (hv : v ∈ L) :
    (eps1 X (w : E) v)⁻¹ = eps1 X (w : E) v := by
  have hwv : (w : E) • v ∈ L := by
    have h := L.smul_mem w hv
    rwa [← algebraMap_smul E w v] at h
  obtain ⟨k, hk⟩ := (hL.2 v).1 hv ((w : E) • v) hwv
  unfold eps1
  rw [hk, ← Complex.exp_neg, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  push_cast
  ring

theorem isTheta1_of_reads_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ θ, A.Reads 1 y.s θ → IsTheta1 X bas idx (H.w0 : E) x L θ := by
  intro E _ _ _ H Dw l Xo c _ r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨-, hall⟩ := reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s
  obtain ⟨hd, hper⟩ := hall θ hθ
  refine ⟨hd, fun v hv => ?_⟩
  have h := hper v hv
  rw [analyticFibre_principalBundle_sign_eq E H Dw l Xo c r g X bas idx e x L y A hs hx hL v hv, pow_one,
    thetaSignExpEF_inv_of_selfDual_lattice X L hL H.w0 v hv] at h
  exact h

end GlobalTheory.Dict
