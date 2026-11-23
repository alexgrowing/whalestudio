import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsVtOverIsUUOverBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicConnectionValueBaseChangeFieldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (hm : FrMap ψ y z) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    (hF : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x (x b)) (F b)) :
    ∃ F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (F' b)) ∧
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab z P F' := by
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hm.1.symm
  choose F' hF' using fun b => GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2)
    (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b)
  refine ⟨F', fun b => ?_, ?_⟩
  · have e : h ≫ levPt Xo y.x (x b) = levPt Xo z.x (x b) := by
      unfold levPt
      rw [← Category.assoc, comp_toUnit]
    rw [← e]
    exact (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) _ _ h y.s z.s
      (GlobalTheory.FramedBaseChange.isPullSec ψ hm h rfl) (F b) (F' b) (hF' b)).1 _ (hF b)
  · unfold thExpr
    rw [map_mul, AlgHom.commutes,
      GlobalTheory.T.harmonicConnectionValue_baseChange_field E H Dw l Xo c nab hnab S T ψ y z hm h rfl a n P hP.1 l.M F F' hF']

theorem exists_algHom_field (F U : Type) [Field F] [CommRing U] [Algebra F U] [Nontrivial U] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K), Nonempty (U →ₐ[F] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal U
  exact ⟨U ⧸ m, Ideal.Quotient.field m, inferInstance, ⟨Ideal.Quotient.mkₐ F m⟩⟩

theorem thetaValue_natural_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S T : Type) [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y0 : FrPt Xo c S) (y : FrPt Xo c T), FrMap φ y0 y → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ v0 w, ThValAt Xo c nab y0 x P v0 → ThValAt Xo c nab y x P w → φ v0 = w := by
  intro E _ _ _ H Dw l Xo c _ nab hnab S T _ _ _ _ φ y0 y hφ a n x P hP v0 w hv hw
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨S₁, i₁, j₁, φ₁, y₁, F₁, hff₁, hm₁, hV₁, he₁⟩ := hv
  obtain ⟨T₁, i₂, j₂, κ, y₂, F₂, hff₂, hm₂, hV₂, he₂⟩ := hw
  obtain ⟨U, iU, jU, ψ₁, ψ₂, hcomm, -, hinj⟩ :=
    exists_faithfullyFlat_pushout c.F S T₁ S₁ (κ.comp φ) φ₁ hff₁
  have hκ : Function.Injective κ := hff₂.injective
  haveI : Nontrivial U := (hinj.comp hκ).nontrivial
  obtain ⟨K, iK, jK, ⟨π⟩⟩ := exists_algHom_field c.F U
  have hψ : (π.comp ψ₁).comp (κ.comp φ) = (π.comp ψ₂).comp φ₁ := by
    rw [AlgHom.comp_assoc, hcomm, AlgHom.comp_assoc]
  obtain ⟨z, hz1⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw l Xo c T₁ K (π.comp ψ₁) y₂
  have hz : FrMap ((π.comp ψ₂).comp φ₁) y0 z :=
    hψ ▸ GlobalTheory.FramedBaseChange.trans (κ.comp φ) (π.comp ψ₁) (FramedBaseChange.trans φ κ hφ hm₂) hz1
  have hz2 : FrMap (π.comp ψ₂) y₁ z := GlobalTheory.FramedBaseChange.cancel φ₁ (π.comp ψ₂) hm₁ hz
  obtain ⟨G1, w1, e1⟩ := exists_pull nab hnab (π.comp ψ₁) y₂ z hz1 a n x P hP F₂ hV₂
  obtain ⟨G2, w2, e2⟩ := exists_pull nab hnab (π.comp ψ₂) y₁ z hz2 a n x P hP F₁ hV₁
  have hG : G1 = G2 := funext fun b => vtUniq_obj hL.globalFns Xo.univ (w1 b) (w2 b)
  apply ((π.comp ψ₁).comp κ).toRingHom.injective
  change (π.comp ψ₁) (κ (φ v0)) = (π.comp ψ₁) (κ w)
  rw [he₂, e1, hG, ← e2, ← he₁]
  exact AlgHom.congr_fun hψ v0

end GlobalTheory.ThetaField
