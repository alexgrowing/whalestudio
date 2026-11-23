import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSectionsStatement
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem thExpr_tmul_lemma (hL : Laws) (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    [StarRing (𝓞 E)] {nab : NabV Xo c} (hnab : IsNab Xo c nab) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (x : Fin n → Dw.La)
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmA c a n)
    {S1 : Type} [CommRing S1] [Algebra c.F S1] [Algebra S S1] (φ1 : S →ₐ[c.F] S1)
    (hφ1 : ∀ s, φ1 s = algebraMap S S1 s) (y1 : FrPt Xo c S1)
    (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x)))
    (h1 : FrMap φ1 y y1)
    (hF1 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s
      (levPt Xo y1.x (x b)) (F1 b))
    {S2 : Type} [CommRing S2] [Algebra c.F S2] [Algebra S S2] (φ2 : S →ₐ[c.F] S2)
    (hφ2 : ∀ s, φ2 s = algebraMap S S2 s) (y2 : FrPt Xo c S2)
    (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x)))
    (h2 : FrMap φ2 y y2)
    (hF2 : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s
      (levPt Xo y2.x (x b)) (F2 b)) :
    TensorProduct.tmul S (thExpr Xo c nab y1 P F1) (1 : S2) =
      TensorProduct.tmul S (1 : S1) (thExpr Xo c nab y2 P F2) := by
  letI : Algebra c.F (TensorProduct S S1 S2) :=
    ((algebraMap S (TensorProduct S S1 S2)).comp (algebraMap c.F S)).toAlgebra
  let χ1 : S1 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeLeft
  let χ2 : S2 →ₐ[S] TensorProduct S S1 S2 := Algebra.TensorProduct.includeRight

  let ψ1 : S1 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ1.toRingHom with
      commutes' := fun r => by
        show χ1 (algebraMap c.F S1 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ1.commutes r, hφ1]
        exact χ1.commutes _ }
  let ψ2 : S2 →ₐ[c.F] TensorProduct S S1 S2 :=
    { χ2.toRingHom with
      commutes' := fun r => by
        show χ2 (algebraMap c.F S2 r) = algebraMap S (TensorProduct S S1 S2) (algebraMap c.F S r)
        rw [← φ2.commutes r, hφ2]
        exact χ2.commutes _ }
  have hcomp : ψ1.comp φ1 = ψ2.comp φ2 := by
    ext s
    show χ1 (φ1 s) = χ2 (φ2 s)
    rw [hφ1, hφ2, χ1.commutes, χ2.commutes]
  exact GlobalTheory.T.thetaExpression_eq_of_witnesses hL hC E H Dw l Xo c nab hnab S y a n x P hP S1 φ1 y1 F1 S2 φ2 y2 F2 h1 hF1 h2 hF2
    (TensorProduct S S1 S2) ψ1 ψ2 hcomp

theorem thValTot_of_chartIndep : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP

  obtain ⟨S', _, _, φ, y', F, hff, hy', hF⟩ := GlobalTheory.T.exists_faithfullyFlat_cover_level_sections hL E H Dw l Xo c S y n x
  letI : Algebra S S' := φ.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S' := hff
  have hφ : ∀ s, φ s = algebraMap S S' s := fun _ => rfl

  have htmul := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ hφ y' F hy' hF
  obtain ⟨v, hv⟩ := (Algebra.IsEffective.of_faithfullyFlat S S' (thExpr Xo c nab y' P F)).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, htmul, sub_self])
  refine ⟨v, ⟨S', inferInstance, inferInstance, φ, y', F, hff, hy', hF, hv⟩, ?_⟩

  rintro w ⟨S2, _, _, φ2, y2, F2, hff2, hy2, hF2, hw⟩
  letI : Algebra S S2 := φ2.toRingHom.toAlgebra
  haveI : Module.FaithfullyFlat S S2 := hff2
  have h12 := thExpr_tmul_lemma hL hC hnab y x hP φ hφ y' F hy' hF φ2 (fun _ => rfl) y2 F2 hy2 hF2
  have hv' : φ v = thExpr Xo c nab y' P F := hv
  rw [← hv', ← hw, hφ, Algebra.TensorProduct.tmul_one_eq_one_tmul] at h12
  have h3 : algebraMap S S2 v = algebraMap S S2 w :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := S) (B := S') S2 h12
  exact (FaithfulSMul.algebraMap_injective S S2 h3).symm

end GlobalTheory
