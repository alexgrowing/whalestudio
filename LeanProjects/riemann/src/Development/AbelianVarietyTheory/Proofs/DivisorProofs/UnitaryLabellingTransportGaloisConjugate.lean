import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRechartingsCommonGeometricFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

theorem exists_lift_rat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] {R : Subalgebra o Ω}
    {P : PolAV (Sp R)} {G : Over (Sp (ratHull R))} [GrpObj G] {α : G.left ⟶ P.A.left}
    (hα : IsGrpPullback G P.A (spMap (toRat R)) α) {K : Type} [Field K] [CharZero K] (q : Sp K ⟶ P.A.left) :
    ∃ g : Sp K ⟶ G.left, g ≫ α = q := by
  obtain ⟨x', hx', -⟩ := existsUnique_ratPoint R (q ≫ P.A.hom)
  exact ⟨hα.1.lift q x' hx'.symm, hα.1.lift_fst _ _ _⟩

set_option maxHeartbeats 1600000 in
theorem isLab_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs a hG _ p _ z₁ ct y h h' yy hy
  haveI : CharZero D.X.Ω₁ := D.X.ar.char
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, -, hu', hR, G, _, α, β, hα, hβ, hL, y₀, hy₀, u, lb, j, hq, hyy,
    hall⟩ := hy
  obtain ⟨wi, W₀, _, e, k₀, he, hk₀, heβ, htw⟩ :=
    GlobalTheory.T.exists_conj_universalTriple_identification E H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hS hu' G _ α β hα hβ hL
  obtain ⟨yy₁, hW⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C D.X wi p _ (D.lift ct (y ≫ s) h')
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'',
    ⟨m'', hm'', hmβ, hmt⟩, y₁, hy₁, u₁, lb₁, j₁, -, -, -⟩ := hW
  have hk'' : IsGrpPullback W₀ G'' (spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp (ratHull R'').val.toRingHom)) (e ≫ m'') :=
    (he.comp hm'').congr (GalTrans.sp_comp rfl) rfl
  have hββ : k₀ ≫ β = (e ≫ m'') ≫ β'' := by rw [Category.assoc, hmβ, heβ]
  obtain ⟨P₀, ka, ka', hka, hka', lka, lka', htor, hβeq⟩ := GlobalTheory.T.unitaryRechartings_common_geometricFibre E H Dw l Xo cf C D.X (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs p
    (gPt p ≫ y) _ _ ρ' ρ'' hR (by rw [Category.assoc]; exact hR₁) y₀ y₁ hy₀ (by rw [Category.assoc]; exact hy₁) u u₁ u'
    u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ (e ≫ m'') hk₀ hk'' hββ
  obtain ⟨ee, hqe, hlab, hback⟩ := GalTrans.compare u u₁ lb lb₁ P₀ ka ka' hka hka' lka lka'
  have hrN : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  refine ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'', y₁, hy₁,
    u₁, lb₁, ee.symm.trans j, fun χ => ?_, fun x χ hχ => ?_, fun m A pk' pk₂' x' x₂' w w₂ hm hQ' hQ₂' hw hw₂ hA => ?_⟩
  · rw [← ee.apply_symm_apply χ, hqe, ee.apply_symm_apply]
    exact hq (ee.symm χ)
  · obtain ⟨w, hw1, hw2⟩ := hmt x
    obtain ⟨w₀, hw₀, hw₀e, hw₀k⟩ := htw x w hw1
    have c'' : w₀ ≫ (e ≫ m'') ≫ α'' =
        spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp R''.val.toRingHom) ≫ (ρ''.pt x).left := by
      rw [Category.assoc, reassoc_of% hw₀e, hw2, ← Category.assoc, GalTrans.sp_comp rfl]
    obtain ⟨v, xo, xo', hv, hva, hva', hx, hx'⟩ := htor (a x) x w₀ hw₀ hw₀k c''
    obtain ⟨pk, pk', hQ, hQ', hcm⟩ := hlab _ xo xo' v hrN
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ xo hx)
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u₁ _ xo' hx') hv hva hva'
    refine (hyy (a x) pk.y (lb.yy_eq _ pk xo hQ hx)).trans (GalTrans.cm_mk ?_)
    have c2 : CongMod (D.X.S.r * D.X.S.N) χ pk'.y := GalTrans.cm_of_mk (hχ.symm.trans (lb₁.yy_eq x pk' xo' hQ' hx'))
    simpa using GalTrans.cm_symm (GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom (GalTrans.cm_trans c2 hcm))
  · obtain ⟨pk, xo, vo, hQ, -, hvo, hvoa, hvoa', c1⟩ := hback m pk' x' hm hQ'
    obtain ⟨pk₂, xo₂, vo₂, hQ₂, -, hvo₂, hvo₂a, hvo₂a', c2⟩ := hback m pk₂' x₂' hm hQ₂'
    obtain ⟨g, hg⟩ := exists_lift_rat hα (xo.left ≫ u.φ)
    obtain ⟨g₂, hg₂⟩ := exists_lift_rat hα (xo₂.left ≫ u.φ)
    have e1 : g ≫ β = w ≫ β'' := hβeq vo g w hvo (by rw [hg, ← hvoa, Category.assoc])
      (by rw [hw, ← hvoa', Category.assoc])
    have e2 : g₂ ≫ β = w₂ ≫ β'' := hβeq vo₂ g₂ w₂ hvo₂ (by rw [hg₂, ← hvo₂a, Category.assoc])
      (by rw [hw₂, ← hvo₂a', Category.assoc])
    have hA' : g₂ ≫ β = g ≫ β ≫ (Xo.univ.t.act.act A).left := by
      rw [e2, hA, ← Category.assoc, ← e1, Category.assoc]
    have c3 := hall m A pk pk₂ xo xo₂ g g₂ hm hQ hQ₂ hg hg₂ hA'
    have c4 : CongMod m ((ee.symm.trans j) pk₂'.y) (j pk₂.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c2
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk₂.y) = j pk₂.y from
        congrArg j (ee.symm_apply_apply pk₂.y)] at this
    have c5 : CongMod m ((ee.symm.trans j) pk'.y) (j pk.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c1
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk.y) = j pk.y from
        congrArg j (ee.symm_apply_apply pk.y)] at this
    have c6 : CongMod m (A • j pk.y) (A • (ee.symm.trans j) pk'.y) :=
      GalTrans.cm_symm (GalTrans.cm_map (DistribMulAction.toAddMonoidHom _ A) c5)
    exact GalTrans.cm_trans c4 (GalTrans.cm_trans c3 c6)

end GlobalTheory.UPoinc.UGalTrans
