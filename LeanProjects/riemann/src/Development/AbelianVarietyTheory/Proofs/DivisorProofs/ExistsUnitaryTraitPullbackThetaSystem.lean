import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitPullAct

theorem mono_spMap_toRat {o Ω F : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field F] [CharZero F] (R : Subalgebra o Ω)
    (s : Sp (ratHull R) ⟶ Sp F) : Mono (spMap (toRat R)) := by
  haveI : CharZero Ω :=
    (RingHom.charZero_iff ((ratHull R).val.toRingHom.comp (Spec.preimage s).hom).injective).1 inferInstance
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  infer_instance

theorem exists_pull_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : UTrait Xo c) :
    ∃ ψ : T.P.A.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback T.P.A.A Xo.univ.t.G (T.y ≫ pullback.fst _ _) ψ ∧
      LBIso T.P.A.L (Xo.univ.t.PP.L.pull ψ) ∧
      ∀ a : 𝓞 E, (T.P.oA.act a).left ≫ ψ = ψ ≫ (Xo.univ.t.act.act a).left := by
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hm := T.P.U.gen_hom
  haveI : IsMonHom T.P.U.gen.symm.hom := inferInstanceAs (IsMonHom T.P.U.gen.inv)
  have hgen : IsGrpPullback T.P.A.A T.t.G (jK T.V) (T.P.U.gen.inv.left ≫ pullback.fst T.t.G.hom (jK T.V)) :=
    ((isGrpPullback_of_iso T.P.U.gen.symm).comp (isGrpPullback_pullback T.t.G (jK T.V))).congr (Category.id_comp _) rfl
  obtain ⟨e, he, he₁⟩ := grpPullback_iso hgen m₁.cart
  haveI := he
  refine ⟨e.hom.left ≫ m₂.cm.F, ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · have hext : LBIso (T.t.PP.L.pull (pullback.fst T.t.G.hom (jK T.V))) (T.P.A.L.pull T.P.U.gen.hom.left) := by
      obtain ⟨w, hw⟩ := T.P.U.ext
      have hb := T.P.bundle
      exact LBIso.symm (hb ▸ ⟨w, hw⟩)
    have s1 := GlobalTheory.TripleTheta.lbIso_inv T.P.U.gen hext
    have s2 := (GlobalTheory.GenSpread.lbIso_pull_pull T.t.PP.isLB (a := pullback.fst T.t.G.hom (jK T.V))
      T.P.U.gen.inv.left rfl).symm
    have s3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₁) e.hom.left he₁.symm
    have s4 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₂) e.hom.left rfl
    exact LBIso.trans T.P.A.isLB (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB Xo.univ.t.PP.isLB _) s1
      (LBIso.trans (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB T.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) s2
      (LBIso.trans (pull_isLB T.t.PP.isLB _) (pull_isLB tK.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) (LBIso.symm s3) s4))
  · letI := H.starRing
    have h0 := T.P.lin.ext a
    have h1 : T.P.oA.act a ≫ T.P.U.gen.inv = T.P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (T.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
      exact h0
    have h2 : ((Over.pullback (jK T.V)).map (T.t.act.act a)).left ≫ pullback.fst T.t.G.hom (jK T.V) =
        pullback.fst T.t.G.hom (jK T.V) ≫ (T.t.act.act a).left := pullback.lift_fst _ _ _
    have h3 : (T.P.oA.act a).left ≫ e.hom.left = e.hom.left ≫ (tK.act.act a).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, m₁.act a, ← Category.assoc e.hom.left, he₁, ← Category.assoc,
          ← Over.comp_left, h1, Over.comp_left, Category.assoc, h2, Category.assoc]
      · rw [← Over.comp_left, ← Over.comp_left, Over.w, Over.w]
    rw [← Category.assoc, h3, Category.assoc, m₂.act a, Category.assoc]

theorem exists_pull_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ S ρ u' G _ α β hα hβ hL T yK hy
  obtain ⟨ψ, hψ, hψL, hψa⟩ := exists_pull_univ T
  have e₀ : T.y ≫ pullback.fst _ _ = spMap yK ≫ u' ≫ pullback.fst _ _ := by rw [← hy, Category.assoc]
  have w₀ : ψ ≫ Xo.univ.t.G.hom = (T.P.A.A.hom ≫ spMap yK) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← e₀]; exact hψ.1.w
  have e₁ := hβ.1.lift_fst _ _ w₀
  have hγ := hβ.cancel (hψ.congr e₀ e₁.symm) (hβ.1.lift_snd _ _ w₀)
  generalize hβ.1.lift _ _ w₀ = γ at e₁ hγ
  refine ⟨γ ≫ α, (hγ.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl, ?_, fun Y x x' w w' a hw hw' h => ?_⟩
  · exact LBIso.trans T.P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB ρ.P.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp γ rfl e₁.symm hL).symm
  · haveI := mono_spMap_toRat S.R (u' ≫ pullback.snd _ _)
    haveI : Mono α := ⟨fun f g hfg => hα.1.hom_ext hfg ((cancel_mono (spMap (toRat S.R))).1 (by
      rw [Category.assoc, Category.assoc, ← hα.1.w, ← Category.assoc, hfg, Category.assoc]))⟩
    obtain rfl : w = x.left ≫ γ := (cancel_mono α).1 (hw.trans (Category.assoc _ _ _).symm)
    obtain rfl : w' = x'.left ≫ γ := (cancel_mono α).1 (hw'.trans (Category.assoc _ _ _).symm)
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψa a, ← e₁]
      simpa only [Category.assoc] using h
    · rw [Over.w, Over.w]

end GlobalTheory.UPoinc.TraitPullAct
