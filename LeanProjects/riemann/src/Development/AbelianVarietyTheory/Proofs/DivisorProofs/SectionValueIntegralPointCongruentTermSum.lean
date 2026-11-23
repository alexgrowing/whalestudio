import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval

theorem value_sub_sum_mem_hRed : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  intro R _ _ I D A G _ _ U h g hF f t e k hT σ fs hE x hx a ha
  let s : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e (𝟙_ (Over (Sp R)))).left :=
    pullback.lift (thick R I e) (𝟙 _) (by simp)
  have hs1 : s ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e := pullback.lift_fst _ _ _
  have hs2 : s ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  obtain ⟨hb, hχ⟩ := hF e
  have hp : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
    rw [← hs2, Category.assoc, ← hb, ← Category.assoc, hs1]
  have hf : hRed I h e ≫ fGl I G e = thick R I e ≫ h.left := hRed_fst h e
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ fs hE
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT' => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, GlobalTheory.ExpansionValueZero.cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (hRed I h e) z J hJ
  have h₂ := h₁ (J' (hRed I h e ≫ fGl I G e)) (hJ' (hRed I h e ≫ fGl I G e))
  have hsv : sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e)) =
      cst (thick R I e) z x * (val f (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ h.left)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (hRed I h e) z J = val (g.s α) (thick R I e) z J := fun α => by
    have e₁ := (val_pull hJ (tG U e α) ((Over.pullback (thick R I e)).map h).left s).symm
    have e₂ := (val_corr hJ (hχ α) s).symm
    have e₃ := val_pull hJ (g.s α) (fstG I e (𝟙_ (Over (Sp R)))).left s
    rw [hs2] at e₁
    rw [hs1] at e₃
    exact e₁.trans (e₂.trans e₃)
  have hg : ∀ α, sval (fs α) (hRed I h e ≫ pGl U e) z J = sval (fs α) (thick R I e ≫ g.b.left) z J := fun α => by
    rw [hp]
  have hTR := hT _ (𝟙 _) z J J' hJ hJ'
  simp only [Category.id_comp] at hTR
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT' (fun α _ hα => (ha α _ _ z J hJ).symm.trans
    (by rw [← hg, h₀ α hα, zero_mul, zero_mul]))]
  have L₁ : cst (thick R I e) z x * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val =
      ((wv U e (hRed I h e) z (J (hRed I h e ≫ pGl U e)) (J' (hRed I h e ≫ fGl I G e)) ^ k).val *
        sv U k σ (hRed I h e ≫ fGl I G e) z (J' (hRed I h e ≫ fGl I G e))) *
        (val t (thick R I e) z J ^ k).val := by
    rw [hsv, ← hTR]
    simp only [mul_pow, Units.val_mul]
    ring
  rw [L₁, h₂, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ht, hg]
  exact ha α _ _ z J hJ

end GlobalTheory.Poinc.IntEval
