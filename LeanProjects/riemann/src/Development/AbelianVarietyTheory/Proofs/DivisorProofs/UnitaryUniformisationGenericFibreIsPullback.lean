import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USepGen

theorem genfib_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (X₁ : GlobalTheory.GSep.GSet) (act : 𝓞 E → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (u : Sp (ratHull X₁.S.R) ⟶ Xo.XF c) (π : X₁.M.Z ⟶ C.Z), GlobalTheory.GSep.ULink C X₁ act u π → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (yK : X₁.S.R →+* FractionRing V) (x' : Sp (FractionRing V) ⟶ Sp (ratHull X₁.S.R)), x' ≫ spMap (toRat X₁.S.R) = spMap yK → GenOf Xo c (x' ≫ u) t → ∃ φ : P.A.A.left ⟶ X₁.ρ.P.A.left, IsGrpPullback P.A.A X₁.ρ.P.A (spMap yK) φ ∧ LBIso P.A.L (X₁.ρ.P.L.pull φ) ∧ ∀ a, (letI := H.starRing; (P.oA.act (H.bar a)).left) ≫ φ = φ ≫ (act a).left := by
  intro E _ _ _ H Dw _ l Xo c C X₁ act u π hL V _ _ _ _ t P yK x' hx' hgen
  obtain ⟨-, ⟨G, iG, α, β, hα, hβ, hLab, hf⟩, -, -⟩ := hL
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := hgen
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  have gpA : IsGrpPullback P.A.A t.G (jK V) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK V))).congr
      (Category.id_comp _) rfl
  have w₁ : (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V)) ≫ t.G.hom = (P.A.A.hom ≫ 𝟙 _) ≫ jK V := by
    rw [gpA.1.w, Category.comp_id]
  let κ : P.A.A.left ⟶ tK.G.left := m₁.cart.1.lift _ _ w₁
  have hκ₁ : κ ≫ m₁.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V) := m₁.cart.1.lift_fst _ _ _
  have hκ₂ : κ ≫ tK.G.hom = P.A.A.hom ≫ 𝟙 _ := m₁.cart.1.lift_snd _ _ _
  have gκ : IsGrpPullback P.A.A tK.G (𝟙 _) κ :=
    m₁.cart.cancel (gpA.congr (Category.id_comp _).symm hκ₁.symm) hκ₂
  have w₂ : m₂.φ ≫ Xo.univ.t.G.hom = (tK.G.hom ≫ x') ≫ u ≫ pullback.fst _ _ := by
    rw [m₂.cart.1.w]; simp only [Category.assoc]
  let lam : tK.G.left ⟶ G.left := hβ.1.lift _ _ w₂
  have hl₁ : lam ≫ β = m₂.φ := hβ.1.lift_fst _ _ _
  have hl₂ : lam ≫ G.hom = tK.G.hom ≫ x' := hβ.1.lift_snd _ _ _
  have gl : IsGrpPullback tK.G G x' lam :=
    hβ.cancel (m₂.cart.congr (Category.assoc _ _ _) hl₁.symm) hl₂
  refine ⟨κ ≫ lam ≫ α, (gκ.comp (gl.comp hα)).congr (by rw [Category.id_comp, hx']) rfl, ?_, ?_⟩
  · have hA := P.A.isLB
    have hT := t.PP.isLB
    have hK := tK.PP.isLB
    have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    obtain ⟨w, hw⟩ := P.U.ext
    have hc : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.inv_hom_id]; rfl
    have e₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK V))) :=
      GlobalTheory.GenSpread.lbIso_pull_comp P.U.gen.inv.left hc.symm rfl ⟨w, hw⟩
    rw [P.bundle, ← hκ₁] at e₁
    have e₀ : LBIso P.A.L (P.A.L.pull (𝟙 _)) := GlobalTheory.SiegelPullComp.iso_pull_id hA
    obtain ⟨w₁, hw₁, -⟩ := m₁.lin
    obtain ⟨w₂, hw₂, -⟩ := m₂.lin
    have e₂ : LBIso (tK.PP.L.pull κ) (t.PP.L.pull (κ ≫ m₁.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₁, hw₁⟩ κ rfl
    have e₃ : LBIso (tK.PP.L.pull κ) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_of_lbIso ⟨w₂, hw₂⟩ κ rfl
    have e₄ : LBIso (X₁.ρ.P.L.pull (κ ≫ lam ≫ α)) (Xo.univ.t.PP.L.pull (κ ≫ m₂.φ)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp (κ ≫ lam) (Category.assoc _ _ _).symm
        (by rw [← hl₁, Category.assoc]) hLab
    refine LBIso.trans hA (pull_isLB hA _) (pull_isLB hP _) e₀ ?_
    refine LBIso.trans (pull_isLB hA _) (pull_isLB hT _) (pull_isLB hP _) e₁ ?_
    refine LBIso.trans (pull_isLB hT _) (pull_isLB hK _) (pull_isLB hP _) e₂.symm ?_
    refine LBIso.trans (pull_isLB hK _) (pull_isLB hU _) (pull_isLB hP _) e₃ ?_
    exact e₄.symm
  · intro a
    obtain ⟨f, hfα, hfβ⟩ := hf a
    letI := H.starRing
    have hext := P.lin.ext (H.bar a)
    have hg : (P.oA.act (H.bar a)).left ≫ P.U.gen.inv.left =
        P.U.gen.inv.left ≫ ((Over.pullback (jK V)).map (t.act.act (H.bar a))).left := by
      have : P.oA.act (H.bar a) ≫ P.U.gen.inv =
          P.U.gen.inv ≫ (Over.pullback (jK V)).map (t.act.act (H.bar a)) := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← hext, Category.assoc, Iso.hom_inv_id, Category.comp_id]; rfl
      rw [← Over.comp_left, this, Over.comp_left]
    have s₁ : (P.oA.act (H.bar a)).left ≫ κ = κ ≫ (tK.act.act (H.bar a)).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, hκ₁, Category.assoc, m₁.act, ← Category.assoc κ, hκ₁, ← Category.assoc, hg,
          Category.assoc, Category.assoc]
        congr 1
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, hκ₂, Category.assoc, Over.w, hκ₂, ← Category.assoc, Over.w]
    have s₂ : (tK.act.act (H.bar a)).left ≫ lam = lam ≫ f.left := by
      apply hβ.1.hom_ext
      · simp only [Category.assoc, hfβ]
        rw [hl₁, ← Category.assoc lam β, hl₁]
        exact m₂.act _
      · rw [Category.assoc, hl₂, ← Category.assoc, Over.w, Category.assoc, Over.w, hl₂]
    rw [← Category.assoc, s₁, Category.assoc, ← Category.assoc _ lam, s₂, Category.assoc, hfα]
    simp only [Category.assoc]

end GlobalTheory.USepGen
