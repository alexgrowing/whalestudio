import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

open GlobalTheory.CechPic GlobalTheory.Poinc.GalTrans

theorem exists_twist_along_genericAutomorphism {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S S' : ThetaSys o Ω} (ρ : S.Real)
    (ρ' : S'.Real) (l' : S.Gam → S'.Gam) (h' : USame ρ ρ' l' (RingHom.id _)) (σ τ : Ω →+* Ω)
    (hτ : τ.comp σ = RingHom.id _) (hσ : σ.comp τ = RingHom.id _) (a : S.Gam → S.Gam)
    (P₀ : PolAV (Sp Ω)) (b : P₀.A.left ⟶ ρ.P.A.left) (t : P₀.A.left ⟶ P₀.A.left)
    (hb : IsGrpPullback P₀.A ρ.P.A (spMap S.R.val.toRingHom) b)
    (ht : IsGrpPullback P₀.A P₀.A (spMap σ) t) (lb : LBIso P₀.L (ρ.P.L.pull b)) (lt : LBIso P₀.L (P₀.L.pull t))
    (hp : ∀ x (w w' : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
      w' ≫ t = spMap σ ≫ w → w' ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt (a x)).left)
    {B : Scheme.{0}} {v : Sp Ω ⟶ B} {r : B ⟶ Sp S'.R} (hv : v ≫ r = spMap S'.R.val.toRingHom)
    (G : Over B) [GrpObj G] (α : G.left ⟶ ρ'.P.A.left) (hα : IsGrpPullback G ρ'.P.A r α)
    {Y : Scheme.{0}} (N : LB Y) (hN : N.IsLB) (β : G.left ⟶ Y) (hL : LBIso (ρ'.P.L.pull α) (N.pull β)) :
    ∃ (P₁ : PolAV (Sp Ω)) (e : P₁.A.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ P₁.A.left) (k₀ : P₁.A.left ⟶ G.left),
      IsGrpPullback P₁.A P₀.A (spMap σ) e ∧ IsGrpPullback P₀.A P₁.A (spMap τ) j ∧ IsGrpPullback P₁.A G v k₀ ∧
      e ≫ j = 𝟙 _ ∧ LBIso (ρ.P.L.pull b) (N.pull (j ≫ k₀ ≫ β)) ∧
      ∀ x (w : Sp Ω ⟶ P₀.A.left), w ≫ b = spMap S.R.val.toRingHom ≫ (ρ.pt x).left →
        ∃ w₀ : Sp Ω ⟶ P₁.A.left, w₀ ≫ P₁.A.hom = 𝟙 _ ∧ w₀ ≫ e = spMap σ ≫ w ∧
          w₀ ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt (l' (a x))).left := by
  obtain ⟨P₁, a₁, a₁', ha₁, ha₁', la₁, la₁', hp₁⟩ := h'
  rw [RingHom.id_comp] at ha₁ hp₁
  have := mono_val S.R S.frac
  have : Mono b := (MorphismProperty.monomorphisms Scheme).of_isPullback hb.1.flip (.infer_property _)
  obtain ⟨κ, hκ, lκ, eκ⟩ := exists_factor ρ.P P₀ P₁ (Category.id_comp _) hb ha₁ lb la₁
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  have e₁ : spMap τ ≫ spMap σ = 𝟙 (Sp Ω) := (sp_comp hτ).trans hid
  have e₂ : spMap σ ≫ spMap τ = 𝟙 (Sp Ω) := (sp_comp hσ).trans hid
  have he : IsGrpPullback P₁.A P₀.A (spMap σ) (κ ≫ t) := (hκ.comp ht).congr (Category.id_comp _) rfl
  have le := lb_comp P₁.isLB P₀.isLB P₀.isLB lκ lt
  have : IsIso (spMap σ) := ⟨_, e₂, e₁⟩
  have : Mono (κ ≫ t) := (MorphismProperty.monomorphisms Scheme).of_isPullback he.1.flip (.infer_property _)
  have : IsMonHom (Iso.refl P₀.A).hom := inferInstanceAs (IsMonHom (𝟙 P₀.A))
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P₀ P₁ P₀ (ψ := 𝟙 _) e₁ he (isGrpPullback_of_iso (Iso.refl P₀.A)) le
    ((iso_iff P₀.isLB P₀.isLB _).2 (by rw [GlobalTheory.CechPic.pull_id]; try rfl))
  have w₁ : a₁' ≫ ρ'.P.A.hom = (P₁.A.hom ≫ v) ≫ r := by rw [ha₁'.1.w, Category.assoc, hv]
  have k₁ := hα.1.lift_fst _ _ w₁
  have k₂ := hα.1.lift_snd _ _ w₁
  generalize hα.1.lift _ _ w₁ = k₀ at k₁ k₂
  have hs : ∀ x, (ρ.pt x).left ≫ ρ.P.A.hom = 𝟙 _ := fun x => Over.w (ρ.pt x)
  refine ⟨P₁, κ ≫ t, j, k₀, he, hj, hα.cancel (ha₁'.congr hv.symm k₁.symm) k₂, ?_, ?_, fun x w hw => ?_⟩
  · rw [← cancel_mono (κ ≫ t), Category.assoc, ej, Category.comp_id, Category.id_comp]
  · have c₁ := (iso_iff (pull_isLB ρ'.P.isLB α) hN β).1 hL
    rw [cls_pull ρ'.P.isLB] at c₁
    rw [iso_iff (pull_isLB ρ.P.isLB b) hN, cls_pull ρ.P.isLB, ← (iso_iff P₀.isLB ρ.P.isLB _).1 lb,
      (iso_iff P₀.isLB P₁.isLB _).1 lj, (iso_iff P₁.isLB ρ'.P.isLB _).1 la₁', ← k₁, pull_comp, pull_comp, pull_comp, c₁]
  · obtain ⟨u, f₁, f₁'⟩ := hp₁ (a x)
    have k₃ : w ≫ P₀.A.hom = 𝟙 _ := by
      rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← hb.1.w, reassoc_of% hw, hs]
      simp
    have c₂ : (spMap σ ≫ w) ≫ P₀.A.hom = 𝟙 _ ≫ spMap σ := by rw [Category.assoc, k₃]; simp
    have k₄ := ht.1.lift_fst _ _ c₂
    generalize ht.1.lift _ _ c₂ = w' at k₄
    have k₅ : u ≫ κ = w' := by
      rw [← cancel_mono b, Category.assoc, eκ, f₁, hp x w w' hw k₄]
    refine ⟨u, ?_, by rw [reassoc_of% k₅, k₄], by rw [k₁, f₁']⟩
    rw [← cancel_mono (spMap S.R.val.toRingHom), Category.assoc, ← ha₁.1.w, reassoc_of% f₁, hs]
    simp

theorem exists_conj_uWit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hs hu G _ α β hα hβ hL
  obtain ⟨P₀, b, t, hb, ht, lb, lt, hp⟩ := hG
  obtain ⟨P₁, e, j, k₀, he, hj, hk, ej, hL', hpt⟩ := exists_twist_along_genericAutomorphism D.X.ρ ρ' _ hs (σ : D.X.Ω₁ →+* D.X.Ω₁)
    (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) (RingHom.ext fun x => σ.symm_apply_apply x) (RingHom.ext fun x => σ.apply_symm_apply x)
    a P₀ b t hb ht lb lt hp (spMap_val_toRat R') G α hα _ Xo.univ.t.PP.isLB β hL
  have h₁ : spMap (σ.symm : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.uΩ = D.X.uΩ := by
    rw [D.pt, ← Category.assoc, sp_comp (RingHom.ext fun x => σ.symm.commutes x)]
  have hβ' : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (j ≫ k₀ ≫ β) :=
    (hj.comp (hk.comp hβ)).congr (by rw [← Category.assoc _ u', hu, ← Category.assoc, h₁]) rfl
  exact ⟨{ G := P₀.A, α := b, β := j ≫ k₀ ≫ β, hα := hb, hβ := hβ', hL := hL' }, P₁.A, inferInstance, e, k₀, he, hk,
    by rw [reassoc_of% ej], hpt⟩

end GlobalTheory.UPoinc.UGalTrans
