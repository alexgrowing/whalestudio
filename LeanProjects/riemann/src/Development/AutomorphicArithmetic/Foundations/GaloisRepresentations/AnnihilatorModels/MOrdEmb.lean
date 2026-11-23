import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem img_comp (T : TjD M r w j c) {X X' : Scheme.{0}} (u : X' ⟶ X) (z : X ⟶ T.Y)
    (a : X ⟶ M.univ.A.left) (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : (u ≫ a) ≫ M.univ.A.hom = (u ≫ z) ≫ T.s) :
    u ≫ T.img z a h = T.img (u ≫ z) (u ≫ a) h' := by
  unfold TjD.img
  rw [← Category.assoc]
  congr 1
  apply T.ms.cart.1.hom_ext <;> simp

private theorem img_congr (T : TjD M r w j c) {X : Scheme.{0}} {z z' : X ⟶ T.Y}
    {a a' : X ⟶ M.univ.A.left} (h : a ≫ M.univ.A.hom = z ≫ T.s)
    (h' : a' ≫ M.univ.A.hom = z' ≫ T.s) (hz : z = z') (ha : a = a') :
    T.img z a h = T.img z' a' h' := by
  subst hz; subst ha; rfl

end

private theorem resPt_apply (V : Type) [CommRing V] [IsLocalRing V]
    (q : Spec (CommRingCat.of (IsLocalRing.ResidueField V))) :
    (resPt V) q = IsLocalRing.closedPoint V := by
  have : q = IsLocalRing.closedPoint (IsLocalRing.ResidueField V) := Subsingleton.elim _ _
  subst this
  exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.ordEmb_of :
    OrdGen → GenDown → ResClosed → OrdReadOf → EW → OrdEmb := by
  intro hOG hGD hRC hOR hEW
  intro p _ D O _ _ _ _ f b N r w _ hS M ϖ hϖ T Y h hflat I a ha hsep C g hpb hr himg
  intro V _ _ _ _ hpV y hgen φ hφ
  haveI := hRC V
  obtain ⟨hcl, hmax⟩ := hGD O ϖ hϖ M.X Y M.s h hflat _ hgen
  have hi : 0 < D.a := by rw [hS.a1]; exact Nat.one_pos
  have hcom : (IsLocalRing.maximalIdeal O).comap (b.t ⟨0, hi⟩) = w := by
    symm
    refine Ideal.IsMaximal.eq_of_le inferInstance ?_ fun x hx => hS.tw _ x hx
    exact Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hord : IsWOrd M.univ w (resPt V ≫ y ≫ h) := by
    refine hOG p D O b N hS.three hS.cop hS.pmem hS.m1 ⟨0, hi⟩ w hcom M _ hcl hmax _ _ fun q => ?_
    simp only [Scheme.Hom.comp_apply, resPt_apply]
    rfl
  obtain ⟨H, _, _, _, C₀, e, hfr, hfr1, hA, hB⟩ := hEW p D O f b N r w hS M T V hpV (y ≫ h)
    hcl hord φ hφ
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← hS.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let s : ∀ j, (C j).Sec y ≃ {z : Sp V ⟶ (T j).Y // z ≫ (T j).s = y ≫ h} := fun j =>
    { toFun := fun z => ⟨z.1 ≫ g j, by rw [Category.assoc, ← (hpb j).w, ← Category.assoc, z.2]⟩
      invFun := fun z => ⟨(hpb j).lift y z.1 z.2.symm, (hpb j).lift_fst _ _ _⟩
      left_inv := fun z => Subtype.ext ((hpb j).hom_ext (by simpa using z.2.symm) (by simp))
      right_inv := fun z => Subtype.ext ((hpb j).lift_snd _ _ _) }
  have key : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I) (e),
      resPt V ≫ z.1 ≫ (C j).r ≫ a i = (T j).img (resPt V ≫ z.1 ≫ g j) (resPt V ≫ y ≫ a i) e := by
    intro j z i e
    have e0 : ((C j).p ≫ a i) ≫ M.univ.A.hom = g j ≫ (T j).s := by
      rw [Category.assoc, ha, (hpb j).w]
    rw [himg j i e0]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (img_comp (T j) (resPt V ≫ z.1) (g j) _ e0
      (by simp only [Category.assoc]; rw [ha, (hpb j).w])).trans ?_
    refine img_congr _ _ _ (by simp) ?_
    simp only [Category.assoc]
    rw [← Category.assoc z.1, z.2]
  have hae : ∀ (j : Fin (D.n + 1)) (z : (C j).Sec y) (i : I),
      (resPt V ≫ y ≫ a i) ≫ M.univ.A.hom = (resPt V ≫ z.1 ≫ g j) ≫ (T j).s := by
    intro j z i
    simp only [Category.assoc]
    rw [ha, ← (hpb j).w, ← Category.assoc z.1, z.2]
  refine hOR (p ^ f) D.n _ (twist φ Y) _ _ (𝓞 D.F ⧸ w) H C₀ (fun j => (s j).trans (e j)) hcard hfr hfr1 ?_ ?_
  · intro j z z' h1 h2 h3
    obtain ⟨t1, t2⟩ := hA j (s j z) (s j z') h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t = resPt V ≫ (z'.1 ≫ g j) ≫ (T j).t := t1
      simp only [Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [Category.assoc]
      rw [key j z i (hae j z i), key j z' i (hae j z' i)]
      exact t2 _ _ _
  · intro j j' z z' hj h1 h2 h3
    obtain ⟨t1, t2⟩ := hB j j' (s j z) (s j' z') hj h1 h2 h3
    refine hsep _ _ _ ?_ fun i => ?_
    · have t1' : resPt V ≫ (z.1 ≫ g j) ≫ (T j).t =
          spMap φ ≫ resPt V ≫ (z'.1 ≫ g j') ≫ (T j').t := t1
      simp only [twist, Category.assoc, hr]
      simpa only [Category.assoc] using t1'
    · simp only [twist, Category.assoc]
      rw [key j z i (hae j z i), key j' z' i (hae j' z' i)]
      exact t2 _ _ _
