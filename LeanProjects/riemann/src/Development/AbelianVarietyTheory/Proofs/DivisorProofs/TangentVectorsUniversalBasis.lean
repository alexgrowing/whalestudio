import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocBasis

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (tvec IsUnivChart scaleD sp)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def vec {S : Type} [CommRing S] (x : Sp S ⟶ X) {n : ℕ}
    (xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G)
    (cc : Fin n → S) : Sp (DualNumber S) ⟶ t.G.left :=
  (tvec (x := xc) cc).left ≫ pullback.fst t.G.hom x

section V

variable {t} {S : Type} [CommRing S] {x : Sp S ⟶ X} {n : ℕ}
  {xc : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ (Over.pullback x).obj t.G}

theorem push_ext {Y : Over (Spec (CommRingCat.of S))} {v v' : Y ⟶ (Over.pullback x).obj t.G}
    (h : v.left ≫ pullback.fst t.G.hom x = v'.left ≫ pullback.fst t.G.hom x) : v = v' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w v).trans (Over.w v').symm

theorem tan_iff (v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v.left ≫ pullback.fst t.G.hom x = (1 : Over.mk x ⟶ t.G).left ↔
      ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := by
  have hid : (sp (R₀ := S) S).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap S S)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e0 : (1 : sp (R₀ := S) S ⟶ (Over.pullback x).obj t.G).left ≫ pullback.fst t.G.hom x =
      (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left :=
    congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) S)))
  have e1 : (1 : Over.mk ((sp (R₀ := S) S).hom ≫ x) ⟶ t.G).left = (1 : Over.mk x ⟶ t.G).left := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.one_left', ReciprocityTheory.ChartRestriction.G.Chart.one_left']
    show ((sp (R₀ := S) S).hom ≫ x) ≫ _ = x ≫ _
    rw [hid, Category.id_comp]
  rw [← e1, ← e0, ← Category.assoc]
  constructor
  · intro e
    exact push_ext e
  · intro e
    exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem vec_tan (hx : IsUnivChart _ n xc) (cc : Fin n → S) : IsTanAtG t x (vec t x xc cc) := by
  refine ⟨?_, (tan_iff _).mpr (ReciprocityTheory.ChartRestriction.G.Chart.isTan_tvec hx cc)⟩
  show ((tvec (x := xc) cc).left ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ x) (Over.w (tvec (x := xc) cc))

theorem vec_exists (hx : IsUnivChart _ n xc) (w : Sp (DualNumber S) ⟶ t.G.left) (hw : IsTanAtG t x w) :
    ∃ cc, w = vec t x xc cc := by
  let v : sp (R₀ := S) (DualNumber S) ⟶ (Over.pullback x).obj t.G :=
    Over.homMk (pullback.lift w _ hw.1) (pullback.lift_snd _ _ _)
  have hv : v.left ≫ pullback.fst t.G.hom x = w := pullback.lift_fst _ _ _
  have ht : ReciprocityTheory.ChartRestriction.G.Chart.IsTan v := (tan_iff v).mp (by rw [hv]; exact hw.2)
  refine ⟨ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht, ?_⟩
  have e : v = tvec (x := xc) (ReciprocityTheory.ChartRestriction.G.Chart.tcoord hx v ht) := ReciprocityTheory.ChartRestriction.G.Chart.tcoord_spec hx v ht
  rw [← hv]
  exact congrArg (fun q => q.left ≫ pullback.fst t.G.hom x) e

theorem tvec_sum (hx : IsUnivChart _ n xc) {m : ℕ} (a : Fin m → S) (e : Fin m → Fin n → S) :
    tvec (x := xc) (∑ j, a j • e j) =
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j)).prod := by
  induction m with
  | zero =>
    have h := ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx (0 : Fin n → S) 0
    rw [add_zero] at h
    simpa using mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  | succ m ih =>
    rw [Fin.sum_univ_succ, ReciprocityTheory.ChartRestriction.G.Chart.tvec_add hx, ReciprocityTheory.ChartRestriction.G.Chart.tvec_smul hx,
      ih (fun j => a j.succ) (fun j => e j.succ), List.ofFn_succ, List.prod_cons]

theorem comb_iff (hx : IsUnivChart _ n xc) {m : ℕ} (e : Fin m → Fin n → S) (a : Fin m → S) (cc : Fin n → S) :
    IsCombAtG t x (fun j => vec t x xc (e j)) a (vec t x xc cc) ↔ cc = ∑ j, a j • e j := by
  let P := pushHom (isGrpPullback_pullback t.G x) (sp (R₀ := S) (DualNumber S))
  let W' : Fin m → (tEpsG x ⟶ t.G) := fun j =>
    P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
  have hW' : ∀ j, (W' j).left = spMap (epsMul (a j)) ≫ vec t x xc (e j) := fun j =>
    Category.assoc _ _ _
  have hP : ((List.ofFn W').prod).left = vec t x xc (∑ j, a j • e j) := by
    have h := map_list_prod P
      (List.ofFn fun j => ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (a j)) ≫ tvec (x := xc) (e j))
    rw [← tvec_sum hx a e, List.map_ofFn] at h
    exact (congrArg (fun q => q.left) h).symm
  constructor
  · rintro ⟨u, hu, hprod⟩
    have eu' : u = W' := funext fun j => Over.OverMorphism.ext ((hu j).trans (hW' j).symm)
    rw [eu', hP] at hprod
    exact (ReciprocityTheory.ChartRestriction.G.Chart.tvec_inj hx (push_ext hprod)).symm
  · intro h
    subst h
    exact ⟨W', hW', hP⟩

theorem vec_bc [IsLocalRing S] {S' : Type} [CommRing S'] [Algebra S S'] (hx : IsUnivChart _ n xc) :
    ∃ (xc' : ∀ m : ℕ, sp (R₀ := S') (ReciprocityTheory.ChartRestriction.G.Chart.JetR S' (Fin n) m) ⟶
        (Over.pullback (spMap (algebraMap S S') ≫ x)).obj t.G), IsUnivChart _ n xc' ∧
      ∀ cc : Fin n → S, vec t (spMap (algebraMap S S') ≫ x) xc' (algebraMap S S' ∘ cc) =
        spMap (dualMap (algebraMap S S')) ≫ vec t x xc cc := by
  obtain ⟨x₁, hx₁, hcomp⟩ := ReciprocityTheory.ChartRestriction.G.Chart.tanBC_alg (R := S) (R' := S') _ n xc hx
  have h₁ := IsGrpPullback.comp
    (isGrpPullback_pullback ((Over.pullback x).obj t.G) (ReciprocityTheory.ChartRestriction.G.Chart.fB S S'))
    (isGrpPullback_pullback t.G x)
  obtain ⟨e, he, hφ⟩ := grpPullback_iso h₁
    (isGrpPullback_pullback t.G (ReciprocityTheory.ChartRestriction.G.Chart.fB S S' ≫ x))
  refine ⟨fun m => x₁ m ≫ e.hom, gfp_chart_iso e hx₁, fun cc => ?_⟩
  have key : (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left =
      (tvec (x := x₁) (algebraMap S S' ∘ cc)).left ≫ e.hom.left := by
    show (_ ≫ x₁ 1 ≫ e.hom).left = (_ ≫ x₁ 1).left ≫ e.hom.left
    rw [Over.comp_left, Over.comp_left, Over.comp_left, Category.assoc]
  show (tvec (x := fun m => x₁ m ≫ e.hom) (algebraMap S S' ∘ cc)).left ≫ pullback.fst _ _ = _
  rw [key, Category.assoc, hφ, ← Category.assoc, hcomp cc, Category.assoc]
  rfl

end V

theorem exists_lie_basis_stable (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0})
    (t : SAB H X) (S : Type) [CommRing S] [IsLocalRing S] (x : Sp S ⟶ X) :
    ∃ (n : ℕ) (D : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ e, IsTanAtG t x (D e)) ∧
      ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (w : Sp (DualNumber S') ⟶ t.G.left),
        IsTanAtG t (spMap φ ≫ x) w →
          ∃! a : Fin n → S', IsCombAtG t (spMap φ ≫ x) (fun e => spMap (dualMap φ) ≫ D e) a w := by
  have : Smooth ((Over.pullback x).obj t.G).hom := by
    have := t.semi.smooth
    show Smooth (pullback.snd t.G.hom x)
    infer_instance
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj t.G)
  refine ⟨n, fun e => vec t x xc (Pi.single e 1), fun e => vec_tan hx _, fun S' _ φ w hw => ?_⟩
  letI : Algebra S S' := φ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := S') hx
  obtain ⟨cc, rfl⟩ := vec_exists hx' w hw
  have hD : (fun e => spMap (dualMap φ) ≫ vec t x xc (Pi.single e 1)) =
      fun e => vec t (spMap (algebraMap S S') ≫ x) xc' (Pi.single e 1) := by
    funext e
    have h1 : (Pi.single e 1 : Fin n → S') = algebraMap S S' ∘ (Pi.single e 1 : Fin n → S) := by
      funext j
      by_cases h : j = e
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    exact (hv _).symm.trans (by rw [← h1])
  have hs : ∀ a : Fin n → S', ∑ j, a j • (Pi.single j 1 : Fin n → S') = a := fun a => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hD]
  refine ⟨cc, (comb_iff hx' _ _ _).2 (hs cc).symm, fun a ha => ?_⟩
  exact (hs a).symm.trans ((comb_iff hx' _ _ _).1 ha).symm

end GlobalTheory.LieLocBasis
