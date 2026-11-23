import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.NormIso

theorem prod_zpow_eq_one {K U : Type} [Fintype K] [CommGroup U] (ε : K → ℤ) (hε : ∑ k, ε k = 0) (c : U) :
    ∏ k, c ^ ε k = 1 := by
  have h : ∀ s : Finset K, ∏ k ∈ s, c ^ ε k = c ^ (∑ k ∈ s, ε k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  rw [h, hε, zpow_zero]

theorem gm_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (ε : K → ℤ) (hε : ∑ k, ε k = 0)
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a a' : M.ι)
    (ha : r y ∈ LB.wchart M φ (fun _ => a)) (ha' : r y ∈ LB.wchart M φ (fun _ => a')) :
    gm r y (LB.wchart M φ (fun _ => a) ⊓ LB.wchart M φ (fun _ => a'))
      ((LB.LinComb M φ ε).g (fun _ => a) (fun _ => a')) = 1 :=
  (gm_linComb M φ ε r y _ _ ha ha').trans ((Finset.prod_congr rfl fun k _ => by rw [hq k]).trans
    (prod_zpow_eq_one ε hε (gm q y (M.U a ⊓ M.U a') (M.g a a'))))

theorem mem_const {B X Y : Scheme.{0}} (M : LB B) {K : Type} [Fintype K] (φ : K → (X ⟶ B))
    (r : Y ⟶ X) (q : Y ⟶ B) (hq : ∀ k, r ≫ φ k = q) (y : Y) (a : M.ι) (ha : q y ∈ M.U a) :
    r y ∈ LB.wchart M φ (fun _ => a) :=
  Set.mem_iInter.2 fun k => show (r ≫ φ k) y ∈ M.U a by rw [hq k]; exact ha

theorem exists_normalised {S X X' B B' : Scheme.{0}} (M : LB B) (M' : LB B') (hM : M.IsLB) (hM' : M'.IsLB)
    {K : Type} [Fintype K] (φ : K → (X ⟶ B)) (φ' : K → (X' ⟶ B')) (ε : K → ℤ) (hε : ∑ k, ε k = 0) (F : X' ⟶ X)
    (e : S ⟶ X') (π : X' ⟶ S) (he : e ≫ π = 𝟙 S) (q : S ⟶ B) (q' : S ⟶ B') (hq : ∀ k, (e ≫ F) ≫ φ k = q)
    (hq' : ∀ k, e ≫ φ' k = q') (w₀ : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso (LB.LinComb M' φ' ε) ((LB.LinComb M φ ε).pull F), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (t : Z ⟶ S) (z : Z) (a : M.ι) (b : M'.ι), q (t z) ∈ M.U a → q' (t z) ∈ M'.U b →
        gw w (t ≫ e) z (fun _ => a) (fun _ => b) = 1 := by
  let C : M.ι × M'.ι → X'.Opens := fun i =>
    ((LB.LinComb M φ ε).pull F).U (fun _ _ => i.1) ⊓ (LB.LinComb M' φ' ε).U (fun _ => i.2)
  have mem : ∀ (x : S) (a : M.ι) (b : M'.ι), q x ∈ M.U a → q' x ∈ M'.U b → e x ∈ C (a, b) := fun x a b ha hb =>
    ⟨mem_pull.2 (mem_const M φ (e ≫ F) q hq x a ha), mem_const M' φ' e q' hq' x b hb⟩
  obtain ⟨u, hu⟩ := glue_unit (⊤ : S.Opens) (fun i => e ⁻¹ᵁ C i) (fun _ => le_top) (fun x _ => by
      obtain ⟨a, ha⟩ := exists_chart hM (q x)
      obtain ⟨b, hb⟩ := exists_chart hM' (q' x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(a, b), mem x a b ha hb⟩)
    (fun i => pullU e (C i) (w₀.s (fun _ _ => i.1, fun _ => i.2))) (fun i j x hx => by
      have hi : e x ∈ C i := hx.1
      have hj : e x ∈ C j := hx.2
      refine (gm_pull (𝟙 S) e x (C i) hi _).trans (Eq.trans ?_ (gm_pull (𝟙 S) e x (C j) hj _).symm)
      rw [Category.id_comp]
      have h := (isGen_iff w₀).1 hw S e x (fun _ => i.1) (fun _ => j.1) (fun _ => i.2) (fun _ => j.2)
        (mem_pull.1 hi.1) (mem_pull.1 hj.1) hi.2 hj.2
      refine h.trans ((congrArg (· * _) ((congrArg₂ (fun s t => s * t⁻¹)
        (gm_const M φ ε hε (e ≫ F) q hq x i.1 j.1 (mem_pull.1 hi.1) (mem_pull.1 hj.1))
        (gm_const M' φ' ε hε e q' hq' x i.2 j.2 hi.2 hj.2)).trans (mul_inv_cancel 1))).trans (_root_.one_mul _)))
  let c : Γ(X', ⊤)ˣ := res (fun _ _ => trivial : (⊤ : X'.Opens) ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ u⁻¹)
  refine ⟨DVR.scaleGen c w₀, DVR.scaleGen_isGen c w₀ hw, fun Z t z a b ha hb => ?_⟩
  have hm : e (t z) ∈ C (a, b) := mem (t z) a b ha hb
  have h₁ : gm (t ≫ e) z (C (a, b)) (res le_top c) = (gm t z ⊤ u)⁻¹ := by
    refine (gm_res (t ≫ e) z le_top hm c).trans ((gm_res (t ≫ e) z (V := ⊤) _ trivial _).trans
      ((gm_pull (t ≫ e) π z ⊤ trivial _).trans ?_))
    rw [Category.assoc, he, Category.comp_id, map_inv]
  have h₂ : gm (t ≫ e) z (C (a, b)) (w₀.s (fun _ _ => a, fun _ => b)) = gm t z ⊤ u :=
    (gm_pull t e z (C (a, b)) hm _).symm.trans ((congrArg (gm t z (e ⁻¹ᵁ C (a, b))) (hu (a, b)).symm).trans
      (gm_res t z le_top hm u))
  exact (map_mul (gm (t ≫ e) z (C (a, b))) _ _).trans ((congrArg₂ (· * ·) h₁ h₂).trans (inv_mul_cancel _))

theorem lift_one_psum {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) 1 ≫ psum G (x2 G) I = 1 := by
  have h : (fun k => lift (1 : T ⟶ G) 1 ≫ x2 G k) = fun _ => 1 := by
    funext k
    fin_cases k
    · exact lift_fst _ _
    · exact lift_snd _ _
  rw [comp_psum, h, psum_one]

theorem origin_square {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {β : G'.left ⟶ G.left} {β₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (T : Over S') :
    (lift (1 : T ⟶ G') 1).left ≫ β₂ = (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left := by
  have h₁ : (1 : T ⟶ G').left ≫ β = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  have a₁ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.1, ← Category.assoc, ← Over.comp_left, lift_fst, h₁]
  have a₂ : ((lift (1 : T ⟶ G') 1).left ≫ β₂) ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
    rw [Category.assoc, hs.2, ← Category.assoc, ← Over.comp_left, lift_snd, h₁]
  have b₁ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (fst G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_fst (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  have b₂ : (lift (1 : Over.mk (T.hom ≫ f) ⟶ G) 1).left ≫ (snd G G).left = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (lift_snd (1 : Over.mk (T.hom ≫ f) ⟶ G) (1 : Over.mk (T.hom ≫ f) ⟶ G))
  exact pullback.hom_ext (a₁.trans b₁.symm) (a₂.trans b₂.symm)

theorem exists_lamVal_origin {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} {β₂ : (G2 G').left ⟶ (G2 G).left} {M : LB G.left}
    {M' : LB G'.left} (hM : M.IsLB) (hM' : M'.IsLB) (h : IsGrpPullback G' G f β) (hs : IsSquare β β₂)
    (H : LBIso (abelian₂ G' M') ((abelian₂ G M).pull β₂)) :
    ∃ w : LB.Iso (abelian₂ G' M') ((abelian₂ G M).pull β₂), w.IsGen ∧ ∀ (T : Over S') z J J', Good M z J → Good M' z J' →
      lamVal w (lift (1 : T ⟶ G') (1 : T ⟶ G')).left z J J' = 1 := by
  obtain ⟨w₀, hw₀⟩ := H
  let e : (𝟙_ (Over S')).left ⟶ (G2 G').left := (lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
  let q : (𝟙_ (Over S')).left ⟶ G.left := (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left
  let q' : (𝟙_ (Over S')).left ⟶ G'.left := (1 : 𝟙_ (Over S') ⟶ G').left
  have hq : ∀ I : ULift.{0} (Finset (Fin 2)), (e ≫ β₂) ≫ (psum G (x2 G) I.down).left = q := fun I =>
    (congrArg (· ≫ (psum G (x2 G) I.down).left) (origin_square h hs (𝟙_ (Over S')))).trans
      (congrArg (fun z => z.left) (lift_one_psum G (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) I.down))
  have hq' : ∀ I : ULift.{0} (Finset (Fin 2)), e ≫ (psum G' (x2 G') I.down).left = q' := fun I =>
    congrArg (fun z => z.left) (lift_one_psum G' (T := 𝟙_ (Over S')) I.down)
  obtain ⟨w, hw, hv⟩ := exists_normalised M M' hM hM' (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum G (x2 G) I.down).left) (fun I => (psum G' (x2 G') I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (by decide) β₂ e (toUnit (G2 G')).left
    (congrArg (fun z => z.left) (toUnit_unique (lift (1 : 𝟙_ (Over S') ⟶ G') 1 ≫ toUnit (G2 G')) (𝟙 _))) q q' hq hq'
    w₀ hw₀
  refine ⟨w, hw, fun T z J J' hJ hJ' => ?_⟩
  have hp : (lift (1 : T ⟶ G') (1 : T ⟶ G')).left = (toUnit T).left ≫ e := by
    show _ = (toUnit T ≫ lift (1 : 𝟙_ (Over S') ⟶ G') 1).left
    rw [comp_lift, MonObj.comp_one]
  have key : ∀ (p : T.left ⟶ (G2 G').left) (j : (abelian₂ G M).ι) (k : (abelian₂ G' M').ι),
      (fun I : ULift.{0} (Finset (Fin 2)) => J (p ≫ β₂ ≫ (psum G (x2 G) I.down).left)) = j →
      (fun I : ULift.{0} (Finset (Fin 2)) => J' (p ≫ (psum G' (x2 G') I.down).left)) = k →
      lamVal w p z J J' = gw (L := abelian₂ G M) (L' := abelian₂ G' M') w p z j k := by
    rintro p _ _ rfl rfl
    rfl
  rw [hp]
  refine (key _ (fun _ => J ((toUnit T).left ≫ q)) (fun _ => J' ((toUnit T).left ≫ q')) (funext fun I => ?_)
    (funext fun I => ?_)).trans (hv T.left (toUnit T).left z _ _ (hJ ((toUnit T).left ≫ q)) (hJ' ((toUnit T).left ≫ q')))
  · rw [← hq I, Category.assoc, Category.assoc]
  · rw [← hq' I, Category.assoc]

theorem exists_normalised_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (P : PolAV (Sp R')) (β : P.A.left ⟶ Q.B.left) (β₂ : (G2 P.A).left ⟶ (G2 Q.B).left), IsGrpPullback P.A Q.B (spMap ρ) β → IsSquare β β₂ → (letI := P.isAb.comm; LBIso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂)) → letI := P.isAb.comm; ∃ w : LB.Iso (abelian₂ P.A P.L) ((abelian₂ Q.B Q.M.L).pull β₂), w.IsGen ∧ ∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good P.L z J' → lamVal w (lift (1 : T ⟶ P.A) (1 : T ⟶ P.A)).left z J J' = 1 :=
  fun _ _ _ _ _ _ Q _ P _ _ hpb hs H =>
    letI := P.isAb.comm
    exists_lamVal_origin Q.M.isLB P.isLB hpb hs H

end GlobalTheory.PolDeg.NormIso
