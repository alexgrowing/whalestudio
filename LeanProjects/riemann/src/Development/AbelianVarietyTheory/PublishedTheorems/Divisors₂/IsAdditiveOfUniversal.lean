import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

variable {S : Scheme.{0}} {A B T Y Z : Over S}

abbrev ev (M : LB (A ⊗ T).left) (a : Y ⟶ A) (t : Y ⟶ T) : LB Y.left := M.pull (lift a t).left

abbrev swap (P : LB (A ⊗ B).left) : LB (B ⊗ A).left := ev P (snd B A) (fst B A)

def evc {M : LB (A ⊗ T).left} (hM : M.IsLB) (a : Y ⟶ A) (t : Y ⟶ T) : Pic Y.left :=
  CechPic.pull (lift a t).left (cls M hM)

theorem cls_ev {M : LB (A ⊗ T).left} (hM : M.IsLB) (a : Y ⟶ A) (t : Y ⟶ T) (h : (ev M a t).IsLB) :
    cls _ h = evc hM a t := rfl

theorem pull_evc {M : LB (A ⊗ T).left} (hM : M.IsLB) (u : Z ⟶ Y) (a : Y ⟶ A) (t : Y ⟶ T) :
    CechPic.pull u.left (evc hM a t) = evc hM (u ≫ a) (u ≫ t) := by
  rw [evc, ← pull_comp, ← Over.comp_left, comp_lift, evc]

theorem triv_ev_iff {M : LB (A ⊗ T).left} (hM : M.IsLB) (a : Y ⟶ A) (t : Y ⟶ T) :
    Triv (ev M a t) ↔ evc hM a t = 0 := (cls_eq_zero_iff (pull_isLB hM _)).symm

theorem evc_ev {M : LB (A ⊗ T).left} (hM : M.IsLB) {A' T' : Over S} (f : A' ⊗ T' ⟶ A) (g : A' ⊗ T' ⟶ T)
    (h : (ev M f g).IsLB) (a : Y ⟶ A') (t : Y ⟶ T') : evc h a t = evc hM (lift a t ≫ f) (lift a t ≫ g) :=
  pull_evc hM _ _ _

theorem evc_swap {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : (swap P).IsLB) (b : Y ⟶ B) (a : Y ⟶ A) :
    evc h b a = evc hP a b := by
  rw [evc_ev hP, lift_fst, lift_snd]

variable [GrpObj A] [GrpObj B]

def IsAdditive (M : LB (A ⊗ T).left) : Prop :=
  ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T), LBIso (ev M (a * a') t) (tens (ev M a t) (ev M a' t))

theorem isAdditive_iff {M : LB (A ⊗ T).left} (hM : M.IsLB) : IsAdditive M ↔
    ∀ (Y : Over S) (a a' : Y ⟶ A) (t : Y ⟶ T), evc hM (a * a') t = evc hM a t + evc hM a' t :=
  forall₄_congr fun _ _ _ _ ↦
    (cls_eq_iff (pull_isLB hM _) (isLB_tens (pull_isLB hM _) (pull_isLB hM _))).symm

theorem isAdditive_of_universal {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : LBIso (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))
      (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
        (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))) : IsAdditive M := by
  refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
  have e := congrArg (CechPic.pull (lift a (lift a' t)).left)
    ((cls_eq_iff (pull_isLB hM _) (isLB_tens (pull_isLB hM _) (pull_isLB hM _))).2 h)
  rw [cls_tens (pull_isLB hM _) (pull_isLB hM _), map_add, cls_ev hM, cls_ev hM, cls_ev hM] at e
  simpa only [pull_evc, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] using e

theorem IsAdditive.evc_one {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    evc hM (1 : Y ⟶ A) t = 0 := by
  have e := (isAdditive_iff hM).1 h Y 1 1 t
  rw [_root_.mul_one] at e
  exact left_eq_add.1 e

variable (A B) in

structure IsDual (P : LB (A ⊗ B).left) : Prop where
  isLB : P.IsLB
  additive : IsAdditive P
  zero : Triv (ev P (𝟙 A) (1 : A ⟶ B))
  univ : ∀ (T : Over S) (M : LB (A ⊗ T).left), M.IsLB → IsAdditive M →
    ∃! x : T ⟶ B, LBIso M (ev P (fst A T) (snd A T ≫ x))

variable (A B) in

structure IsPerfect (P : LB (A ⊗ B).left) : Prop where
  isLB : P.IsLB
  zero_left : Triv (ev P (1 : B ⟶ A) (𝟙 B))
  zero_right : Triv (ev P (𝟙 A) (1 : A ⟶ B))
  ker_left : ∀ (T : Over S) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1
  ker_right : ∀ (T : Over S) (x : T ⟶ B), Triv (ev P (fst A T) (snd A T ≫ x)) → x = 1

theorem evc_one_right {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : Triv (ev P (𝟙 A) (1 : A ⟶ B))) (a : Y ⟶ A) :
    evc hP a (1 : Y ⟶ B) = 0 := by
  have e := congrArg (CechPic.pull a.left) ((triv_ev_iff hP _ _).1 h)
  rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e

theorem evc_one_left {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : Triv (ev P (1 : B ⟶ A) (𝟙 B))) (b : Y ⟶ B) :
    evc hP (1 : Y ⟶ A) b = 0 := by
  have e := congrArg (CechPic.pull b.left) ((triv_ev_iff hP _ _).1 h)
  rwa [pull_evc, map_zero, Category.comp_id, MonObj.comp_one] at e

theorem IsDual.eq_one {P : LB (A ⊗ B).left} (h : IsDual A B P) (x : T ⟶ B)
    (hx : Triv (ev P (fst A T) (snd A T ≫ x))) : x = 1 := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  have e := (triv_ev_iff h.isLB _ _).1 hx
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 ?_)
  · have z : cls _ hM = 0 := e
    simp only [evc, z, map_zero, add_zero]
  · rw [cls_ev h.isLB, cls_ev h.isLB, e, MonObj.comp_one, evc_one_right h.isLB h.zero]

theorem IsDual.isPerfect {P : LB (A ⊗ B).left} (h : IsDual A B P) (h' : IsDual B A (swap P)) :
    IsPerfect A B P where
  isLB := h.isLB
  zero_left := (triv_ev_iff h.isLB _ _).2 (h.additive.evc_one h.isLB _)
  zero_right := h.zero
  ker_left T x hx := h'.eq_one x <| (triv_ev_iff h'.isLB _ _).2 <| by
    have e := congrArg (CechPic.pull (lift (snd B T) (fst B T)).left) ((triv_ev_iff h.isLB _ _).1 hx)
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd, ← evc_swap h.isLB h'.isLB] at e
  ker_right _ := h.eq_one

theorem IsPerfect.swap {P : LB (A ⊗ B).left} (h : IsPerfect A B P) : IsPerfect B A (swap P) := by
  have hs : (AbDual.swap P).IsLB := pull_isLB h.isLB _
  refine ⟨hs, ?_, ?_, fun T x hx ↦ h.ker_right T x ?_, fun T x hx ↦ h.ker_left T x ?_⟩
  · rw [triv_ev_iff hs, evc_swap h.isLB, evc_one_right h.isLB h.zero_right]
  · rw [triv_ev_iff hs, evc_swap h.isLB, evc_one_left h.isLB h.zero_left]
  · have e := congrArg (CechPic.pull (lift (snd A T) (fst A T)).left) ((triv_ev_iff hs _ _).1 hx)
    rwa [pull_evc, map_zero, lift_fst_assoc, lift_snd, evc_swap h.isLB, ← triv_ev_iff] at e
  · have e := congrArg (CechPic.pull (lift (snd T B) (fst T B)).left) ((triv_ev_iff hs _ _).1 hx)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst, evc_swap h.isLB, ← triv_ev_iff] at e

theorem pull_eq_zero_of_mem {X X' : Scheme.{0}} (W : X.Opens) (r : X' ⟶ X) (hr : ∀ z, r z ∈ W) {c : Pic X}
    (h : CechPic.pull W.ι c = 0) : CechPic.pull r c = 0 := by
  rw [← IsOpenImmersion.lift_fac W.ι r (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact hr z),
    pull_comp, h, map_zero]

theorem pull_translDiff {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (x : T ⟶ G)
    (h : (Out.translDiff G L x).IsLB) (t : Y ⟶ T) (u : Y ⟶ G) :
    CechPic.pull (lift t u).left (cls _ h) =
      CechPic.pull ((t ≫ x) * u).left (cls L hL) - CechPic.pull u.left (cls L hL) := by
  have e : cls _ h = CechPic.pull ((fst T G ≫ x) * snd T G).left (cls L hL) -
      CechPic.pull (snd T G).left (cls L hL) := by
    refine (cls_linComb hL _ _ h).trans ?_
    rw [Fin.sum_univ_two, sub_eq_add_neg]
    exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)
  rw [e, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_mul, lift_fst_assoc,
    lift_snd]

theorem pull_mul_eq {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {x : T ⟶ G} {V : T.left.Opens}
    (hc : Triv ((Out.translDiff G L x).pull ((fst T G).left ⁻¹ᵁ V).ι)) (t : Y ⟶ T) (ht : ∀ z, t.left z ∈ V)
    (u : Y ⟶ G) : CechPic.pull ((t ≫ x) * u).left (cls L hL) = CechPic.pull u.left (cls L hL) := by
  have hD : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  have z : CechPic.pull ((fst T G).left ⁻¹ᵁ V).ι (cls _ hD) = 0 := (cls_eq_zero_iff (pull_isLB hD _)).2 hc
  have e : (lift t u).left ≫ (fst T G).left = t.left := by rw [← Over.comp_left, lift_fst]
  rw [← sub_eq_zero, ← pull_translDiff hL x hD]
  exact pull_eq_zero_of_mem _ _ (fun z ↦ (congrArg (fun q ↦ q z ∈ V) e).mpr (ht z)) z

theorem IsPerfect.kTriv {P : LB (A ⊗ B).left} (h : IsPerfect A B P) : Out.KTriv (A ⊗ B) P := by
  intro R _ t x hx
  choose V hV hc using hx
  let j : ∀ p, Over.mk ((V p).ι ≫ t) ⟶ Over.mk t := fun p ↦ Over.homMk (V p).ι rfl
  have key : ∀ p (Y : Over S) (s : Y ⟶ Over.mk ((V p).ι ≫ t)) (a : Y ⟶ A) (b : Y ⟶ B),
      evc h.isLB ((s ≫ j p ≫ x ≫ fst A B) * a) ((s ≫ j p ≫ x ≫ snd A B) * b) = evc h.isLB a b := by
    intro p Y s a b
    refine Eq.trans (congrArg (fun q : Y ⟶ A ⊗ B ↦ CechPic.pull q.left (cls P h.isLB)) ?_)
      (pull_mul_eq h.isLB (hc p) (s ≫ j p) (fun z ↦ (s.left z).2) (lift a b))
    ext <;> simp [MonObj.mul_comp]
  have k : ∀ p, j p ≫ x = 1 := fun p ↦ by
    have ka : j p ≫ x ≫ fst A B = 1 := h.ker_left _ _ <| (triv_ev_iff h.isLB _ _).2 <| by
      have e := key p _ (fst _ B) 1 ((fst _ B ≫ j p ≫ x ≫ snd A B)⁻¹ * snd _ B)
      rwa [_root_.mul_one, mul_inv_cancel_left, evc_one_left h.isLB h.zero_left] at e
    have kb : j p ≫ x ≫ snd A B = 1 := h.ker_right _ _ <| (triv_ev_iff h.isLB _ _).2 <| by
      have e := key p _ (snd A _) ((snd A _ ≫ j p ≫ x ≫ fst A B)⁻¹ * fst A _) 1
      rwa [_root_.mul_one, mul_inv_cancel_left, evc_one_right h.isLB h.zero_right] at e
    ext
    · rw [Category.assoc, ka, MonObj.one_comp]
    · rw [Category.assoc, kb, MonObj.one_comp]
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun p ↦ ⟨V p, hV p, ?_⟩)
  have e : j p ≫ x = j p ≫ 1 := (k p).trans (MonObj.comp_one _).symm
  exact congrArg (fun q ↦ q.left) e

theorem triv_pull_of_mem {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : X' ⟶ X) {i : L.ι}
    (hi : ∀ y, f y ∈ L.U i) : Triv (L.pull f) := by
  have le : ∀ j, (L.pull f).U j ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U i) := fun j y hy ↦ ⟨mem_pull.1 hy, hi y⟩
  refine ⟨⟨fun j ↦ res (le j) (pullU f _ (L.g (j PUnit.unit) i))⟩, (isGen_iff_germ _).2 fun y j j' hj hj' ↦ ?_⟩
  have k : ∀ j, y ∈ (L.pull f).U j → gm (𝟙 X') y _ (res (le j) (pullU f _ (L.g (j PUnit.unit) i))) =
      gm (𝟙 X' ≫ f) y _ (L.g (j PUnit.unit) i) := fun j hj ↦
    (gm_res (𝟙 X') y (le j) hj _).trans (gm_pull (𝟙 X') f y _ (le j hj) _)
  refine (k j hj).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_pull_g L f (𝟙 X') y j j' hj hj') (k j' hj')).symm)
  exact (gm_cocycle hL (𝟙 X' ≫ f) y (mem_pull.1 hj) (mem_pull.1 hj') (hi y)).symm

theorem exists_pull_eq_zero {X : Scheme.{0}} (c : Pic X) (p : X) :
    ∃ V : X.Opens, p ∈ V ∧ CechPic.pull V.ι c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨i, hi⟩ := exists_chart hL p
  exact ⟨L.U i, hi, (cls_eq_zero_iff (pull_isLB hL _)).2 (triv_pull_of_mem hL _ fun y ↦ y.2)⟩

theorem isPerfect_lam [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (hK : Out.KTriv A L) :
    IsPerfect A A (abelian₂ A L) := by
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have k : ∀ (T : Over S) (x : T ⟶ A), lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 → x = 1 := fun T x hx ↦ by
    have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
    obtain ⟨z, rfl⟩ := (memKL_iff_of_kTriv hL hK x).1 fun p ↦ by
      obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
        (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
      refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
      have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
      rw [lift_fst_snd, Over.id_left, pull_id] at e₁
      have e₂ : cls _ hD = CechPic.pull (fst T A).left
          (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
        rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
          ← sub_eq_zero, ← hx, lam]
        abel
      rw [cls_pull hD, e₂, ← pull_comp]
      exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc
    rw [toUnit_unique z (toUnit T)]
    rfl
  refine ⟨hP, ?_, ?_, fun T x hx ↦ k T x ?_, fun T x hx ↦ k T x ?_⟩
  · rw [triv_ev_iff hP, e, lam_one_left]
  · rw [triv_ev_iff hP, e, lam_one_right]
  · rwa [triv_ev_iff hP, e] at hx
  · have e' := congrArg (CechPic.pull (lift (snd T A) (fst T A)).left) ((triv_ev_iff hP _ _).1 hx)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst, e, lam_comm] at e'

theorem isPerfect_ell {R : Type} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    haveI := (WeierstrassCurve.ellPolAV W).isAb.comm
    IsPerfect (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).A
      (abelian₂ _ (WeierstrassCurve.ellPolAV W).L) :=
  haveI := (WeierstrassCurve.ellPolAV W).isAb.comm
  isPerfect_lam (WeierstrassCurve.ellPolAV W).isLB (WeierstrassCurve.ellPolAV W).ktriv

theorem isDual_unit : IsDual (𝟙_ (Over S)) (𝟙_ (Over S)) (LB.triv _) := by
  have h0 : ∀ (Y : Over S) (a b : Y ⟶ 𝟙_ (Over S)), evc (LB.isLB_triv _) a b = 0 := fun _ _ _ ↦ map_zero _
  refine ⟨LB.isLB_triv _, (isAdditive_iff (LB.isLB_triv _)).2 fun _ _ _ _ ↦ by simp only [h0, add_zero],
    (triv_ev_iff (LB.isLB_triv _) _ _).2 (h0 _ _ _), fun T M hM ha ↦ ⟨toUnit T, ?_, fun _ _ ↦ toUnit_unique _ _⟩⟩
  refine (cls_eq_iff hM (pull_isLB (LB.isLB_triv _) _)).1 ?_
  have e := ha.evc_one hM (snd (𝟙_ (Over S)) T)
  rw [toUnit_unique 1 (fst _ T), evc, lift_fst_snd, Over.id_left, pull_id] at e
  rw [e, cls_ev (LB.isLB_triv _), h0]

end GlobalTheory.AbDual
