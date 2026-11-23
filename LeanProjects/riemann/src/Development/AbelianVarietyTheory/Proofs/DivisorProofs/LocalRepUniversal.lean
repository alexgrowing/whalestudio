import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfGroupPullbackDataBase

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pullPull {P X Y : Scheme.{0}} {M : LB P} (hM : M.IsLB) (b : X ⟶ P) (c : Y ⟶ X) :
    LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
  LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))

theorem lbIso_pullAlong {X Y : Scheme.{0}} {P Q : LB X} (H : LBIso P Q) (h : Y ⟶ X) :
    LBIso (P.pull h) (Q.pull h) :=
  LBIso.chartPull (chartPullPull P h h rfl) (chartPullPull Q h h rfl) H

theorem Pt.f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (e : x.t = x'.t) :
    pullback.lift (pullback.fst A.hom x'.t) (pullback.snd A.hom x'.t) (by rw [pullback.condition, e]) ≫ x.f = x'.f := by
  subst h
  rw [pullback.lift_fst_snd, Category.id_comp]

section
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  {V : Scheme.{0}} {j : V ⟶ S} {A' B' : Over V} [GrpObj A'] [GrpObj B'] {φA : A'.left ⟶ A.left}
  {φB : B'.left ⟶ B.left}

theorem univ_iso (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)) :
    LBIso (L.pull (R.φA ≫ φA)) ((M.pull (R.φB ≫ φB)).pull R.Φ.left) :=
  LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (lbIso_pullPull hL φA R.φA).symm
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
      (pull_isLB (pull_isLB hM _) _) R.iso (lbIso_pullAlong (lbIso_pullPull hM φB R.φB) R.Φ.left))

def univPt (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) : Pt A B L M R.H :=
  Pt.ofData (R.π ≫ j) R.AH R.BH (R.φA ≫ φA) (R.φB ≫ φB) R.Φ (R.pbA.comp hA) (R.pbB.comp hB) R.hom
    (univ_iso hL hM R)

theorem univPt_key (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) {Z P : Scheme.{0}} (c : Z ⟶ R.H) (t : Z ⟶ V)
    (e : P ⟶ pullback A.hom (t ≫ j)) (ψ : P ⟶ R.AH.left)
    (h1 : ψ ≫ R.φA ≫ φA = e ≫ pullback.fst _ _) (h2 : ψ ≫ R.AH.hom = e ≫ pullback.snd _ _ ≫ c)
    (w : pullback.fst A.hom (t ≫ j) ≫ A.hom = pullback.snd A.hom (t ≫ j) ≫ c ≫ R.π ≫ j) :
    e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c ≫ (univPt hL hM R hA hB).f =
      ψ ≫ R.Φ.left ≫ R.φB ≫ φB := by
  have hk : e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c =
      ψ ≫ (R.pbA.comp hA).1.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pmap, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      exact h1.symm
    · simp only [pmap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd]
      exact h2.symm
  have e0 : (univPt hL hM R hA hB).f = (R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB := rfl
  have := congrArg (· ≫ ((R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB)) hk
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at this
  rw [e0]
  exact this

end
end GlobalTheory.EndLoc.HomGlue

namespace GlobalTheory.EndLoc.HomGlue

theorem localRep_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A']
    [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)),
    IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧
      ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  intro S A B _ _ L M hL hM V j _ A' B' _ _ φA φB R hA hB
  refine ⟨univPt hL hM R hA hB, rfl, ?_⟩
  rintro Z ⟨t, f, w⟩ b hx
  dsimp only at hx
  subst hx
  have w₀ := w
  obtain ⟨A'', B'', _, _, φ'', ψ'', Φ'', hA'', hB'', hΦ'', hI'', e, e1, e2, e3⟩ := w₀
  let φ'A : A''.left ⟶ A'.left := hA.1.lift φ'' (A''.hom ≫ b) (by rw [hA''.1.w, Category.assoc])
  have fA : φ'A ≫ φA = φ'' := hA.1.lift_fst _ _ _
  have sA : φ'A ≫ A'.hom = A''.hom ≫ b := hA.1.lift_snd _ _ _
  have pA : IsGrpPullback A'' A' b φ'A := hA.cancel (hA''.congr rfl fA.symm) sA
  let φ'B : B''.left ⟶ B'.left := hB.1.lift ψ'' (B''.hom ≫ b) (by rw [hB''.1.w, Category.assoc])
  have fB : φ'B ≫ φB = ψ'' := hB.1.lift_fst _ _ _
  have sB : φ'B ≫ B'.hom = B''.hom ≫ b := hB.1.lift_snd _ _ _
  have pB : IsGrpPullback B'' B' b φ'B := hB.cancel (hB''.congr rfl fB.symm) sB
  have iso' : LBIso ((L.pull φA).pull φ'A) (((M.pull φB).pull φ'B).pull Φ''.left) := by
    have h1 := lbIso_pullPull hL φA φ'A
    rw [fA] at h1
    have h2 := (lbIso_pullAlong (lbIso_pullPull hM φB φ'B) Φ''.left).symm
    rw [fB] at h2
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) hI'' h2)
  obtain ⟨h, ⟨hh, ψA, ψB, qA, qB, gA, gB, qΦ⟩, huniq⟩ := R.rep Z b A'' B'' φ'A φ'B Φ'' pA pB hΦ'' iso'
  have he : e = hA''.1.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [e1, IsPullback.isoPullback_hom_fst]
    · rw [e2, IsPullback.isoPullback_hom_snd]
  have hΦw : Φ''.left ≫ B''.hom = A''.hom := Over.w Φ''
  refine ⟨h, ?_, ?_⟩
  · refine Pt.ext' (show h ≫ R.π ≫ j = b ≫ j by rw [← Category.assoc, hh]) ?_
    have : IsIso e := by rw [he]; infer_instance
    rw [← cancel_epi e, e3]
    refine (univPt_key hL hM R hA hB h b e ψA (by rw [← Category.assoc, gA, fA, e1])
      (by rw [qA.1.w, ← Category.assoc, e2]) _).trans ?_
    rw [← Category.assoc ψA, ← qΦ, Category.assoc, ← Category.assoc ψB, gB, fB]
  · intro c hc
    have ht : c ≫ R.π ≫ j = b ≫ j := congrArg Pt.t hc
    have hcb : c ≫ R.π = b := (cancel_mono j).1 (by rw [Category.assoc]; exact ht)
    have hf := Pt.f_eq hc ht
    let ψA' : A''.left ⟶ R.AH.left := R.pbA.1.lift φ'A (A''.hom ≫ c) (by rw [sA, ← hcb, Category.assoc])
    have kA : ψA' ≫ R.φA = φ'A := R.pbA.1.lift_fst _ _ _
    have kA2 : ψA' ≫ R.AH.hom = A''.hom ≫ c := R.pbA.1.lift_snd _ _ _
    let ψB' : B''.left ⟶ R.BH.left := R.pbB.1.lift φ'B (B''.hom ≫ c) (by rw [sB, ← hcb, Category.assoc])
    have kB : ψB' ≫ R.φB = φ'B := R.pbB.1.lift_fst _ _ _
    have kB2 : ψB' ≫ R.BH.hom = B''.hom ≫ c := R.pbB.1.lift_snd _ _ _
    have key := univPt_key hL hM R hA hB c b e ψA' (by rw [← Category.assoc, kA, fA, e1])
      (by rw [kA2, ← Category.assoc, e2]) (by rw [pullback.condition, ← ht])
    have hΦA : R.Φ.left ≫ R.BH.hom = R.AH.hom := Over.w R.Φ
    apply huniq
    refine ⟨hcb, ψA', ψB', R.pbA.cancel (pA.congr hcb.symm kA.symm) kA2,
      R.pbB.cancel (pB.congr hcb.symm kB.symm) kB2, kA, kB, ?_⟩
    apply R.pbB.1.hom_ext
    · rw [Category.assoc, kB]
      apply hB.1.hom_ext
      · rw [Category.assoc, fB, ← e3, Category.assoc, Category.assoc, ← key]
        exact congrArg (e ≫ ·) hf.symm
      · rw [Category.assoc, sB, ← Category.assoc, hΦw, Category.assoc, Category.assoc, R.pbB.1.w,
          ← Category.assoc R.Φ.left, hΦA, ← Category.assoc, kA2, Category.assoc, hcb]
    · rw [Category.assoc, kB2, ← Category.assoc, hΦw, Category.assoc, hΦA, kA2]

end GlobalTheory.EndLoc.HomGlue
