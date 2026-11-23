import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.CompanionTheory.KummerPrimitive

theorem res_d_neg {R : Type} [CommRing R] (F : Shv R) : (res R F).d (-1) 0 = 0 := by
  have : (res R F).IsStrictlyGE 0 := by
    unfold res
    infer_instance
  exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 (-1) (by omega)).eq_of_src _ _

theorem cechPt_congr {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) {U : Scheme.{0}} {x x' : U ⟶ X}
    {y y' : Fin (k + 1) → (U ⟶ Y)} (h : ∀ i, y i ≫ f = x) (h' : ∀ i, y' i ≫ f = x') (hx : x = x')
    (hy : ∀ i, y i = y' i) : cechPt f k x y h = cechPt f k x' y' h' := by
  subst hx
  obtain rfl := funext hy
  rfl

def pt0 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b : V ⟶ Y) : Sx (cech f) 0 V :=
  cechPt f 0 (b ≫ f) ![b] (by intro i; fin_cases i; rfl)

def pt1 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : Sx (cech f) 1 V :=
  cechPt f 1 (b ≫ f) ![b, c] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm)

def pt2 {Y X : Scheme.{0}} (f : Y ⟶ X) {V : Scheme.{0}} (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    Sx (cech f) 2 V :=
  cechPt f 2 (b ≫ f) ![b, c, e] (by
    intro i; fin_cases i
    · rfl
    · exact h.symm
    · exact (h.trans h').symm)

section Simplices

variable (hC : CechPt) {Y X : Scheme.{0}} (f : Y ⟶ X) {V V' : Scheme.{0}}
include hC

theorem cechPoint_augmentation (b : V ⟶ Y) : Sx.map (cechAug f) (pt0 f b) = b ≫ f :=
  (((hC Y X f 0 V).2.2 _ _ _).1)

theorem cechPoint_restrict (g : V' ⟶ V) (b : V ⟶ Y) : Sx.res g (pt0 f b) = pt0 f (g ≫ b) := by
  refine ((hC Y X f 0 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i; rfl

theorem cechPair_restrict (g : V' ⟶ V) (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : (g ≫ b) ≫ f = (g ≫ c) ≫ f) :
    Sx.res g (pt1 f b c h) = pt1 f (g ≫ b) (g ≫ c) h' := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.1 V' g |>.trans (cechPt_congr _ _ _ _ (Category.assoc _ _ _).symm ?_)
  intro i; fin_cases i <;> rfl

theorem cechPair_face_zero (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 0 = pt0 f c := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i; rfl

theorem cechPair_face_one (b c : V ⟶ Y) (h : b ≫ f = c ≫ f) : (pt1 f b c h).face 1 = pt0 f b := by
  refine ((hC Y X f 1 V).2.2 _ _ _).2.2 0 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i; rfl

theorem cechTriple_face_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 0 = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 0) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 1 = pt1 f b e (h.trans h') := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 1) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_face_two (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) :
    (pt2 f b c e h h').face 2 = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.δ 2) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_zero (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 0 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 0 1 hs = pt1 f b c h := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 0 1 hs) |>.trans (cechPt_congr _ _ _ _ rfl ?_)
  intro i; fin_cases i <;> rfl

theorem cechTriple_subface_one (b c e : V ⟶ Y) (h : b ≫ f = c ≫ f) (h' : c ≫ f = e ≫ f) (hs : 1 + 1 ≤ 2) :
    (pt2 f b c e h h').sub 1 1 hs = pt1 f c e h' := by
  refine ((hC Y X f 2 V).2.2 _ _ _).2.2 1 (SimplexCategory.subinterval 1 1 hs) |>.trans (cechPt_congr _ _ _ _ h ?_)
  intro i; fin_cases i <;> rfl

end Simplices

section Coboundary

variable (hD : EvDel) {R : Type} [CommRing R] {E : Spc} {I : GlobalTheory.EtC.Cx R} (β : Cochain ((chains R).obj E) I 1)
  (U : Scheme.{0})
include hD

theorem del_one (z : Sx E 1 U) : ev (δ 1 2 β) 1 1 (by simp) U z =
    Sec.map (I.d 0 1) (ev β 1 0 (by simp) U z) +
      (ev β 0 1 (by simp) U (z.face 0) - ev β 0 1 (by simp) U (z.face 1)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 0 0 1 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

theorem del_two (z : Sx E 2 U) : ev (δ 1 2 β) 2 0 (by simp) U z =
    Sec.map (I.d (-1) 0) (ev β 2 (-1) (by simp) U z) +
      (ev β 1 0 (by simp) U (z.face 0) - ev β 1 0 (by simp) U (z.face 1) + ev β 1 0 (by simp) U (z.face 2)) := by
  refine ((hD R E I 1 2 (by norm_num) β U).2 1 (-1) 0 (by simp) (by simp) z).trans ?_
  rw [Int.negOnePow_even 2 (by decide), one_smul, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

end Coboundary

theorem main : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.EvDel → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.CechPt →
    CrystallineSemistableComparison.E.FirstChernCoboundary := by
  intro hExt hNat hDel hConc hBasic hCech hC1 q _ X D L hL hInv x hx
  obtain ⟨γ, hγ, hγ0, hγ1, hγ2⟩ := hC1 q (cech D.f) L hInv
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (res _ (tw q 1)) X 2).1 x
  obtain ⟨α, hαc, hαx⟩ := (hConc (ZMod q) (res _ (tw q 1)) X 2 a).2.1 x ha
  have hmk : CohomologyClass.mk (γ - zcomp (Cocycle.ofHom ((chains (ZMod q)).map (cechAug D.f))) α (zero_add 2)) = 0 := by
    rw [CohomologyClass.mk_sub, hγ, ← hx, ← hαx]
    exact sub_self _
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)] at hmk
  obtain ⟨β, hβ⟩ := hmk
  have hv : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) p U),
      ev (δ 1 2 β) p s h U z = ev γ.1 p s h U z - ev α.1 p s h U (Sx.map (cechAug D.f) z) := by
    intro p s h U z
    have e : δ 1 2 β = γ.1 - (Cochain.ofHom ((chains (ZMod q)).map (cechAug D.f))).comp α.1 (zero_add 2) := hβ
    rw [e, ((hExt _ _ _ _ _ _).2 p s h U z).2.1, ((hNat _ _ _ _ α.1 p s h U).2 _ _ z)]
  have hv1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 2 = s) (U : Scheme.{0}) (z : Sx (cech D.f) (p + 1) U),
      ev (δ 1 2 β) (p + 1) s h U z = ev γ.1 (p + 1) s h U z := by
    intro p s h U z
    rw [hv, show ev α.1 (p + 1) s h U (Sx.map (cechAug D.f) z) = 0 from hαc.2 p s h U (Sx.map (cechAug D.f) z), sub_zero]
  refine ⟨a, fun V b => - ev β 0 1 (by simp) V (pt0 D.f b), fun V b c h => ev β 1 0 (by simp) V (pt1 D.f b c h),
    ha, ?_, ?_, ?_, ?_, ?_⟩
  · intro V V' g b
    have e := (hNat _ _ _ _ β 0 1 (by simp) V).1 V' g (pt0 D.f b)
    rw [cechPoint_restrict hCech] at e
    simp only [map_neg]
    exact congrArg Neg.neg e.symm
  · intro V V' g b c h h'
    rw [← (hNat _ _ _ _ β 1 0 (by simp) V).1 V' g (pt1 D.f b c h), cechPair_restrict hCech]
  · intro V b
    have h0 := ((hDel _ _ _ 1 2 (by norm_num) β V).1 (pt0 D.f b))
    rw [hv, hγ0, cechPoint_augmentation hCech, show ev α.1 0 2 (by simp) V (b ≫ D.f) = Sec.res (b ≫ D.f) a from hαc.1 V _, zero_sub] at h0
    simp only [map_neg]
    exact (congrArg Neg.neg h0).symm.trans (neg_neg _)
  · intro V b c h v hv'
    have hu : v ^ q = lineUnit L (pt1 D.f b c h) := hv'.trans (hL V _ ![b, c] _).symm
    have h1 := del_one hDel β V (pt1 D.f b c h)
    rw [hv1 0 1 _ V (pt1 D.f b c h), hγ1 V _ v hu, cechPair_face_zero hCech, cechPair_face_one hCech] at h1
    simp only [map_sub]
    change -ev β 0 1 (by simp) V (pt0 D.f c) - -ev β 0 1 (by simp) V (pt0 D.f b) =
      Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (ev β 1 0 (by simp) V (pt1 D.f b c h)) -
        Sec.map ((res (ZMod q) (tw q 1)).d 0 1) (kumT q V v)
    rw [h1]
    abel
  · intro V b c e h h' v w hv' hw'
    have hu : v ^ q = lineUnit L ((pt2 D.f b c e h h').sub 0 1 (by omega)) := by
      rw [cechTriple_subface_zero hCech]
      exact hv'.trans (hL V _ ![b, c] _).symm
    have hu' : w ^ q = lineUnit L ((pt2 D.f b c e h h').sub 1 1 (by omega)) := by
      rw [cechTriple_subface_one hCech]
      exact hw'.trans (hL V _ ![c, e] _).symm
    have h2 := del_two hDel β V (pt2 D.f b c e h h')
    have hz : ∀ y : Sec ((res (ZMod q) (tw q 1)).X (-1)) V, Sec.map ((res (ZMod q) (tw q 1)).d (-1) 0) y = 0 := by
      intro y
      rw [res_d_neg]
      rfl
    rw [hv1 1 0 _ V (pt2 D.f b c e h h'), hγ2 V _ v w hu hu', cechTriple_face_zero hCech, cechTriple_face_one hCech, cechTriple_face_two hCech,
      hz, zero_add] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.KummerPrimitive
