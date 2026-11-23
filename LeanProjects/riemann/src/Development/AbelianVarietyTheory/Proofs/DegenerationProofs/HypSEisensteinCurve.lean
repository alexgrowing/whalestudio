import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEisensteinCurve
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.CubeRootAut

open GlobalTheory.CechPic GlobalTheory.TripleProd GlobalTheory.WeierstrassCurve GlobalTheory.CMCurve GlobalTheory.AddLaw

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cubeCls_pair {T : Over S} (x y : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y] c = pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem cubeCls_triple {T : Over S} (x y z : T ⟶ G) (c : CechPic.Pic G.left) :
    cubeCls ![x, y, z] c = pull (x * y * z).left c - pull (x * y).left c - pull (x * z).left c -
      pull (y * z).left c + pull x.left c + pull y.left c + pull z.left c - pull (1 : T ⟶ G).left c := by
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 3)) ≃ Finset (Fin 3)) _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, y, z] I).left c) fun _ => rfl).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have p₀ : psum G ![x, y, z] ∅ = 1 := rfl
  have p₁ : psum G ![x, y, z] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y, z] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y, z] {2} = z := _root_.mul_one z
  have p₄ : psum G ![x, y, z] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₅ : psum G ![x, y, z] {0, 2} = x * z := congrArg (x * ·) (_root_.mul_one z)
  have p₆ : psum G ![x, y, z] {1, 2} = y * z := congrArg (y * ·) (_root_.mul_one z)
  have p₇ : psum G ![x, y, z] {0, 1, 2} = x * y * z :=
    (congrArg (fun w => x * (y * w)) (_root_.mul_one z)).trans (_root_.mul_assoc x y z).symm
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇]
  have c₁ : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c₂ : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₃ : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c₄ : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  simp only [c₁, c₂, c₃, c₄, Finset.card_singleton, Finset.card_empty]
  norm_num
  abel

theorem hypS_of_invariant {L : LB G.left} (hL : L.IsLB) (h0 : Rigidified G L)
    (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (w wd : G ⟶ G) [IsMonHom w] [IsMonHom wd]
    (hsum : w * wd = 𝟙 G) (hcomp : wd ≫ w = 𝟙 G) (hw : pull w.left (cls L hL) = cls L hL)
    (hι : pull (ι[G]).left (cls L hL) = cls L hL) : HypS G L := by
  have qw : ∀ {T : Over S} (x : T ⟶ G), pull (x ≫ w).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [Over.comp_left, pull_comp, hw]
  have qwd : ∀ {T : Over S} (x : T ⟶ G), pull (x ≫ wd).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [← qw, Category.assoc, hcomp, Category.comp_id]
  have qι : ∀ {T : Over S} (x : T ⟶ G), pull (x⁻¹).left (cls L hL) = pull x.left (cls L hL) := fun x => by
    rw [Hom.inv_def, Over.comp_left, pull_comp, hι]
  have q1 : ∀ T : Over S, pull (1 : T ⟶ G).left (cls L hL) = 0 := fun T => by
    have e : pull (η[G]).left (cls L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 h0
    rw [Hom.one_def, Over.comp_left, pull_comp, e, map_zero]
  have qid : pull (𝟙 G : G ⟶ G).left (cls L hL) = cls L hL := pull_id _
  have hwd : pull wd.left (cls L hL) = cls L hL := by
    have := qwd (𝟙 G)
    rwa [Category.id_comp, qid] at this
  have cube : cubeCls ![𝟙 G, w, w⁻¹] (cls L hL) = 0 := by
    have h : cubeCls (x3 G) (cls L hL) = 0 := (cls_cubeLB _ hL).symm.trans ((cls_eq_zero_iff _).2 hΘ)
    rw [pull_cubeCls (lift (𝟙 G) (lift w w⁻¹)) (x3 G) _ _ (fun i => by fin_cases i <;> simp [x3]), h, map_zero]
  have e₁ : 𝟙 G * w⁻¹ = wd := by rw [← hsum, _root_.mul_comm w wd, mul_inv_cancel_right]
  rw [cubeCls_triple, mul_inv_cancel_right, e₁, mul_inv_cancel, q1, qι, qid, hw, hwd] at cube
  refine ⟨w, wd, inferInstance, inferInstance, hsum, (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 ?_,
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1 ?_⟩
  · refine Eq.trans ?_ (cls_cubeLB _ hL).symm
    rw [cubeCls_pair, q1, qid, hw]
    refine sub_eq_zero.1 (Eq.trans ?_ cube)
    abel
  · refine (cls_cubeLB _ hL).trans (Eq.trans ?_ (cls_cubeLB _ hL).symm)
    have e₂ : (fst G G * (snd G G ≫ wd)) ≫ w = (fst G G ≫ w) * snd G G := by
      rw [MonObj.mul_comp, Category.assoc, hcomp, Category.comp_id]
    rw [cubeCls_pair, cubeCls_pair, ← e₂, qw, qw, qwd]

end General

theorem pull_cls_originLB {R : Type} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic]
    (u : schemeOver W ⟶ schemeOver W) [IsIso u] (hu : η[schemeOver W] ≫ u = η[schemeOver W]) :
    pull u.left (cls (originLB W) (originLB_isLB W)) = cls (originLB W) (originLB_isLB W) := by
  have : IsIso u.left := inferInstanceAs (IsIso ((Over.forget _).map u))
  have hreg := fun i V h => ((isRegularSec_originSec W i).resG (V := V) h).mem
  have key := SameZeroScheme.exists_isGen_linComb (schemeOver W).left _ (originLB W) (originSec W) u.left (𝟙 _)
    (originLB_isLB W)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) (by
      intro T t i j h h'
      rw [appLE_originSec_eq_zero_iff_eSec, appLE_originSec_eq_zero_iff_eSec, Category.comp_id]
      have h1 : u.left ≫ (schemeOver W).hom = (schemeOver W).hom := Over.w _
      have h2 : eSec (schemeOver W) ≫ u.left = eSec (schemeOver W) := congrArg (·.left) hu
      have h3 : (t ≫ u.left) ≫ (schemeOver W).hom ≫ eSec (schemeOver W) =
          (t ≫ (schemeOver W).hom ≫ eSec (schemeOver W)) ≫ u.left := by
        rw [Category.assoc, reassoc_of% h1]
        simp only [Category.assoc]
        exact congrArg (fun v => t ≫ (schemeOver W).hom ≫ v) h2.symm
      rw [h3]
      exact cancel_mono _)
  have e := (cls_linComb (originLB_isLB W) _ _ _).symm.trans
    ((cls_eq_zero_iff (LB.isLB_linComb (originLB_isLB W) _ _)).2 key)
  rw [Fin.sum_univ_two] at e
  have e' : (1 : ℤ) • pull u.left (cls (originLB W) (originLB_isLB W)) +
      (-1 : ℤ) • pull (𝟙 (schemeOver W).left) (cls (originLB W) (originLB_isLB W)) = 0 := e
  rwa [pull_id, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at e'

theorem hypS_eisensteinCurve (hC : CubeSt) {R : Type} [CommRing R] [IsNoetherianRing R] {ω : R}
    (hω : ω ^ 2 + ω + 1 = 0) [(eisensteinCurve R).IsElliptic] :
    HypS (ellPolAV (eisensteinCurve R)).A (ellPolAV (eisensteinCurve R)).L := by
  let P := ellPolAV (eisensteinCurve R)
  obtain ⟨r, hr⟩ := P.rigid
  obtain ⟨⟨cub⟩, -⟩ := hC _ P ⟨P.L, r, P.isLB, hr⟩ rfl
  let φ : P.A ⟶ P.A := eisensteinAut hω
  have : IsMonHom φ := isMonHom_eisensteinAut hω
  have h₂ : (φ ≫ φ) * φ * 𝟙 _ = 1 := eisensteinAut_sq hω
  have h₃ : φ ≫ φ ≫ φ = 𝟙 _ := by
    have h := congrArg (φ ≫ ·) h₂
    simp only [MonObj.comp_mul, MonObj.comp_one, Category.comp_id] at h
    rw [_root_.mul_comm] at h₂
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel (h.trans h₂.symm)
  have : IsIso φ := ⟨φ ≫ φ, h₃, (Category.assoc _ _ _).trans h₃⟩
  have hφ : pull φ.left (cls P.L P.isLB) = cls P.L P.isLB :=
    @pull_cls_originLB _ _ (eisensteinCurve R) _ φ ‹IsIso φ› (IsMonHom.one_hom φ)
  have hι : pull (ι[P.A]).left (cls P.L P.isLB) = cls P.L P.isLB :=
    pull_cls_originLB (eisensteinCurve R) ι[schemeOver _] GrpObj.one_inv
  refine hypS_of_invariant P.isLB P.rigid ⟨cub.t, cub.isGen⟩ (φ ≫ ι[P.A]) ((φ ≫ φ) ≫ ι[P.A]) ?_ ?_ ?_ hι
  · rw [← Hom.inv_def, ← Hom.inv_def, ← mul_inv_rev, inv_eq_iff_mul_eq_one, h₂]
  · rw [← Hom.inv_def, ← Hom.inv_def, GrpObj.comp_inv, GrpObj.inv_comp, inv_inv, Category.assoc, h₃]
  · rw [Over.comp_left, pull_comp, hι, hφ]

theorem exists_hypS : Laws → ∀ (K : Type) [Field K] [CharZero K] (ω : K), ω ^ 2 + ω + 1 = 0 →
    ∃ P : PolAV (Sp K), P.g = 1 ∧ HypS P.A P.L := by
  intro hL K _ _ ω hω
  have := isElliptic_eisensteinCurve (R := K) (Ne.isUnit three_ne_zero)
  exact ⟨ellPolAV (eisensteinCurve K), rfl, hypS_eisensteinCurve hL.cube hω⟩

end GlobalTheory.ZH.CubeRootAut
