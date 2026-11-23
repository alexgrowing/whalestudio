import Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceDegeneracyIdentities

theorem pull_pull {E : Spc} {U : Scheme.{0}} {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (x : Sx E c U) :
    (E.map f.op).app (op U) ((E.map g.op).app (op U) x) = (E.map (f ≫ g).op).app (op U) x := by
  rw [op_comp, E.map_comp]; rfl

theorem pull_congr {E : Spc} {U : Scheme.{0}} {a b : ℕ} {f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b}
    (h : f = g) (x : Sx E b U) : (E.map f.op).app (op U) x = (E.map g.op).app (op U) x := by rw [h]

theorem f0s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 0 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem L_nat {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ} (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (y : Sx E n U) : (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map f.op).app (op U) y) =
      ((ofCat (glCat 1)).map f.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) y) := by
  have h := L.naturality f.op
  have h2 := NatTrans.congr_app h (op U)
  first
  | exact (by simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom h2 y)
  | exact (by simpa only [NatTrans.comp_app, types_comp_apply] using congr_fun h2 y)

theorem line_mul {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (y : Sx E 2 U) :
    lineUnit L (y.face 1) = lineUnit L (y.sub 0 1 (by omega)) * lineUnit L (y.sub 1 1 (by omega)) := by
  unfold lineUnit Sx.face Sx.sub SimplicialObject.δ
  rw [L_nat, L_nat, L_nat]
  generalize (L.app (op (SimplexCategory.mk 2))).app (op U) y = z
  let z' : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := z
  change Matrix.GeneralLinearGroup.det (z'.map' 0 2) = Matrix.GeneralLinearGroup.det (z'.map' 0 1) * Matrix.GeneralLinearGroup.det (z'.map' 1 2)
  rw [z'.map'_comp 0 1 2, SingleObj.comp_as_mul, map_mul, mul_comm]

theorem f0s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 0).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 1 1 (by omega) = x.sub 2 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f1s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 1).sub 0 1 (by omega) = (x.face 3).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f2s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 2).sub 1 1 (by omega) = (x.face 0).face 1 := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull, pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s0 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 0 1 (by omega) = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem f3s1 {E : Spc} {U : Scheme.{0}} (x : Sx E 3 U) : (x.face 3).sub 1 1 (by omega) = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ
  rw [pull_pull]; exact pull_congr (by first | decide | (ext i; fin_cases i <;> rfl)) x

theorem local_zero (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hC : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α) {V : Scheme.{0}}
    (x : Sx E 3 V) (a b c : (Γ(V, ⊤))ˣ) (ha : a ^ q = lineUnit L (x.sub 0 1 (by omega)))
    (hb : b ^ q = lineUnit L (x.sub 1 1 (by omega))) (hc : c ^ q = lineUnit L (x.sub 2 1 (by omega))) :
    ev (δ 2 3 α) 3 0 (by simp) V x = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
    2 (-1) 0 (by norm_num) (by norm_num) x
  refine hd.trans ?_
  have h0 : ev α 3 (-1) (by norm_num) V x = 0 :=
    LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q (-1) (by norm_num)) V _ _
  have v0 := hC.2.2 V (x.face 0) b c (by rw [f0s0]; exact hb) (by rw [f0s1]; exact hc)
  have v1 := hC.2.2 V (x.face 1) (a * b) c (by rw [f1s0, line_mul, f3s0, f3s1, mul_pow, ha, hb]) (by rw [f1s1]; exact hc)
  have v2 := hC.2.2 V (x.face 2) a (b * c) (by rw [f2s0]; exact ha) (by rw [f2s1, line_mul, f0s0, f0s1, mul_pow, hb, hc])
  have v3 := hC.2.2 V (x.face 3) a b (by rw [f3s0]; exact ha) (by rw [f3s1]; exact hb)
  rw [Fin.sum_univ_four]
  erw [h0, v0, v1, v2, v3]
  rw [mul_assoc]
  simp only [Sec.map, map_zero, zero_add]
  convert smul_zero (Int.negOnePow 3) using 2
  simp
  abel

open LateralTheory.EtaleFoundations.FirstChernUniqueness in

theorem etale_kummer_chern_cochain_coboundary_vanishes_on_tetrahedra_of_root_localization (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra := by
  intro q _ E L hi α hC U x
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine loc_imp (loc_and (root_line hr q L hi U (x.sub 0 1 (by omega)))
    (loc_and (root_line hr q L hi U (x.sub 1 1 (by omega))) (root_line hr q L hi U (x.sub 2 1 (by omega)))))
    fun V g hv => ?_
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := hv
  rw [← sub_res] at ha hb hc
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, local_zero q L α hC (x.res g) a b c ha hb hc]
  simp [Sec.res]

end LateralTheory.E.ChernCocycleFaceDegeneracyIdentities
