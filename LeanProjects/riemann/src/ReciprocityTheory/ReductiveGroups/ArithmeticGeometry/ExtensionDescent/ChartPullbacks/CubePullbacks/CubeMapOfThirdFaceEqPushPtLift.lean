import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi

section Geo

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)

lemma pzero_left {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] (T : Over S₀) :
    (pzero H T).left = T.hom ≫ eSec H := by
  first
    | rfl
    | simp [pzero, eSec]

lemma eSec_hom {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] : eSec H ≫ H.hom = 𝟙 _ := by
  first
    | simp [eSec]
    | (unfold eSec; exact Over.w _)

lemma psum_empty {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀} {n : ℕ}
    (x : Fin n → (T ⟶ H)) : psum H x ∅ = pzero H T := by
  first
    | rfl
    | simp [psum, pzero]

lemma padd_pzero {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (a : T ⟶ H) : padd H a (pzero H T) = a := by
  first
    | simp [padd, pzero]
    | simp [padd]

lemma psum_single {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) (i : Fin 3) : psum H x {i} = x i := by
  fin_cases i <;>
    first
      | exact padd_pzero H _
      | simp [psum, List.finRange, padd_pzero]

lemma cubeMap_lies_over_base : m.F3 ≫ (G3 G).hom = (G3 G').hom ≫ m.e := by
  have h := m.psum_comm ∅
  rw [psum_empty, psum_empty, pzero_left, pzero_left, Category.assoc, m.e_comm] at h
  have h2 := congrArg (· ≫ G.hom) h
  simp only [Category.assoc, eSec_hom, Category.comp_id] at h2
  exact h2.symm

lemma cubeMap_on_coordinates (i : Fin 3) : (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := by
  have h := m.psum_comm {i}
  rwa [psum_single, psum_single] at h

theorem m_over : G'.hom ≫ m.e = m.F ≫ G.hom := by
  have key : (x3 G' 0).left ≫ G'.hom ≫ m.e = (x3 G' 0).left ≫ m.F ≫ G.hom := by
    rw [← Category.assoc, Over.w (x3 G' 0), ← cubeMap_lies_over_base, ← Category.assoc, cubeMap_on_coordinates, Category.assoc,
      Over.w (x3 G 0)]
  have hs : (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G') ≫ x3 G' 0 = 𝟙 G' := by
    simp [x3]
  have hl := congrArg (fun f => f.left) hs
  simp only [Over.comp_left, Over.id_left] at hl
  have h := congrArg (fun f => (lift (𝟙 G') (lift (𝟙 G') (𝟙 G')) : G' ⟶ G3 G').left ≫ f) key
  simp only [← Category.assoc, hl, Category.id_comp] at h
  exact h

def tb {T : Over S'} (y : T ⟶ G') : (Over.map m.e).obj T ⟶ G :=
  Over.homMk (y.left ≫ m.F) (by
    show (y.left ≫ m.F) ≫ G.hom = T.hom ≫ m.e
    rw [Category.assoc, ← m_over, ← Category.assoc, Over.w y])

lemma tb_left {T : Over S'} (y : T ⟶ G') : (tb m y).left = y.left ≫ m.F := rfl

lemma tb_comp {T T' : Over S'} (a : T' ⟶ T) (y : T ⟶ G') :
    tb m (a ≫ y) = (Over.map m.e).map a ≫ tb m y := by
  ext
  simp [tb]

lemma tb_pzero (T : Over S') : tb m (pzero G' T) = pzero G ((Over.map m.e).obj T) := by
  ext
  rw [tb_left, pzero_left, pzero_left, Category.assoc, m.e_comm]
  all_goals first | rfl | simp

lemma psum_01 {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] [IsCommMonObj H] {T : Over S₀}
    (x : Fin 3 → (T ⟶ H)) : psum H x {0, 1} = padd H (x 0) (x 1) := by
  first
    | exact congrArg (padd H (x 0)) (padd_pzero H (x 1))
    | (show padd H (x 0) (padd H (x 1) (pzero H T)) = _; rw [padd_pzero])

lemma comp_padd' {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T)
    (a b : T ⟶ H) : L ≫ padd H a b = padd H (L ≫ a) (L ≫ b) := by
  first
    | (simp only [padd, ← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | (unfold padd; rw [← Category.assoc, CartesianMonoidalCategory.comp_lift])
    | simp [padd]

lemma comp_pzero' {S₀ : Scheme.{0}} (H : Over S₀) [GrpObj H] {T T' : Over S₀} (L : T' ⟶ T) :
    L ≫ pzero H T = pzero H T' := by
  first
    | simp [pzero]
    | (unfold pzero; simp)

def cubeMapOverAlt : (Over.map m.e).obj (G3 G') ⟶ G3 G := Over.homMk m.F3 (cubeMap_lies_over_base m)

abbrev L3 : (Over.map m.e).obj (G3 G') ⟶ G3 G :=
  lift (tb m (x3 G' 0)) (lift (tb m (x3 G' 1)) (tb m (x3 G' 2)))

lemma cubeMapOver_comp_proj (i : Fin 3) : cubeMapOverAlt m ≫ x3 G i = tb m (x3 G' i) := by
  ext
  first
    | simp [cubeMapOverAlt, tb, cubeMap_on_coordinates]
    | (simp only [cubeMapOverAlt, tb, Over.comp_left, Over.homMk_left]; exact (cubeMap_on_coordinates m i).symm)

lemma cubeMapOver_eq_productMap : cubeMapOverAlt m = L3 m := by
  apply CartesianMonoidalCategory.hom_ext
  · simpa [x3] using cubeMapOver_comp_proj m 0
  · apply CartesianMonoidalCategory.hom_ext
    · simpa [x3] using cubeMapOver_comp_proj m 1
    · simpa [x3] using cubeMapOver_comp_proj m 2

lemma cubeMapOf_thirdFace_eq_pushPt_lift : m.F3 = (L3 m).left := by
  rw [← cubeMapOver_eq_productMap]
  rfl

lemma tb_psum3 (I : Finset (Fin 3)) : tb m (psum G' (x3 G') I) = L3 m ≫ psum G (x3 G) I := by
  ext
  rw [tb_left, m.psum_comm, Over.comp_left, ← cubeMapOf_thirdFace_eq_pushPt_lift]

lemma tb_lift3 {T : Over S'} (a b c : T ⟶ G') :
    (Over.map m.e).map (lift a (lift b c)) ≫ L3 m = lift (tb m a) (lift (tb m b) (tb m c)) := by
  simp only [L3, comp_lift, ← tb_comp]
  simp [x3]

lemma tb_padd {T : Over S'} (y z : T ⟶ G') : tb m (padd G' y z) = padd G (tb m y) (tb m z) := by
  ext
  have hw : lift y (lift z y) ≫ padd G' (x3 G' 0) (x3 G' 1) = padd G' y z := by
    simp [comp_padd', x3]
  have h01 := m.psum_comm {0, 1}
  rw [psum_01, psum_01] at h01
  have h3 := congrArg (fun f => f.left) (tb_lift3 m y z y)
  simp only [Over.comp_left, Over.map_map_left] at h3
  rw [tb_left, ← hw, Over.comp_left, Category.assoc, h01, cubeMapOf_thirdFace_eq_pushPt_lift, ← Category.assoc, h3,
    ← Over.comp_left, comp_padd']
  simp [x3]

lemma lift_triple_comm_pullback {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) (p q r : T ⟶ G')
    (p0 q0 r0 : T0 ⟶ G) (hp : tb m p = L ≫ p0) (hq : tb m q = L ≫ q0) (hr : tb m r = L ≫ r0) :
    (lift p (lift q r)).left ≫ m.F3 = L.left ≫ (lift p0 (lift q0 r0)).left := by
  rw [cubeMapOf_thirdFace_eq_pushPt_lift]
  have h := congrArg (fun f => f.left) (tb_lift3 m p q r)
  simp only [Over.comp_left, Over.map_map_left] at h
  rw [h, hp, hq, hr, ← comp_lift, ← comp_lift, Over.comp_left]

abbrev L2 : (Over.map m.e).obj (G2 G') ⟶ G2 G := lift (tb m (x2 G' 0)) (tb m (x2 G' 1))

abbrev L4 : (Over.map m.e).obj (G4 G') ⟶ G4 G :=
  lift (tb m (x4 G' 0)) (lift (tb m (x4 G' 1)) (lift (tb m (x4 G' 2)) (tb m (x4 G' 3))))

def pullbackMapSquare : (G2 G').left ⟶ (G2 G).left := (L2 m).left

def pullbackMapFourth : (G4 G').left ⟶ (G4 G).left := (L4 m).left

lemma pullback_proj_square (j : Fin 2) : tb m (x2 G' j) = L2 m ≫ x2 G j := by
  fin_cases j <;> simp [L2, x2]

lemma pullback_proj_cube (j : Fin 3) : tb m (x3 G' j) = L3 m ≫ x3 G j := by
  rw [← cubeMapOver_eq_productMap, cubeMapOver_comp_proj]

lemma pullback_proj_fourth (j : Fin 4) : tb m (x4 G' j) = L4 m ≫ x4 G j := by
  fin_cases j <;> simp [L4, x4]

lemma tb_pzero' {T : Over S'} {T0 : Over S} (L : (Over.map m.e).obj T ⟶ T0) :
    tb m (pzero G' T) = L ≫ pzero G T0 := by
  rw [tb_pzero, comp_pzero']

theorem face_comm (i : Fin 3) :
    (faceMap G' i).left ≫ m.F3 = pullbackMapSquare m ≫ (faceMap G i).left := by
  fin_cases i
  · have h := lift_triple_comm_pullback m (L2 m) (pzero G' (G2 G')) (x2 G' 0) (x2 G' 1) (pzero G (G2 G)) (x2 G 0) (x2 G 1) (tb_pzero' m (L2 m)) (pullback_proj_square m 0) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (pzero G' (G2 G')) (x2 G' 1) (x2 G 0) (pzero G (G2 G)) (x2 G 1) (pullback_proj_square m 0) (tb_pzero' m (L2 m)) (pullback_proj_square m 1)
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h
  · have h := lift_triple_comm_pullback m (L2 m) (x2 G' 0) (x2 G' 1) (pzero G' (G2 G')) (x2 G 0) (x2 G 1) (pzero G (G2 G)) (pullback_proj_square m 0) (pullback_proj_square m 1) (tb_pzero' m (L2 m))
    first
      | exact h
      | (simp only [faceMap, pullbackMapSquare]; exact h)
      | simpa [faceMap, pullbackMapSquare] using h

theorem swap_first_two_comm :
    (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left ≫ m.F3 =
      m.F3 ≫ (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left := by
  rw [lift_triple_comm_pullback m (L3 m) (x3 G' 1) (x3 G' 0) (x3 G' 2) (x3 G 1) (x3 G 0) (x3 G 2)
    (pullback_proj_cube m 1) (pullback_proj_cube m 0) (pullback_proj_cube m 2), cubeMapOf_thirdFace_eq_pushPt_lift]

theorem swap_last_two_comm :
    (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left ≫ m.F3 =
      m.F3 ≫ (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left := by
  rw [lift_triple_comm_pullback m (L3 m) (x3 G' 0) (x3 G' 2) (x3 G' 1) (x3 G 0) (x3 G 2) (x3 G 1)
    (pullback_proj_cube m 0) (pullback_proj_cube m 2) (pullback_proj_cube m 1), cubeMapOf_thirdFace_eq_pushPt_lift]

theorem cube_face_comm (a b c : Fin 4) :
    (lift (x4 G' a) (lift (x4 G' b) (x4 G' c))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (x4 G b) (x4 G c))).left := by
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) (pullback_proj_fourth m b) (pullback_proj_fourth m c)]

theorem cube_sum_face_comm (a b c d : Fin 4) :
    (lift (padd G' (x4 G' a) (x4 G' b)) (lift (x4 G' c) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (padd G (x4 G a) (x4 G b)) (lift (x4 G c) (x4 G d))).left := by
  have hp : tb m (padd G' (x4 G' a) (x4 G' b)) = L4 m ≫ padd G (x4 G a) (x4 G b) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ hp (pullback_proj_fourth m c) (pullback_proj_fourth m d)]

theorem c4p'_comm (a b c d : Fin 4) :
    (lift (x4 G' a) (lift (padd G' (x4 G' b) (x4 G' c)) (x4 G' d))).left ≫ m.F3 =
      pullbackMapFourth m ≫ (lift (x4 G a) (lift (padd G (x4 G b) (x4 G c)) (x4 G d))).left := by
  have hq : tb m (padd G' (x4 G' b) (x4 G' c)) = L4 m ≫ padd G (x4 G b) (x4 G c) := by
    rw [tb_padd, pullback_proj_fourth, pullback_proj_fourth, comp_padd']
  rw [show pullbackMapFourth m = (L4 m).left from rfl,
    lift_triple_comm_pullback m (L4 m) _ _ _ _ _ _ (pullback_proj_fourth m a) hq (pullback_proj_fourth m d)]

lemma tb_inv {T : Over S'} (y : T ⟶ G') : tb m (y ≫ ι[G']) = tb m y ≫ ι[G] := by
  have hm : ∀ {T0 : Over S} (a b : T0 ⟶ G), padd G a b = pzero G T0 → b = a ≫ ι[G] := by
    intro T0 a b hab
    have h1 : (a ≫ ι[G]) * a = 1 := by
      change lift (a ≫ ι[G]) a ≫ μ = toUnit _ ≫ η
      simp
    have h2 : a * b = 1 := by
      change lift a b ≫ μ = toUnit _ ≫ η
      exact hab
    exact (left_inv_eq_right_inv h1 h2).symm
  apply hm
  rw [← tb_padd, ← tb_pzero]
  congr 1
  simp [padd, pzero]

theorem inv_comm : (GrpObj.inv (X := G')).left ≫ m.F = m.F ≫ (GrpObj.inv (X := G)).left := by
  have h := congrArg (fun f => f.left) (tb_inv m (𝟙 G'))
  simpa [tb_left] using h

end Geo

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
