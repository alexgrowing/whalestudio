import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.Transfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.SubAddEqZeroOfEqAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi

section IdIso

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)

variable {X : Scheme.{0}}

def idIsoL (L : LB X) : LB.Iso L L := ⟨fun p => L.g p.1 p.2⟩

theorem idIsoL_isGen {L : LB X} (hL : L.IsLB) : (idIsoL L).IsGen := by
  rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  apply unit_ext
  intro x hx
  have h11 : x ∈ L.U p₁ := hx.1.1
  have h12 : x ∈ L.U p₂ := hx.1.2
  have h21 : x ∈ L.U q₁ := hx.2.1
  have h22 : x ∈ L.U q₂ := hx.2.2
  rw [map_mul, gU_res, gU_res]
  erw [Transport.gU_div L L (p₁, p₂) (q₁, q₂) x hx.1 hx.2]
  have c1 := Transport.gU_cocycle hL x h11 h21 h22
  have c2 := Transport.gU_cocycle hL x h11 h12 h22
  show gU x (⟨h11, h12⟩ : x ∈ L.U p₁ ⊓ L.U p₂) (L.g p₁ p₂) =
    gU x (⟨h11, h21⟩ : x ∈ L.U p₁ ⊓ L.U q₁) (L.g p₁ q₁) *
      (gU x (⟨h12, h22⟩ : x ∈ L.U p₂ ⊓ L.U q₂) (L.g p₂ q₂))⁻¹ *
      gU x (⟨h21, h22⟩ : x ∈ L.U q₁ ⊓ L.U q₂) (L.g q₁ q₂)
  rw [eq_mul_inv_of_mul_eq c2, ← c1, mul_right_comm]

end IdIso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
  [IsCommMonObj G] (m : CubeMap G' G)

theorem rigPull_eq (L : LB G.left) (r : LB.Gen (L.pull (eSec G))) :
    m.rigPull L r = GeneratorPullback.pullAlong L m.F m.e (fun _ : PUnit => eSec G) (fun _ => 1)
      (fun _ => eSec G') (fun _ => m.e_comm) r := rfl

theorem thetaPull_eq (L : LB G.left) (t : LB.Gen (Theta G L)) :
    m.thetaPull L t = GeneratorPullback.pullAlong L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) t := rfl

theorem hψ2_of {Z W : Scheme.{0}} {a : Z ⟶ (G3 G').left} {h2 : Z ⟶ W} {b : W ⟶ (G3 G).left}
    (hab : a ≫ m.F3 = h2 ≫ b) (k : thK) :
    (a ≫ thφ G' (x3 G') k) ≫ m.F = h2 ≫ (b ≫ thφ G (x3 G) k) := by
  have hp := m.psum_comm k.down
  simp only [thφ] at hp ⊢
  rw [Category.assoc, hp, ← Category.assoc, hab, Category.assoc]

abbrev tP (L : RigLB G) (c : CubicalStr G L) : LB.Gen (LB.LinComb (L.L.pull m.F) (thφ G' (x3 G')) thε) :=
  GeneratorPullback.pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G')) (fun I => m.psum_comm I.down) c.t

set_option maxHeartbeats 800000 in

def cubical (L : RigLB G) (c : CubicalStr G L) (hL : (L.L.pull m.F).IsLB)
    (hr : (m.rigPull L.L L.rig).IsGen) : CubicalStr G' (m.rigLB L hL hr) where
  t := tP m L c
  isGen := LBxP.isGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
    (fun I => m.psum_comm I.down) c.t c.isGen
  face := fun i => by
    refine LBxP.corr_of_eq (LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) c.t (faceMap G' i).left (pullbackMapSquare m) (faceMap G i).left
      (face_comm m i) (fun k => hψ2_of m (face_comm m i) k))
      (LBxP.oneGen_pullAlong L.L m.F (pullbackMapSquare m) (fun k => k.elim)).symm ?_
    exact corr_pullAlong_sameSum L.L L.isLB m.F (pullbackMapSquare m) _ _ _ _ _ _ _ _ _ _
      (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _) (LB.isGen_oneGen (L := L.L)) (c.face i)
      (face_sameSum G' i)
  cubeSymmetric_swap_first := by
    show LB.Gen.Corr (L.L.pull m.F) (thφ G' (x3 G')) thε
      (fun k => (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left ≫ thφ G' (x3 G') k) thε (tP m L c)
      (LB.pullGen (L.L.pull m.F) (thφ G' (x3 G')) thε (tP m L c) (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left)
    refine LBxP.corr_of_eq rfl (LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε
      (thφ G' (x3 G')) (fun I => m.psum_comm I.down) c.t (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left m.F3 (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left (swap_first_two_comm m)
      (fun k => hψ2_of m (swap_first_two_comm m) k)) ?_
    exact corr_pullAlong_sameSum L.L L.isLB m.F m.F3 (thφ G (x3 G)) thε
      (fun k => (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left ≫ thφ G (x3 G) k) thε (thφ G' (x3 G'))
      (fun k => (lift (x3 G' 1) (lift (x3 G' 0) (x3 G' 2))).left ≫ thφ G' (x3 G') k) (fun I => m.psum_comm I.down)
      (fun k => hψ2_of m (swap_first_two_comm m) k) c.t
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 1) (lift (x3 G 0) (x3 G 2))).left) c.isGen
      (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _) c.cubeSymmetric_swap_first (swap_first_two_same_sum G')
  cubeSymmetric_swap_last := by
    show LB.Gen.Corr (L.L.pull m.F) (thφ G' (x3 G')) thε
      (fun k => (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left ≫ thφ G' (x3 G') k) thε (tP m L c)
      (LB.pullGen (L.L.pull m.F) (thφ G' (x3 G')) thε (tP m L c) (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left)
    refine LBxP.corr_of_eq rfl (LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε
      (thφ G' (x3 G')) (fun I => m.psum_comm I.down) c.t (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left m.F3 (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left (swap_last_two_comm m)
      (fun k => hψ2_of m (swap_last_two_comm m) k)) ?_
    exact corr_pullAlong_sameSum L.L L.isLB m.F m.F3 (thφ G (x3 G)) thε
      (fun k => (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left ≫ thφ G (x3 G) k) thε (thφ G' (x3 G'))
      (fun k => (lift (x3 G' 0) (lift (x3 G' 2) (x3 G' 1))).left ≫ thφ G' (x3 G') k) (fun I => m.psum_comm I.down)
      (fun k => hψ2_of m (swap_last_two_comm m) k) c.t
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (x3 G 0) (lift (x3 G 2) (x3 G 1))).left) c.isGen
      (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _) c.cubeSymmetric_swap_last (swap_last_two_same_sum G')
  cocycle := by
    have e1 := LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) c.t
      (lift (padd G' (x4 G' 0) (x4 G' 1)) (lift (x4 G' 2) (x4 G' 3))).left (pullbackMapFourth m)
      (lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3))).left (cube_sum_face_comm m 0 1 2 3)
      (fun k => hψ2_of m (cube_sum_face_comm m 0 1 2 3) k)
    have e2 := LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) c.t
      (lift (x4 G' 0) (lift (x4 G' 1) (x4 G' 3))).left (pullbackMapFourth m)
      (lift (x4 G 0) (lift (x4 G 1) (x4 G 3))).left (cube_face_comm m 0 1 3)
      (fun k => hψ2_of m (cube_face_comm m 0 1 3) k)
    have e3 := LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) c.t
      (lift (x4 G' 0) (lift (padd G' (x4 G' 1) (x4 G' 2)) (x4 G' 3))).left (pullbackMapFourth m)
      (lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3))).left (c4p'_comm m 0 1 2 3)
      (fun k => hψ2_of m (c4p'_comm m 0 1 2 3) k)
    have e4 := LBxP.pullGen_pullAlong L.L m.F m.F3 (thφ G (x3 G)) thε (thφ G' (x3 G'))
      (fun I => m.psum_comm I.down) c.t
      (lift (x4 G' 1) (lift (x4 G' 2) (x4 G' 3))).left (pullbackMapFourth m)
      (lift (x4 G 1) (lift (x4 G 2) (x4 G 3))).left (cube_face_comm m 1 2 3)
      (fun k => hψ2_of m (cube_face_comm m 1 2 3) k)
    have hS1 : ∀ k, Sum.elim
        (fun k => (lift (padd G' (x4 G' 0) (x4 G' 1)) (lift (x4 G' 2) (x4 G' 3))).left ≫
          thφ G' (x3 G') k)
        (fun k => (lift (x4 G' 0) (lift (x4 G' 1) (x4 G' 3))).left ≫ thφ G' (x3 G') k) k ≫ m.F =
        pullbackMapFourth m ≫ Sum.elim
        (fun k => (lift (padd G (x4 G 0) (x4 G 1)) (lift (x4 G 2) (x4 G 3))).left ≫
          thφ G (x3 G) k)
        (fun k => (lift (x4 G 0) (lift (x4 G 1) (x4 G 3))).left ≫ thφ G (x3 G) k) k := by
      rintro (k | k)
      · exact hψ2_of m (cube_sum_face_comm m 0 1 2 3) k
      · exact hψ2_of m (cube_face_comm m 0 1 3) k
    have hS2 : ∀ k, Sum.elim
        (fun k => (lift (x4 G' 0) (lift (padd G' (x4 G' 1) (x4 G' 2)) (x4 G' 3))).left ≫
          thφ G' (x3 G') k)
        (fun k => (lift (x4 G' 1) (lift (x4 G' 2) (x4 G' 3))).left ≫ thφ G' (x3 G') k) k ≫ m.F =
        pullbackMapFourth m ≫ Sum.elim
        (fun k => (lift (x4 G 0) (lift (padd G (x4 G 1) (x4 G 2)) (x4 G 3))).left ≫
          thφ G (x3 G) k)
        (fun k => (lift (x4 G 1) (lift (x4 G 2) (x4 G 3))).left ≫ thφ G (x3 G) k) k := by
      rintro (k | k)
      · exact hψ2_of m (c4p'_comm m 0 1 2 3) k
      · exact hψ2_of m (cube_face_comm m 1 2 3) k
    refine LBxP.corr_of_eq
      ((congrArg₂ (LB.mulGen (L.L.pull m.F) _ _ _ _) e1 e2).trans
        (LBxP.mulGen_pullAlong L.L m.F (pullbackMapFourth m) _ _ _ _ _ _ _ _ hS1 _ _).symm)
      ((congrArg₂ (LB.mulGen (L.L.pull m.F) _ _ _ _) e3 e4).trans
        (LBxP.mulGen_pullAlong L.L m.F (pullbackMapFourth m) _ _ _ _ _ _ _ _ hS2 _ _).symm) ?_
    exact corr_pullAlong_sameSum L.L L.isLB m.F (pullbackMapFourth m) _ _ _ _ _ _ hS1 hS2 _ _
      (LB.isGen_mulGen (L := L.L) _ _ _ _ _ _ (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _)
        (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _))
      (LB.isGen_mulGen (L := L.L) _ _ _ _ _ _ (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _)
        (LB.isGen_pullGen (L := L.L) _ _ _ c.isGen _))
      c.cocycle (cocycle_sameSum G')

end ReciprocityTheory.ChartRestriction.G.Out.CubePf

namespace ReciprocityTheory.ChartRestriction.G.Out.CubePf

open Semi

theorem cubePull : CubePullSt := by
  intro S S' G G' _ _ _ _ m L c
  have hL : (L.L.pull m.F).IsLB := LB.isLB_pull L.isLB m.F
  have hr : (m.rigPull L.L L.rig).IsGen :=
    LBxP.isGen_pullAlong L.L m.F m.e (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec G')
      (fun _ => m.e_comm) L.rig L.rigGen
  refine ⟨hL, hr, ⟨cubical m L c hL hr, ?_⟩, sym_pull m L hL hr⟩
  refine ⟨idIsoL _, idIsoL_isGen hL, fun p => hr p.1 p.2, ?_⟩
  rw [thetaPull_eq]
  exact fun p => (cubical m L c hL hr).isGen p.1 p.2

end ReciprocityTheory.ChartRestriction.G.Out.CubePf
