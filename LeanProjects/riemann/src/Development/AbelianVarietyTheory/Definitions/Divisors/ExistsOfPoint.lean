import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTauLattice
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasTrivialKernelIff
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

structure TautBase (o : Type) [CommRing o] (W : Type) [CommRing W] [IsLocalRing W] where

  b : o →+* W

  B : Over (Sp W)
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B

  g : ℕ
  smoothDim : SmoothOfRelativeDimension g B.hom

  M : RigLB B

  cub : CubicalStr B M
  ample : RelAmple B M.L
  ktriv : KTriv B M.L

  r : ℕ

  c₀ : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ B)
  c₀_add : ∀ a a', c₀ (a + a') = c₀ a * c₀ a'

  τ₀ : ∀ a a' : Fin r → ℤ, LB.Gen (LB.LinComb M.L (lamPts (c₀ a) (c₀ a')) negε)
  τ₀_gen : ∀ a a', (τ₀ a a').IsGen
  τ₀_symm : ∀ a a' z J, Good M.L z J → val (τ₀ a a') (𝟙 _) z J = val (τ₀ a' a) (𝟙 _) z J
  τ₀_add : ∀ a a' a'' z J, Good M.L z J →
    val (τ₀ (a + a') a'') (𝟙 _) z J * cubV cub z J (c₀ a) (c₀ a') (c₀ a'') =
      val (τ₀ a a'') (𝟙 _) z J * val (τ₀ a' a'') (𝟙 _) z J

attribute [instance] TautBase.grp TautBase.comm

open InhTate Inh in

def TautBase.torus {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (b : o →+* W) (r : ℕ)
    (u : Γ((𝟙_ (Over (Sp W))).left, ⊤)ˣ) (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ a a', β a a' = β a' a) :
    TautBase o W where
  b := b
  B := (zeroPolAV (Sp W)).A
  comm := (zeroPolAV (Sp W)).isAb.comm
  isAb := (zeroPolAV (Sp W)).isAb
  g := (zeroPolAV (Sp W)).g
  smoothDim := (zeroPolAV (Sp W)).smoothDim
  M := ⟨(zeroPolAV (Sp W)).L, cg _ _ 1, (zeroPolAV (Sp W)).isLB, cg_isGen _ _ 1⟩
  cub :=
    { t := cg _ _ 1
      isGen := cg_isGen _ _ 1
      face := fun _ => corr_of_isConst ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _)) (isConst_oneGen _)
      cubeSymmetric_swap_first := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cubeSymmetric_swap_last := corr_of_isConst (cg_isConst _ _ 1) ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
      cocycle := corr_of_isConst
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
          ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _))
        ((isConst_mulGen ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))
          ((isConst_pullGen (cg_isConst _ _ 1) _).of_eq (map_one _))).of_eq (_root_.mul_one _)) }
  ample := (zeroPolAV (Sp W)).ample
  ktriv := (zeroPolAV (Sp W)).ktriv
  r := r
  c₀ := fun _ => toUnit _ ≫ η[(zeroPolAV (Sp W)).A]
  c₀_add := fun _ _ => toUnit_unique _ _
  τ₀ a a' := cg _ _ (u ^ β a a')
  τ₀_gen a a' := cg_isGen _ _ _
  τ₀_symm a a' z J hJ := (gm_res _ z _ (hJ.mem _ _) _).trans
    ((congrArg (fun l : ℤ => gm (𝟙 _) z ⊤ (u ^ l)) (hβ a a')).trans (gm_res _ z _ (hJ.mem _ _) _).symm)
  τ₀_add a a' a'' z J hJ := by
    refine (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) ((gm_res _ z _ (hJ.mem _ _) _).trans (map_one _))).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) (gm_res _ z _ (hJ.mem _ _) _) (gm_res _ z _ (hJ.mem _ _) _)).symm)
    rw [_root_.mul_one, ← map_mul, ← zpow_add, map_add, LinearMap.add_apply]

def TautBase.ofPolAV {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (b : o →+* W) (P : PolAV (Sp W))
    [IsCommMonObj P.A] (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen)
    (cub : CubicalStr P.A ⟨P.L, rig, P.isLB, hr⟩) {r : ℕ}
    (c : (Fin r → ℤ) → (𝟙_ (Over (Sp W)) ⟶ P.A)) (hc : ∀ a a', c (a + a') = c a * c a') : TautBase o W :=
  have h := GlobalTheory.TauLocal.exists_tau_local ⟨P.L, rig, P.isLB, hr⟩ cub c hc
  { b := b
    B := P.A
    isAb := P.isAb
    g := P.g
    smoothDim := P.smoothDim
    M := ⟨P.L, rig, P.isLB, hr⟩
    cub := cub
    ample := P.ample
    ktriv := P.ktriv
    r := r
    c₀ := c
    c₀_add := hc
    τ₀ := h.choose
    τ₀_gen := h.choose_spec.1
    τ₀_symm := h.choose_spec.2.1
    τ₀_add := h.choose_spec.2.2 }

theorem TautBase.exists_of_point {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (b : o →+* W) (P : PolAV (Sp W)) (p : 𝟙_ (Over (Sp W)) ⟶ P.A) :
    ∃ (T : TautBase o W) (a : Fin T.r → ℤ), T.B = P.A ∧ T.g = P.g ∧ T.r = 1 ∧ HEq (T.c₀ a) p := by
  obtain ⟨D, α, rfl, h⟩ := GlobalTheory.TwistCompare.exists_degPre P p
  have := D.P.isAb.comm
  refine ⟨TautBase.ofPolAV b D.P D.rig D.rig_gen D.cub (r := 1) (fun a => D.c (a 0 • α))
    (fun a a' => by rw [Pi.add_apply, add_smul, D.c_add]; rfl), fun _ => 1, rfl, rfl, rfl, heq_of_eq ?_⟩
  exact (congrArg D.c (one_smul ℤ α)).trans h

theorem TautBase.exists_ell {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] [IsNoetherianRing W]
    (b : o →+* W) (E : _root_.WeierstrassCurve W) [E.IsElliptic]
    (p : 𝟙_ (Over (Sp W)) ⟶ (GlobalTheory.WeierstrassCurve.ellPolAV E).A) :
    ∃ (T : TautBase o W) (a : Fin T.r → ℤ),
      T.B = (GlobalTheory.WeierstrassCurve.ellPolAV E).A ∧ T.g = 1 ∧ T.r = 1 ∧ HEq (T.c₀ a) p :=
  TautBase.exists_of_point b _ p

theorem TautBase.c₀_zero {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) : T.c₀ 0 = 1 := by
  have h := T.c₀_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

theorem TautBase.c₀_neg {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (a : Fin T.r → ℤ) :
    T.c₀ (-a) = (T.c₀ a)⁻¹ := by
  have h := T.c₀_add (-a) a
  rw [neg_add_cancel, T.c₀_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

example {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (b : o →+* W) (r : ℕ) :
    (TautBase.torus b r 1 0 (fun _ _ => rfl)).r = r := rfl

example : ∃ T : TautBase ℤ ℚ, T.g = 1 ∧ T.r = 1 := by
  let E : _root_.WeierstrassCurve ℚ := ⟨0, 0, 0, 0, 1⟩
  have : E.IsElliptic := ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [E, _root_.WeierstrassCurve.Δ, _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄,
      _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈]⟩
  obtain ⟨T, -, -, h₁, h₂, -⟩ := TautBase.exists_ell (Int.castRingHom ℚ) E 1
  exact ⟨T, h₁, h₂⟩

end GlobalTheory.PolDeg
