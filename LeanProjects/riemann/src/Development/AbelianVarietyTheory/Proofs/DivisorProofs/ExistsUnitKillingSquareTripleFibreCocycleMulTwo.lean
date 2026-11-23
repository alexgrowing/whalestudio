import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulIncl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFiniteCommGroupSchemeCoboundaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleFiberProductOverMulTwoIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseGlobalUnitAbelianSchemeBaseChangeStatement

set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

namespace GlobalTheory.TwoTors

theorem sq_symm_of_cocycle {G M : Type} [CommGroup G] [CommGroup M] (c : G → G → M)
    (hc : ∀ x y z, c x y * c (x * y) z = c y z * c x (y * z)) (h2 : ∀ x : G, x ^ 2 = 1) (x y : G) :
    c x y ^ 2 = c y x ^ 2 := by
  let a : G → G → Additive M := fun x y => Additive.ofMul (c x y)
  have hca : ∀ x y z, a x y + a (x * y) z = a y z + a x (y * z) := fun x y z => by
    simp only [a, ← ofMul_mul, hc]
  let e : G → G → Additive M := fun x y => a x y - a y x
  have emul : ∀ x y z, e (x * y) z = e x z + e y z := by
    intro x y z
    have h₁ := hca x y z
    have h₂ := hca z x y
    have h₃ := hca x z y
    rw [mul_comm z x] at h₂
    rw [mul_comm z y] at h₃
    have e₁ : a (x * y) z = a y z + a x (y * z) - a x y := by rw [← h₁]; abel
    have e₂ : a z (x * y) = a z x + a (x * z) y - a x y := by rw [h₂]; abel
    have e₃ : a x z = a z y + a x (y * z) - a (x * z) y := by rw [← h₃]; abel
    simp only [e]
    rw [e₁, e₂, e₃]
    abel
  have hone : ∀ y, e 1 y = 0 := by
    intro y
    have h₁ := hca 1 1 y
    have h₂ := hca y 1 1
    simp only [_root_.one_mul, _root_.mul_one] at h₁ h₂
    have : a 1 1 = a 1 y := by
      have := congrArg (· - a 1 y) h₁; simpa using this
    have : a y 1 = a 1 1 := by
      have := congrArg (· - a y 1) h₂; simpa using this
    simp only [e]
    rw [sub_eq_zero]
    rw [← ‹a 1 1 = a 1 y›, ‹a y 1 = a 1 1›]
  have key : e x y + e x y = 0 := by
    rw [← emul, ← pow_two, h2, hone]
  apply Additive.ofMul.injective
  rw [ofMul_pow, ofMul_pow]
  change 2 • a x y = 2 • a y x
  rw [← sub_eq_zero, ← smul_sub, two_nsmul]
  exact key

theorem isFinite_two {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hf : IsFinite (sq A).left) :
    IsFinite (Two A).hom := by
  have h := (IsPullback.of_hasPullback (sq A) η[A]).map (Over.forget S)
  have h₂ : IsFinite (pullback.snd (sq A) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h hf
  rw [← Over.w (pullback.snd (sq A) η[A])]
  exact MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S)))

end GlobalTheory.TwoTors

namespace GlobalTheory.TwoTors

theorem pullTop_pullTop {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (u : Γ(Z, ⊤)ˣ) :
    GlobalTheory.CharKer.pullTop f (GlobalTheory.CharKer.pullTop g u) = GlobalTheory.CharKer.pullTop (f ≫ g) u := by
  ext; simp [GlobalTheory.CharKer.pullTop]; rfl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def inclHom (T : Over S) : (T ⟶ Two A) →* (T ⟶ A) := MonoidHom.mk' (· ≫ incl A) mul_incl

theorem comp_dif {T T' : Over S} (g : T' ⟶ T) (a b : T ⟶ A) (h : a ≫ sq A = b ≫ sq A) :
    g ≫ dif a b h = dif (g ≫ a) (g ≫ b) (by rw [Category.assoc, h, Category.assoc]) :=
  two_ext (by rw [Category.assoc, dif_incl, dif_incl, MonObj.comp_mul, GrpObj.comp_inv])

theorem dif_incl_incl {T : Over S} (u v : T ⟶ Two A) (h : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A) :
    dif (u ≫ incl A) (v ≫ incl A) h = u⁻¹ * v :=
  two_ext (by
    rw [dif_incl]
    change (inclHom T u)⁻¹ * inclHom T v = inclHom T (u⁻¹ * v)
    rw [map_mul, map_inv])

theorem incl_sq_eq {T : Over S} (u v : T ⟶ Two A) : (u ≫ incl A) ≫ sq A = (v ≫ incl A) ≫ sq A := by
  rw [comp_sq, comp_sq, incl_sq, incl_sq]

theorem sq_eq_one {T : Over S} (x : T ⟶ Two A) : x ^ 2 = 1 := by
  have h : inclHom T (x ^ 2) = inclHom T 1 := by rw [map_pow, map_one]; exact incl_sq x
  exact two_ext h

def tpt {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) : T ⟶ tripO A :=
  Over.homMk (GlobalTheory.PolRoot.tri (sq A).left a.left b.left c.left (by rw [← Over.comp_left, h₁, Over.comp_left])
    (by rw [← Over.comp_left, h₂, Over.comp_left])) (by
      show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom = T.hom
      rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst_assoc]
      exact Over.w a)

theorem tpt_ψ {T : Over S} (a b c : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = c ≫ sq A) :
    tpt a b c h₁ h₂ ≫ ψ A = lift (dif a b h₁) (dif b c h₂) := by
  have e₁ : tpt a b c h₁ h₂ ≫ t₁ A = a := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = a.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_fst])
  have e₂ : tpt a b c h₁ h₂ ≫ t₂ A = b := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = b.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_fst_assoc, pullback.lift_snd])
  have e₃ : tpt a b c h₁ h₂ ≫ t₃ A = c := Over.OverMorphism.ext (by
    show GlobalTheory.PolRoot.tri _ _ _ _ _ _ ≫ pullback.snd _ _ ≫ pullback.snd _ _ = c.left
    rw [GlobalTheory.PolRoot.tri, pullback.lift_snd_assoc, pullback.lift_snd])
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, ψ, lift_fst, lift_fst, comp_dif]; congr 1 <;> assumption
  · rw [Category.assoc, ψ, lift_snd, lift_snd, comp_dif]; congr 1 <;> assumption

variable (A)

theorem fst_δ : (pullback.fst _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₁ A) (t₂ A) (t₁₂_sq A)).left := by
  have : (Over.homMk (pullback.fst _ _) rfl : tripO A ⟶ pairO A) ≫ δ A = dif (t₁ A) (t₂ A) (t₁₂_sq A) := by
    rw [δ, comp_dif]; congr 1 <;> exact Over.OverMorphism.ext rfl
  exact congrArg CommaMorphism.left this

theorem snd_δ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (δ A).left = (dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₂ : (pullback.snd _ _ : Triple (sq A).left ⟶ _) ≫ (pairO A).hom = (tripO A).hom := by
    show pullback.snd _ _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [← pullback.condition_assoc, snd_w]
  have : (Over.homMk (pullback.snd _ _) w₂ : tripO A ⟶ pairO A) ≫ δ A = dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]; congr 1
    all_goals first
      | exact Over.OverMorphism.ext rfl
      | exact Over.OverMorphism.ext (pullback.condition (f := pullback.snd (sq A).left (sq A).left)).symm
  exact congrArg CommaMorphism.left this

theorem tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion : pr13 (sq A).left ≫ (δ A).left =
    (dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A)).left := by
  have w₃ : pr13 (sq A).left ≫ (pairO A).hom = (tripO A).hom := by
    show pr13 _ ≫ pullback.fst _ _ ≫ A.hom = pullback.fst _ _ ≫ pullback.fst _ _ ≫ A.hom
    rw [pr13, pullback.lift_fst_assoc, Category.assoc]
  have a₁ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₁ A = t₁ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.fst _ _ = _; rw [pr13, pullback.lift_fst]; rfl)
  have a₃ : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ s₂ A = t₃ A :=
    Over.OverMorphism.ext (by show pr13 _ ≫ pullback.snd _ _ = _; rw [pr13, pullback.lift_snd]; rfl)
  have : (Over.homMk (pr13 (sq A).left) w₃ : tripO A ⟶ pairO A) ≫ δ A =
      dif (t₁ A) (t₂ A) (t₁₂_sq A) * dif (t₂ A) (t₃ A) (t₂₃_sq A) := by
    rw [δ, comp_dif]
    apply two_ext
    rw [dif_incl, mul_incl, dif_incl, dif_incl, a₁, a₃]
    group
  exact congrArg CommaMorphism.left this

theorem killsSq_of (c : Γ((Two A ⊗ Two A).left, ⊤)ˣ) (w : Γ((Two A).left, ⊤)ˣ) (D : Γ(Triple (sq A).left, ⊤)ˣ)
    (hc : GlobalTheory.CharKer.pullTop (ψ A).left c = D)
    (hw : ∀ (T : Over S) (x y : T ⟶ Two A), GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) *
      GlobalTheory.CharKer.pullTop (x * y).left w = GlobalTheory.CharKer.pullTop x.left w * GlobalTheory.CharKer.pullTop y.left w) :
    KillsSq (sq A).left D (GlobalTheory.CharKer.pullTop (δ A).left w⁻¹) := by
  unfold KillsSq
  rw [pullTop_pullTop, pullTop_pullTop, pullTop_pullTop, fst_δ, snd_δ, tripleFibreProjOneThree_comp_fiberProductMulTwoToTwoTorsion, ← hc, map_inv, map_inv, map_inv]
  have H := hw (tripO A) (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))
  rw [map_pow] at H
  have hψ : (ψ A).left = (lift (dif (t₁ A) (t₂ A) (t₁₂_sq A)) (dif (t₂ A) (t₃ A) (t₂₃_sq A))).left := rfl
  rw [hψ, _root_.mul_assoc, ← _root_.mul_inv, ← H, _root_.mul_inv, mul_inv_cancel_left]

end GlobalTheory.TwoTors

open GlobalTheory.TwoTors in

theorem GlobalTheory.TwoTors.killsSq_of_triCocycle : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A],
    IsAbelianScheme A → IsFinite ((𝟙 A) ^ 2 : A ⟶ A).left → ∀ D : Γ(Triple ((𝟙 A) ^ 2 : A ⟶ A).left, ⊤)ˣ,
    TriCocycle ((𝟙 A) ^ 2 : A ⟶ A).left D → ∃ u, KillsSq ((𝟙 A) ^ 2 : A ⟶ A).left D u := by
  intro K _ _ A _ _ hA hf D hD
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_base_globalUnit_abelianScheme_baseChange A (Two A ⊗ Two A) hA (t₁ A).left (ψ A).left (GlobalTheory.T.tripleFiberProductOverMulTwo_isPullback A) D
  have key : ∀ {T : Over (Sp K)} (a b d : T ⟶ A) (h₁ : a ≫ sq A = b ≫ sq A) (h₂ : b ≫ sq A = d ≫ sq A) p₁ p₂,
      GlobalTheory.CharKer.pullTop (tri (sq A).left a.left b.left d.left p₁ p₂) D =
        GlobalTheory.CharKer.pullTop (lift (dif a b h₁) (dif b d h₂)).left c := by
    intro T a b d h₁ h₂ p₁ p₂
    rw [← hc, pullTop_pullTop, ← tpt_ψ a b d h₁ h₂]
    rfl
  have hcoc : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left c * GlobalTheory.CharKer.pullTop (lift (x * y) z).left c =
        GlobalTheory.CharKer.pullTop (lift y z).left c * GlobalTheory.CharKer.pullTop (lift x (y * z)).left c := by
    intro T x y z
    have H := hD T.left ((1 : T ⟶ Two A) ≫ incl A).left (x ≫ incl A).left ((x * y) ≫ incl A).left
      ((x * y * z) ≫ incl A).left (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
      (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left]) (by rw [← Over.comp_left, incl_sq_eq, Over.comp_left])
    rw [key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _),
      key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _), key _ _ _ (incl_sq_eq _ _) (incl_sq_eq _ _)] at H
    simp only [dif_incl_incl] at H
    have e₁ : (1 : T ⟶ Two A)⁻¹ * x = x := by group
    have e₂ : x⁻¹ * (x * y) = y := by group
    have e₃ : (1 : T ⟶ Two A)⁻¹ * (x * y) = x * y := by group
    have e₄ : (x * y)⁻¹ * (x * y * z) = z := by group
    have e₅ : x⁻¹ * (x * y * z) = y * z := by group
    rw [e₁, e₂, e₃, e₄, e₅] at H
    exact H
  have hsym : ∀ (T : Over (Sp K)) (x y : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) = GlobalTheory.CharKer.pullTop (lift y x).left (c ^ 2) := by
    intro T x y
    rw [map_pow, map_pow]
    exact sq_symm_of_cocycle (fun x y : T ⟶ Two A => GlobalTheory.CharKer.pullTop (lift x y).left c) (hcoc T) sq_eq_one x y
  have hcoc2 : ∀ (T : Over (Sp K)) (x y z : T ⟶ Two A),
      GlobalTheory.CharKer.pullTop (lift x y).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift (x * y) z).left (c ^ 2) =
        GlobalTheory.CharKer.pullTop (lift y z).left (c ^ 2) * GlobalTheory.CharKer.pullTop (lift x (y * z)).left (c ^ 2) := by
    intro T x y z
    simp only [map_pow]
    rw [← mul_pow, ← mul_pow, hcoc]
  obtain ⟨w, hw⟩ := GlobalTheory.T.symmetricTwoCocycle_finiteCommGroupScheme_coboundary K (Two A) (isFinite_two A hf) (c ^ 2) hcoc2 hsym
  refine ⟨GlobalTheory.CharKer.pullTop (δ A).left w⁻¹, ?_⟩
  exact killsSq_of A c w D hc hw
