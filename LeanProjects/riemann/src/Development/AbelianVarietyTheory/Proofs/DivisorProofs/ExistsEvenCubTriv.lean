import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EvenGenTorus

open TorusCube

theorem exists_ratio {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]
    (i : H ⟶ G) [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen) :
    ∃ w : Γ((H ⊗ H ⊗ H).left, ⊤)ˣ, ∀ (T : Over S) (x y u : T ⟶ H) (z : T.left)
      (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      ∀ v : (T ⟶ H) → (T.left.presheaf.stalk z)ˣ, (∀ a, v a = val τ a.left z J) →
      (v (x * y * u) * v x * v y * v u *
        (cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * v (x * y) * v (x * u) * v (y * u) * v 1)⁻¹).val =
        gs (𝟙 T.left) z ⊤ ((lift x (lift y u)).left.appTop.hom w.val) := by
  let p₀ := x3 H 0
  let p₁ := x3 H 1
  let p₂ := x3 H 2
  have P : ∀ p : G3 H ⟶ H, HasVal L.L (fun _ _ h => h (p.left ≫ i.left))
      (fun _ r z J => val τ (r ≫ p.left) z J) := fun p =>
    ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left,
      DVR.pullGen_isGen _ _ _ _ hτ p.left, fun V _ k => by simp, fun Z r z J hJ => val_pull hJ _ _ _⟩
  let M := (lift (p₀ ≫ i) (lift (p₁ ≫ i) (p₂ ≫ i))).left
  have em : ∀ a b : G3 H ⟶ H, (a ≫ i) * (b ≫ i) = (a * b) ≫ i := fun a b => (MonObj.mul_comp _ _ _).symm
  have e1 : (1 : G3 H ⟶ G) = (1 : G3 H ⟶ H) ≫ i := (MonObj.one_comp _).symm
  have C : HasVal L.L (fun _ _ h => h ((p₀ * p₁ * p₂).left ≫ i.left) * (h ((p₀ * p₁).left ≫ i.left))⁻¹ *
      (h ((p₀ * p₂).left ≫ i.left))⁻¹ * (h ((p₁ * p₂).left ≫ i.left))⁻¹ * h (p₀.left ≫ i.left) *
        h (p₁.left ≫ i.left) * h (p₂.left ≫ i.left) * (h ((1 : G3 H ⟶ H).left ≫ i.left))⁻¹)
      (fun _ r z J => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (r ≫ M) z J) :=
    ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t M, DVR.pullGen_isGen _ _ _ _ c.isGen M,
      fun V _ h => by
        have := prod_cub (p₀ ≫ i) (p₁ ≫ i) (p₂ ≫ i) h
        rw [e1] at this
        simp only [em] at this
        simpa only [Over.comp_left] using this,
      fun Z r z J hJ => val_pull hJ _ _ _⟩
  obtain ⟨w, hw⟩ := (((((P (p₀ * p₁ * p₂)).mul (P p₀)).mul (P p₁)).mul (P p₂)).mul
    ((((C.mul (P (p₀ * p₁))).mul (P (p₀ * p₂))).mul (P (p₁ * p₂))).mul (P 1)).inv).exists_unit
    L.isLB (fun V _ k => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T x y u z J hJ v hv => ?_⟩
  refine Eq.trans ?_ (hw _ (lift x (lift y u)).left z J hJ)
  have r₀ : lift x (lift y u) ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y u) ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y u) ≫ p₂ = u := by simp [p₂, x3]
  have hM : (lift x (lift y u)).left ≫ M = (lift (x ≫ i) (lift (y ≫ i) (u ≫ i))).left := by
    simp only [M, ← Over.comp_left, comp_lift, ← Category.assoc, r₀, r₁, r₂]
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂, hv]
  rw [hM]
  rfl

theorem cube (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G)
    [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen)
    (T : Over (Spec (CommRingCat.of k))) (x y u : T ⟶ splitTorus (Spec (CommRingCat.of k)) X) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    val τ (x * y * u).left z J * val τ x.left z J * val τ y.left z J * val τ u.left z J =
      cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * val τ (x * y).left z J * val τ (x * u).left z J *
        val τ (y * u).left z J * val τ (1 : T ⟶ splitTorus (Spec (CommRingCat.of k)) X).left z J := by
  obtain ⟨w, hw⟩ := exists_ratio i L c τ hτ
  have hT : TwoUniqueSums (X × X × X) := inferInstance
  have face : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b d : Z ⟶ splitTorus (Spec (CommRingCat.of k)) X),
      (a = 1 ∨ b = 1 ∨ d = 1) → (lift a (lift b d)).left.appTop.hom w.val = 1 := by
    intro Z a b d h
    refine fn_ext fun q _ => ?_
    choose I hI using fun χ : Z.left ⟶ G.left => exists_chart L.isLB (χ q)
    have C := isCub_cubV c (show Good L.L q I from hI)
    rw [← hw Z a b d q I hI (fun a => val τ a.left q I) (fun _ => rfl), gs_eq _ q ⊤ trivial, map_one, map_one,
      Units.val_eq_one, mul_inv_eq_one]
    rcases h with rfl | rfl | rfl
    · rw [MonObj.one_comp, C.face]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₂]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₃]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
  have key := unit_eq_one k X w.val w.isUnit (face _ _ _ _ (Or.inr (Or.inl rfl))) (face _ _ _ _ (Or.inl rfl))
    (face _ _ _ _ (Or.inl rfl)) T x y u
  have := hw T x y u z J hJ _ (fun _ => rfl)
  rw [key, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_eq_one, mul_inv_eq_one] at this
  exact this

end GlobalTheory.EvenGenTorus
