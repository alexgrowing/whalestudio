import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubTrivDeltaAndEvenUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_char_of_cub [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have := connectedSpace_torus (S := S) (X := X)
  let pb : ∀ {W : Over S}, (W ⟶ splitTorus S X) → Γ(W.left, ⊤)ˣ := fun p => Units.map p.left.appTop.hom.toMonoidHom u
  have hpb : ∀ {W Z : Over S} (p : W ⟶ splitTorus S X) (r : Z ⟶ W) (z : Z.left),
      gm r.left z ⊤ (pb p) = gm (r ≫ p).left z ⊤ u := fun p r z => gm_pull r.left p.left z ⊤ trivial u
  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    let d : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ :=
      pb (fst _ _ * snd _ _) * (pb (fst _ _))⁻¹ * (pb (snd _ _))⁻¹
    have hd : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left), gm (lift x y).left z ⊤ d =
        gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := fun Z x y z => by
      simp only [d, map_mul, map_inv, hpb, MonObj.comp_mul, lift_fst, lift_snd]
    have e := eq_one_of_mul d (fun Z t t' y z => by
      have e' := congrArg Additive.ofMul (h₃ Z t t' y z)
      rw [hd, hd, hd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e') (fun Z t z => by
        rw [hd, _root_.mul_one, h₁, mul_inv_cancel, inv_one, _root_.one_mul]) Z x y z
    rw [hd, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at e
    exact e
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  let ρ : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ := pb (fst _ _)
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm t.left z ⊤ u := fun Z t y z => by rw [hpb, lift_fst]
  obtain ⟨χ, hχ, -⟩ := existsUnique_char ρ fun Z t t' y z => by rw [hρ, hρ, hρ, hmul]
  exact ⟨χ, fun Z t z => (hρ Z t (toUnit _) z).symm.trans (hχ Z t _ z)⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem cub_down_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₀ c c₀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ : U}
    (h : v₁ * v₂ * v₃ * v₄ = c * v₅ * v₆ * v₇) (hc : c * w₅ * w₆ * w₇ * w₀ = w₁ * w₂ * w₃ * w₄ * c₀)
    (r₁ : v₁ = w₁ * w₀⁻¹ * a₁) (r₂ : v₂ = w₂ * w₀⁻¹ * a₂) (r₃ : v₃ = w₃ * w₀⁻¹ * a₃) (r₄ : v₄ = w₄ * w₀⁻¹ * a₄)
    (r₅ : v₅ = w₅ * w₀⁻¹ * a₅) (r₆ : v₆ = w₆ * w₀⁻¹ * a₆) (r₇ : v₇ = w₇ * w₀⁻¹ * a₇) :
    a₁ * a₂ * a₃ * a₄ = c₀ * a₅ * a₆ * a₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul h
  have b := congrArg Additive.ofMul hc
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b ⊢
  linear_combination (norm := abel) a + b

theorem ratio_alg {U : Type} [CommGroup U] {a₁ a₂ a₃ a₄ a₅ a₆ a₇ s₁ s₂ s₃ s₄ s₅ s₆ s₇ g₁ g₂ g₃ g₄ g₅ g₆ g₇ c : U}
    (ha : a₁ * a₂ * a₃ * a₄ = c * a₅ * a₆ * a₇) (hs : s₁ * s₂ * s₃ * s₄ = c * s₅ * s₆ * s₇)
    (r₁ : s₁ = g₁ * a₁) (r₂ : s₂ = g₂ * a₂) (r₃ : s₃ = g₃ * a₃) (r₄ : s₄ = g₄ * a₄)
    (r₅ : s₅ = g₅ * a₅) (r₆ : s₆ = g₆ * a₆) (r₇ : s₇ = g₇ * a₇) :
    g₁ * g₂ * g₃ * g₄ = g₅ * g₆ * g₇ := by
  subst r₁ r₂ r₃ r₄ r₅ r₆ r₇
  have a := congrArg Additive.ofMul ha
  have b := congrArg Additive.ofMul hs
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a b ⊢
  linear_combination (norm := abel) b - a

theorem even_alg {U : Type} [CommGroup U] {A₁ A Wi Wx W₀ E s s' g : U}
    (e₁ : Wi * W₀⁻¹ * A₁ = E * (s * (Wx * W₀⁻¹ * A))) (e₂ : s * Wx = Wi * s')
    (e₃ : g⁻¹ * A₁ = s' * (g * A)) : E = g * g := by
  have a := congrArg Additive.ofMul e₁
  have b := congrArg Additive.ofMul e₂
  have d := congrArg Additive.ofMul e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a b d ⊢
  linear_combination (norm := abel) d - a - b

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_char_odd {S : Scheme.{0}} [ConnectedSpace S] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G} [IsMonHom i] (P : CP G) (σ : CubTriv P.c i) :
    ∃ κ : X, ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
      val σ.s (x⁻¹).left z J = gm (𝟙 T.left) z ⊤ (chV x κ) * (val P.sym (x ≫ i).left z J * val σ.s x.left z J) := by
  obtain ⟨E, hE⟩ := exists_odd P σ.s σ.gen
  obtain ⟨κ, hκ⟩ := exists_char_of_cub E (fun T x y u z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
      have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
      simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
      have o := odd_alg (σ := fun a : T ⟶ splitTorus S X => val σ.s a.left z C)
        (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
        (σ.cub T x y u z C hC) a b
      have o' := congrArg Additive.ofMul o
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div, ofMul_one] at o' ⊢
      linear_combination (norm := abel) o')
    (fun T z => by
      obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
      have e := hE T 1 z C hC
      rw [inv_one, σ.val_one hC, MonObj.one_comp, P.val_sym_one hC, _root_.mul_one, _root_.mul_one] at e
      exact e.symm)
  exact ⟨κ, fun T x z J hJ => (hE T x z J hJ).trans (by rw [hκ])⟩

end GlobalTheory.TwistCompare

namespace GlobalTheory.TwistCompare
open GlobalTheory GlobalTheory.UU GlobalTheory.CubTrivTorus GlobalTheory.CubeLift

theorem exists_twist_even : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k → IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] [IsCommMonObj G'₀] (β₀ : G'₀.left ⟶ G₀.left) (hβ₀ : IsGrpPullback G'₀ G₀ (spMap ρ) β₀) (P₀ : GlobalTheory.UU.CP G₀) (P'₀ : GlobalTheory.UU.CP G'₀) (w₀ : LB.Iso P'₀.L.L (P₀.L.L.pull β₀)), GlobalTheory.UU.IsCPMap P'₀ P₀ (spMap ρ) β₀ hβ₀.1.w w₀ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G₀) (i₁ : splitTorus (Sp k') X ⟶ G'₀), IsMonHom i → IsMonHom i₁ → GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ i → ∀ (σ : GlobalTheory.UU.CubTriv P₀.c i) (σ₁ : GlobalTheory.UU.CubTriv P'₀.c i₁), GlobalTheory.UU.CubTriv.Even (P := P'₀) σ₁ → ∃ χ : X, GlobalTheory.UU.CubTriv.Even (P := P₀) (σ.twist χ) := by
  intro k k' _ _ hk hk' ρ G₀ _ _ G'₀ _ _ β₀ hβ₀ P₀ P'₀ w₀ hm X _ _ _ i i₁ hi hi₁ hc σ σ₁ hσ₁
  haveI := hi
  haveI := hi₁
  haveI : ConnectedSpace (Sp k) := by letI := hk.toField; infer_instance
  haveI : ConnectedSpace (Sp k') := by letI := hk'.toField; infer_instance
  obtain ⟨κ, hκ⟩ := exists_char_odd P₀ σ
  let f := spMap ρ
  let hw : β₀ ≫ G₀.hom = G'₀.hom ≫ f := hβ₀.1.w
  have hi' : SplitTorus.bcMap f X ≫ i.left = i₁.left ≫ β₀ := torusCompat_iff.1 hc
  have hcc : ∀ n : Fin 2, ![i₁.left, (1 : splitTorus (Sp k') X ⟶ G'₀).left] n ≫ β₀ =
      SplitTorus.bcMap f X ≫ ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left] n := fun n => by
    fin_cases n
    · exact hi'.symm
    · refine (one_left_comp hm.mul _).trans (Eq.trans ?_ (congrArg (SplitTorus.bcMap f X ≫ ·) (one_left G₀ _)).symm)
      rw [← SplitTorus.bcMap_hom, Category.assoc]
  obtain ⟨a, ha, H⟩ := CubTransport.exists_pmaps ((isGen_iff w₀).1 hm.gen) P₀.L.isLB P'₀.L.isLB
    (SplitTorus.bcMap f X) hcc σ.s σ.gen

  let up : ∀ T : Over (Sp k'), (T ⟶ splitTorus (Sp k') X) →* (Over.mk (T.hom ≫ f) ⟶ splitTorus (Sp k) X) :=
    fun T => toBaseHom (hw := SplitTorus.bcMap_hom f X) (fun T x y => Over.OverMorphism.ext
      (SplitTorus.mul_left_bcMap f X T x y _ _ rfl rfl).symm) T
  have up_left : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x).left = x.left ≫ SplitTorus.bcMap f X :=
    fun _ => rfl
  have up_comp : ∀ {T : Over (Sp k')} (x : T ⟶ splitTorus (Sp k') X), (up T x ≫ i).left = (x ≫ i₁).left ≫ β₀ :=
    fun x => by rw [Over.comp_left, up_left, Category.assoc, hi', Over.comp_left, Category.assoc]
  have vrel : ∀ (T : Over (Sp k')) (z : T.left) (C₀ C), Good P'₀.L.L z C₀ → Good P₀.L.L z C →
      ∀ x : T ⟶ splitTorus (Sp k') X, val σ.s (up T x).left z C =
        gw w₀ (x ≫ i₁).left z (C ((x ≫ i₁).left ≫ β₀)) (C₀ (x ≫ i₁).left) *
          (gw w₀ (1 : T ⟶ G'₀).left z (C ((1 : T ⟶ G'₀).left ≫ β₀)) (C₀ (1 : T ⟶ G'₀).left))⁻¹ *
          val a x.left z C₀ := fun T z C₀ C hC₀ hC x =>
    (CubTransport.val_pmaps hcc H x.left hC hC₀).trans
      (congrArg₂ (· * ·) (prod_triv (i := i₁) x (fun q => gw w₀ q z (C (q ≫ β₀)) (C₀ q))) rfl)

  obtain ⟨r, hr⟩ := TorusCoord.exists_ratio P'₀.L.isLB (fun _ _ _ => rfl) σ₁.s σ₁.gen a ha
  have a_one : ∀ (T : Over (Sp k')) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (1 : T ⟶ splitTorus (Sp k') X).left z C₀ = 1 := fun T z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have e := vrel T z C₀ C hC₀ hC 1
    rw [map_one, σ.val_one hC, MonObj.one_comp, mul_inv_cancel, _root_.one_mul] at e
    exact e.symm
  have a_cub : ∀ (T : Over (Sp k')) (x y u : T ⟶ splitTorus (Sp k') X) (z : T.left) (C₀), Good P'₀.L.L z C₀ →
      val a (x * y * u).left z C₀ * val a x.left z C₀ * val a y.left z C₀ * val a u.left z C₀ =
        cubV P'₀.c z C₀ (x ≫ i₁) (y ≫ i₁) (u ≫ i₁) * val a (x * y).left z C₀ * val a (x * u).left z C₀ *
          val a (y * u).left z C₀ := fun T x y u z C₀ hC₀ => by
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have h₀ := σ.cub (Over.mk (T.hom ≫ f)) (up T x) (up T y) (up T u) z C hC
    have hup : ∀ q : T ⟶ splitTorus (Sp k') X, up T q ≫ i = toBase hw (q ≫ i₁) :=
      fun q => Over.OverMorphism.ext (up_comp q)
    simp only [← map_mul, hup] at h₀
    have c := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.2 (x ≫ i₁) (y ≫ i₁) (u ≫ i₁)
    simp only [← MonObj.mul_comp] at c
    exact cub_down_alg h₀ c (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
      (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _) (vrel T z C₀ C hC₀ hC _)
  obtain ⟨ψ, hψ⟩ := exists_char_of_cub r (fun T x y u z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      exact ratio_alg (a_cub T x y u z C₀ hC₀) (σ₁.cub T x y u z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀)
        (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀) (hr _ _ z C₀ hC₀))
    (fun T z => by
      obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
      have e := hr _ (1 : T ⟶ splitTorus (Sp k') X).left z C₀ hC₀
      rw [σ₁.val_one hC₀, a_one T z C₀ hC₀, _root_.mul_one] at e
      exact e.symm)

  have key : ∀ (T : Over (Sp k')) (x : T ⟶ splitTorus (Sp k') X) (z : T.left),
      gm (𝟙 T.left) z ⊤ (chV x κ) = gm (𝟙 T.left) z ⊤ (chV x (ψ + ψ)) := fun T x z => by
    obtain ⟨C₀, hC₀⟩ := exists_good_pt P'₀.L.isLB z
    obtain ⟨C, hC⟩ := exists_good_pt P₀.L.isLB z
    have hchv : chV (up T x) κ = chV x κ := Units.ext (by
      rw [chV_val, chV_val, up_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
        bcMap_charUnit])
    have e₁ := hκ (Over.mk (T.hom ≫ f)) (up T x) z C hC
    rw [← map_inv, up_comp, vrel T z C₀ C hC₀ hC, vrel T z C₀ C hC₀ hC, hchv] at e₁
    have s₁ := (hm.vals T z C₀ C hC₀ hC _ (fun _ => rfl)).2.1 (x ≫ i₁)
    rw [← GrpObj.inv_comp] at s₁
    have ev := hσ₁ T x z C₀ hC₀
    rw [hr _ _ z C₀ hC₀, hr _ _ z C₀ hC₀, hψ, hψ, chV_inv, map_inv] at ev
    exact (even_alg e₁ s₁ ev).trans (by rw [chV_add, map_mul])
  have hκψ : κ = ψ + ψ := by
    apply SplitTorusHom.charUnit_injective (S := Sp k')
    have e : chV (𝟙 (splitTorus (Sp k') X)) κ = chV (𝟙 (splitTorus (Sp k') X)) (ψ + ψ) :=
      unit_ext fun z _ => key _ _ z
    have e' := congrArg Units.val e
    rwa [chV_val, chV_val, Over.id_left, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply,
      RingHom.id_apply] at e'
  refine ⟨ψ, fun T t z J hJ => ?_⟩
  rw [σ.val_twist ψ _ hJ, σ.val_twist ψ _ hJ, hκ T t z J hJ, hκψ, chV_inv, chV_add, map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.TwistCompare
