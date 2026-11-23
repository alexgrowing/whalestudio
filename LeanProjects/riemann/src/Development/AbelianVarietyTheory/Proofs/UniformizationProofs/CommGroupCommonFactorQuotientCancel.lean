import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.WtBundle

section Units
variable {X Y Z W : Scheme.{0}}

theorem gm_appLE (f : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)ˣ) (z : Z) :
    gm (𝟙 Z) z ⊤ (Units.map (f.appLE U ⊤ h).hom.toMonoidHom a) = gm f z U a := by
  have e : Units.map (f.appLE U ⊤ h).hom.toMonoidHom a = res h (pullU f U a) := Units.ext rfl
  rw [e, gm_res _ z h trivial, gm_pull _ f z U (h trivial), Category.id_comp]

theorem gm_stalkMap (κ : W ⟶ Z) (w : W) (r : Z ⟶ Y) (U : Y.Opens) (h : r (κ w) ∈ U) (a : Γ(Y, U)ˣ) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (gm r (κ w) U a) = gm (κ ≫ r) w U a := by
  apply Units.ext
  rw [gm_val (κ ≫ r) w U h]
  show (κ.stalkMap w).hom (gm r (κ w) U a).val = _
  rw [gm_val r (κ w) U h]
  exact Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ U) w h _

theorem unit_ext_of_flat (π : X ⟶ Y) [Flat π] [Surjective π] {U : Y.Opens} {a b : Γ(Y, U)ˣ}
    (h : ∀ x, π x ∈ U → gm π x U a = gm π x U b) : a = b := by
  have e : pullU π U a = pullU π U b := unit_ext fun x hx => by
    rw [gm_pull (𝟙 X) π x U hx, gm_pull (𝟙 X) π x U hx, Category.id_comp]; exact h x hx
  exact Units.ext (FunDescent.app_injective π U (congrArg Units.val e))

theorem exists_unit_desc (π : X ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] (U : Y.Opens)
    (f : Γ(X, π ⁻¹ᵁ U)ˣ)
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (z : Z), g₁ ≫ π = g₂ ≫ π → π (g₁ z) ∈ U → π (g₂ z) ∈ U →
      gm g₁ z (π ⁻¹ᵁ U) f = gm g₂ z (π ⁻¹ᵁ U) f) :
    ∃ a : Γ(Y, U)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ X) (z : Z), π (g z) ∈ U →
      gm (g ≫ π) z U a = gm g z (π ⁻¹ᵁ U) f := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq π U f.val fun Z g₁ g₂ h₁ h₂ e => by
    have : Units.map (g₁.appLE _ ⊤ h₁).hom.toMonoidHom f = Units.map (g₂.appLE _ ⊤ h₂).hom.toMonoidHom f :=
      unit_ext fun z _ => by
        rw [gm_appLE, gm_appLE]
        exact hf Z g₁ g₂ z e (h₁ trivial) (h₂ trivial)
    exact congrArg Units.val this
  have hu : IsUnit a := FunDescent.isUnit_of_isUnit_app π U a (ha ▸ f.isUnit)
  refine ⟨hu.unit, fun Z g z hz => ?_⟩
  rw [← gm_pull g π z U hz]
  exact congrArg _ (Units.ext ha)

theorem exists_gen_desc {G B Y' : Scheme.{0}} (q : G ⟶ B) (N : LB B) (u : ∀ j, Γ(G, q ⁻¹ᵁ N.U j)ˣ)
    (hu : ∀ (Z : Scheme.{0}) (g : Z ⟶ G) (z : Z) (i j : N.ι), q (g z) ∈ N.U i → q (g z) ∈ N.U j →
      gm g z (q ⁻¹ᵁ N.U i) (u i) = gm (g ≫ q) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (q ⁻¹ᵁ N.U j) (u j))
    (π : Y' ⟶ Y) [Flat π] [Surjective π] [QuasiCompact π] {K : Type} [Fintype K] (φ : K → (Y ⟶ B))
    (ψ : K → (Y' ⟶ G)) (hψ : ∀ k, ψ k ≫ q = π ≫ φ k) (ε : K → ℤ)
    (inv : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (j : K → N.ι), g₁ ≫ π = g₂ ≫ π →
      (∀ k, q ((g₂ ≫ ψ k) z) ∈ N.U (j k)) →
      ∏ k, gm (g₁ ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k =
        ∏ k, gm (g₂ ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k) :
    ∃ s : LB.Gen (LB.LinComb N φ ε), s.IsGen := by
  have le : ∀ (j : K → N.ι) k, π ⁻¹ᵁ LB.wchart N φ j ≤ ψ k ⁻¹ᵁ (q ⁻¹ᵁ N.U (j k)) := fun j k y hy =>
    (congrArg (fun m : Y' ⟶ B => m y ∈ N.U (j k)) (hψ k)).mpr (Set.mem_iInter.1 hy k)
  have loc : ∀ j : K → N.ι, ∃ a : Γ(Y, LB.wchart N φ j)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z),
      π (g z) ∈ LB.wchart N φ j → gm (g ≫ π) z (LB.wchart N φ j) a =
        ∏ k, gm (g ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun j => by
    have v : ∀ (Z : Scheme.{0}) (g : Z ⟶ Y') (z : Z), π (g z) ∈ LB.wchart N φ j →
        gm g z (π ⁻¹ᵁ LB.wchart N φ j) (∏ k, res (le j k) (pullU (ψ k) _ (u (j k))) ^ ε k) =
          ∏ k, gm (g ≫ ψ k) z (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun Z g z hz => by
      rw [map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [map_zpow, gm_res g z (le j k) hz, gm_pull g (ψ k) z _ (le j k hz)]
    obtain ⟨a, ha⟩ := exists_unit_desc π (LB.wchart N φ j) (∏ k, res (le j k) (pullU (ψ k) _ (u (j k))) ^ ε k)
      fun Z g₁ g₂ z e h₁ h₂ => by
        rw [v Z g₁ z h₁, v Z g₂ z h₂]
        exact inv Z g₁ g₂ z j e fun k => le j k h₂
    exact ⟨a, fun Z g z hz => (ha Z g z hz).trans (v Z g z hz)⟩
  choose a ha using loc
  refine ⟨⟨a⟩, fun j j' => unit_ext_of_flat π fun y hy => ?_⟩
  have b : ∀ j, π y ∈ LB.wchart N φ j → gm π y (LB.wchart N φ j) (a j) =
      ∏ k, gm (ψ k) y (q ⁻¹ᵁ N.U (j k)) (u (j k)) ^ ε k := fun j hj => by
    have := ha j _ (𝟙 Y') y hj
    simpa only [Category.id_comp] using this
  refine ((gm_res π y _ hy _).trans (b j hy.1)).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_linComb N φ ε π y j j' hy.1 hy.2) ((gm_res π y _ hy _).trans (b j' hy.2))).trans ?_)))
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← mul_zpow, hu _ (ψ k) y (j k) (j' k) (le j k hy.1) (le j' k hy.2), hψ]

end Units

theorem commGroup_common_factor_quotient_cancel {U : Type} [CommGroup U] (c a b : U) : c * a * (c * b)⁻¹ = a * b⁻¹ := by
  rw [← div_eq_mul_inv, mul_div_mul_left_eq_div, div_eq_mul_inv]

section Wt
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X]

theorem gm_of_isWt {i : splitTorus S X ⟶ G} {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V)
    (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  let Z' : Over S := Over.mk (W.ι ≫ Z.hom)
  let κ : Z' ⟶ Z := Over.homMk W.ι rfl
  let w : W.toScheme := ⟨z, h₁, h₂⟩
  have e : ((κ ≫ t) ≫ i) * (κ ≫ g) = κ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have k₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ g)).left ⁻¹ᵁ V := by
    rw [e]; exact fun y _ => y.2.1
  have k₂ : ⊤ ≤ (κ ≫ g).left ⁻¹ᵁ V := fun y _ => y.2.2
  have a : Units.map ((((κ ≫ t) ≫ i) * (κ ≫ g)).left.appLE V ⊤ k₁).hom.toMonoidHom u =
      chV (κ ≫ t) χ * Units.map ((κ ≫ g).left.appLE V ⊤ k₂).hom.toMonoidHom u :=
    Units.ext ((hu Z' _ _ k₁ k₂).trans (congrArg (· * _) (chV_val _ χ).symm))
  have b := congrArg (gm (𝟙 Z'.left) w ⊤) a
  rw [map_mul, gm_appLE, gm_appLE, ← gm_charUnit, e] at b
  rw [← gm_charUnit]
  apply Units.map_injective (f := (W.ι.stalkMap w).hom.toMonoidHom)
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w)).1
  exact (gm_stalkMap W.ι w _ V h₁ u).trans (b.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_stalkMap W.ι w t.left ⊤ trivial _) (gm_stalkMap W.ι w g.left V h₂ u))).symm)

variable (Q : TQ G X)

theorem act_comp {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]

theorem exists_act {Z : Over S} {a b : Z ⟶ G} (e : a ≫ Q.q = b ≫ Q.q) :
    ∃ t : Z ⟶ splitTorus S X, a = (t ≫ Q.i) * b := by
  have := Q.q_hom
  have w : (a * b⁻¹) ≫ Q.q = toUnit Z ≫ η[Q.B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  exact ⟨Q.isKernel.lift _ _ w, by rw [Q.isKernel.lift_fst, inv_mul_cancel_right]⟩

theorem gm_act {V : Q.B.left.Opens} {u : Γ(G.left, Q.q.left ⁻¹ᵁ V)ˣ} {χ : X} (hu : IsWt Q.i _ u.val χ)
    {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h : Q.q.left (g.left z) ∈ V) :
    gm ((t ≫ Q.i) * g).left z (Q.q.left ⁻¹ᵁ V) u =
      gm (𝟙 Z.left) z ⊤ (chV t χ) * gm g.left z (Q.q.left ⁻¹ᵁ V) u :=
  gm_of_isWt hu t g z ((congrArg (fun m : Z ⟶ Q.B => m.left z ∈ V) (act_comp Q t g)).mpr h) h

theorem exists_bundle (χ : X) : ∃ (N : LB Q.B.left) (u : ∀ j, Γ(G.left, Q.q.left ⁻¹ᵁ N.U j)ˣ), N.IsLB ∧
    (∀ j, IsWt Q.i _ (u j).val χ) ∧
    ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z) (i j : N.ι), Q.q.left (g z) ∈ N.U i → Q.q.left (g z) ∈ N.U j →
      gm g z (Q.q.left ⁻¹ᵁ N.U i) (u i) =
        gm (g ≫ Q.q.left) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (Q.q.left ⁻¹ᵁ N.U j) (u j) := by
  have := Q.q_flat
  have := Q.q_surj
  have := Q.q_affine
  choose V hV u hu using fun b => Q.loc b χ
  have tr : ∀ i j, ∃ a : Γ(Q.B.left, V i ⊓ V j)ˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z),
      Q.q.left (g z) ∈ V i → Q.q.left (g z) ∈ V j → gm (g ≫ Q.q.left) z (V i ⊓ V j) a =
        gm g z (Q.q.left ⁻¹ᵁ V i) (u i) * (gm g z (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun i j => by
    have l₁ : Q.q.left ⁻¹ᵁ (V i ⊓ V j) ≤ Q.q.left ⁻¹ᵁ V i := fun _ h => h.1
    have l₂ : Q.q.left ⁻¹ᵁ (V i ⊓ V j) ≤ Q.q.left ⁻¹ᵁ V j := fun _ h => h.2
    have v : ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z), Q.q.left (g z) ∈ V i ⊓ V j →
        gm g z (Q.q.left ⁻¹ᵁ (V i ⊓ V j)) (res l₁ (u i) * (res l₂ (u j))⁻¹) =
          gm g z (Q.q.left ⁻¹ᵁ V i) (u i) * (gm g z (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun Z g z hz => by
      rw [map_mul, map_inv, gm_res g z l₁ hz, gm_res g z l₂ hz]
    obtain ⟨a, ha⟩ := exists_unit_desc Q.q.left (V i ⊓ V j) (res l₁ (u i) * (res l₂ (u j))⁻¹)
      fun Z g₁ g₂ z e h₁ h₂ => by
        let Z' : Over S := Over.mk (g₂ ≫ G.hom)
        let k₂ : Z' ⟶ G := Over.homMk g₂ rfl
        let k₁ : Z' ⟶ G := Over.homMk g₁ (by
          change g₁ ≫ G.hom = g₂ ≫ G.hom
          rw [← Over.w Q.q, reassoc_of% e])
        obtain ⟨t, ht⟩ := exists_act Q (show k₁ ≫ Q.q = k₂ ≫ Q.q from Over.OverMorphism.ext e)
        have a₁ := gm_act Q (hu i) t k₂ z h₂.1
        have a₂ := gm_act Q (hu j) t k₂ z h₂.2
        rw [← ht] at a₁ a₂
        rw [v Z g₁ z h₁, v Z g₂ z h₂]
        exact (congrArg₂ (fun a b => a * b⁻¹) a₁ a₂).trans (commGroup_common_factor_quotient_cancel _ _ _)
    exact ⟨a, fun Z g z h₁ h₂ => (ha Z g z ⟨h₁, h₂⟩).trans (v Z g z ⟨h₁, h₂⟩)⟩
  choose a ha using tr
  have b : ∀ i j x, Q.q.left x ∈ V i → Q.q.left x ∈ V j → gm Q.q.left x (V i ⊓ V j) (a i j) =
      gm (𝟙 _) x (Q.q.left ⁻¹ᵁ V i) (u i) * (gm (𝟙 _) x (Q.q.left ⁻¹ᵁ V j) (u j))⁻¹ := fun i j x h₁ h₂ => by
    have := ha i j _ (𝟙 _) x h₁ h₂
    rwa [Category.id_comp] at this
  refine ⟨⟨_, V, a⟩, u, ⟨?_, fun i => ?_, fun i j k => ?_⟩, hu, fun Z g z i j h₁ h₂ => ?_⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hV x⟩
  · refine unit_ext_of_flat Q.q.left fun x hx => ?_
    exact (gm_res _ x _ hx _).trans ((b i i x hx hx).trans ((mul_inv_cancel _).trans (map_one _).symm))
  · refine unit_ext_of_flat Q.q.left fun x hx => ?_
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ x _ hx _).trans (b i j x hx.1.1 hx.1.2))
      ((gm_res _ x _ hx _).trans (b j k x hx.1.2 hx.2)))).trans
      (Eq.trans ?_ ((gm_res _ x _ hx _).trans (b i k x hx.1.1 hx.2)).symm)
    rw [_root_.mul_assoc, inv_mul_cancel_left]
  · exact eq_mul_of_mul_inv_eq (ha i j Z g z h₁ h₂).symm

end Wt

section Square
variable {S : Scheme.{0}}

def sq {G T : Over S} [GrpObj G] (x y : T ⟶ G) : Fin 4 → (T ⟶ G) := ![x * y, x, y, 1]

theorem comp_sq {G T T' : Over S} [GrpObj G] (ρ : T' ⟶ T) (x y : T ⟶ G) (k : Fin 4) :
    ρ ≫ sq x y k = sq (ρ ≫ x) (ρ ≫ y) k := by
  fin_cases k
  exacts [MonObj.comp_mul _ _ _, rfl, rfl, MonObj.comp_one _]

theorem sq_comp {G H T : Over S} [GrpObj G] [GrpObj H] (x y : T ⟶ G) (f : G ⟶ H) [IsMonHom f] (k : Fin 4) :
    sq x y k ≫ f = sq (x ≫ f) (y ≫ f) k := by
  fin_cases k
  exacts [MonObj.mul_comp _ _ _, rfl, rfl, MonObj.one_comp _]

theorem sq_mul {G T : Over S} [GrpObj G] [IsCommMonObj G] (a b x y : T ⟶ G) (k : Fin 4) :
    sq (a * x) (b * y) k = sq a b k * sq x y k := by
  fin_cases k
  exacts [mul_mul_mul_comm _ _ _ _, rfl, rfl, (_root_.mul_one _).symm]

theorem prod_sq {G T : Over S} [GrpObj G] (x y : T ⟶ G) {U : Type} [CommGroup U] (F : (T ⟶ G) → U) :
    ∏ k, F (sq x y k) ^ Oε k = F (x * y) * (F x)⁻¹ * (F y)⁻¹ * F 1 := by
  rw [Fin.prod_univ_four]
  change F (x * y) ^ (1 : ℤ) * F x ^ (-1 : ℤ) * F y ^ (-1 : ℤ) * F 1 ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem prod_psum {B T : Over S} [GrpObj B] (x : Fin 2 → (T ⟶ B)) {U : Type} [CommGroup U] (F : (T ⟶ B) → U) :
    ∏ J : ULift.{0} (Finset (Fin 2)), F (psum B x J.down) ^ ((-1 : ℤ) ^ (2 - J.down.card)) =
      F (x 0 * x 1) * (F (x 0))⁻¹ * (F (x 1))⁻¹ * F 1 := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun J => F (psum B x J) ^ ((-1 : ℤ) ^ (2 - J.card)))
    (fun _ => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B x ∅ = 1 := rfl
  have p₁ : psum B x {0} = x 0 := _root_.mul_one (x 0)
  have p₂ : psum B x {1} = x 1 := _root_.mul_one (x 1)
  have p₃ : psum B x {0, 1} = x 0 * x 1 := congrArg (x 0 * ·) (_root_.mul_one (x 1))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

variable {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)

theorem exists_gen_lam (χ : X) (N : LB Q.B.left) (hN : N.IsLB) (u : ∀ j, Γ(G.left, Q.q.left ⁻¹ᵁ N.U j)ˣ)
    (hw : ∀ j, IsWt Q.i _ (u j).val χ)
    (hu : ∀ (Z : Scheme.{0}) (g : Z ⟶ G.left) (z : Z) (i j : N.ι), Q.q.left (g z) ∈ N.U i → Q.q.left (g z) ∈ N.U j →
      gm g z (Q.q.left ⁻¹ᵁ N.U i) (u i) =
        gm (g ≫ Q.q.left) z (N.U i ⊓ N.U j) (N.g i j) * gm g z (Q.q.left ⁻¹ᵁ N.U j) (u j)) :
    ∃ s : LB.Gen (abelian₂ Q.B N), s.IsGen := by
  have := Q.q_hom
  have := Q.i_hom
  have := Q.q_affine
  have : Flat (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @Flat) Q.q_flat Q.q_flat
    (Over.w Q.q).symm (Over.w Q.q).symm
  have : MorphismProperty.IsStableUnderComposition @Surjective := ⟨fun f g _ _ => inferInstance⟩
  have : Surjective (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @Surjective) Q.q_surj Q.q_surj
    (Over.w Q.q).symm (Over.w Q.q).symm
  have : QuasiCompact (Q.q ⊗ₘ Q.q).left := MorphismProperty.pullbackMap (P := @QuasiCompact)
    (inferInstanceAs (QuasiCompact Q.q.left)) (inferInstanceAs (QuasiCompact Q.q.left))
    (Over.w Q.q).symm (Over.w Q.q).symm
  obtain ⟨s, hs⟩ := exists_gen_desc Q.q.left N u hu (Q.q ⊗ₘ Q.q).left
    (fun k => (sq (fst Q.B Q.B) (snd Q.B Q.B) k).left) (fun k => (sq (fst G G) (snd G G) k).left)
    (fun k => by
      rw [← Over.comp_left, ← Over.comp_left, sq_comp, comp_sq, tensorHom_fst, tensorHom_snd]) Oε
    fun Z g₁ g₂ z j e h₂ => by
      let Z' : Over S := Over.mk (g₂ ≫ (G ⊗ G).hom)
      let k₂ : Z' ⟶ G ⊗ G := Over.homMk g₂ rfl
      let k₁ : Z' ⟶ G ⊗ G := Over.homMk g₁ (by
        change g₁ ≫ (G ⊗ G).hom = g₂ ≫ (G ⊗ G).hom
        rw [← Over.w (Q.q ⊗ₘ Q.q), reassoc_of% e])
      have e' : k₁ ≫ (Q.q ⊗ₘ Q.q) = k₂ ≫ (Q.q ⊗ₘ Q.q) := Over.OverMorphism.ext e
      obtain ⟨t, ht⟩ := exists_act Q (a := k₁ ≫ fst G G) (b := k₂ ≫ fst G G) (by
        rw [Category.assoc, Category.assoc, ← tensorHom_fst Q.q Q.q, reassoc_of% e'])
      obtain ⟨t', ht'⟩ := exists_act Q (a := k₁ ≫ snd G G) (b := k₂ ≫ snd G G) (by
        rw [Category.assoc, Category.assoc, ← tensorHom_snd Q.q Q.q, reassoc_of% e'])
      have a : ∀ k, k₁ ≫ sq (fst G G) (snd G G) k = (sq t t' k ≫ Q.i) * (k₂ ≫ sq (fst G G) (snd G G) k) :=
        fun k => by rw [comp_sq, comp_sq, ht, ht', sq_mul, sq_comp]
      have b : ∀ k, gm (k₁ ≫ sq (fst G G) (snd G G) k).left z (Q.q.left ⁻¹ᵁ N.U (j k)) (u (j k)) =
          gm (𝟙 Z'.left) z ⊤ (chV (sq t t' k) χ) *
            gm (k₂ ≫ sq (fst G G) (snd G G) k).left z (Q.q.left ⁻¹ᵁ N.U (j k)) (u (j k)) := fun k => by
        rw [a]; exact gm_act Q (hw (j k)) (sq t t' k) (k₂ ≫ sq (fst G G) (snd G G) k) z (h₂ k)
      have c : ∏ k, gm (𝟙 Z'.left) z ⊤ (chV (sq t t' k) χ) ^ Oε k = 1 := by
        have o : chV (1 : Z' ⟶ splitTorus S X) χ = 1 := by rw [chV, map_one]; rfl
        rw [prod_sq t t' fun a => gm (𝟙 Z'.left) z ⊤ (chV a χ), chV_mul, o, map_mul, map_one, _root_.mul_one,
          mul_right_comm, mul_inv_cancel_right, mul_inv_cancel]
      refine (Finset.prod_congr rfl fun k _ => (congrArg (· ^ Oε k) (b k)).trans (mul_zpow _ _ _)).trans ?_
      exact Finset.prod_mul_distrib.trans ((congrArg (· * _) c).trans (_root_.one_mul _))
  obtain ⟨s', hs', -⟩ := exists_gen hN (K' := ULift.{0} (Finset (Fin 2)))
    (φ' := fun I => (psum Q.B (x2 Q.B) I.down).left) (ε' := fun I => (-1) ^ (2 - I.down.card))
    (fun U _ h => (prod_sq _ _ fun a => h a.left).trans (prod_psum (x2 Q.B) fun a => h a.left).symm) s hs
  exact ⟨s', hs'⟩

theorem exists_genWt (χ : X) : ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ ∧
    ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen := by
  obtain ⟨N, u, hN, hw, hu⟩ := exists_bundle Q χ
  have le : ∀ J : PUnit → N.ι, (N.pull Q.q.left).U J ≤ Q.q.left ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ h => mem_pull.1 h
  refine ⟨N, ⟨fun J => res (le J) (u _)⟩, hN, ⟨fun J J' => unit_ext fun y hy => ?_, fun J => (hw _).res (le J)⟩,
    exists_gen_lam Q χ N hN u hw hu⟩
  exact ((gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans
    (hu _ (𝟙 _) y _ _ (le J hy.1) (le J' hy.2)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_pull_g N Q.q.left (𝟙 _) y J J' hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_res _ y _ hy.2 _)))).symm

end Square

end GlobalTheory.WtBundle

namespace GlobalTheory

theorem exists_weight_bundle : (∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (χ : X), ∃ (N : LB Q.B.left) (t : LB.Gen (N.pull Q.q.left)), N.IsLB ∧ Q.GenWt N t χ ∧ ∃ u : LB.Gen (abelian₂ Q.B N), u.IsGen) :=
  fun _ _ _ _ _ _ _ _ Q χ => WtBundle.exists_genWt Q χ

end GlobalTheory
end
