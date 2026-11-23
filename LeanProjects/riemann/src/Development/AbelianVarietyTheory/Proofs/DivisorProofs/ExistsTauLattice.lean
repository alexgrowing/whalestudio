import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TauLocal

section Alg

variable {X U : Type} [AddCommGroup X] [CommGroup U]

theorem firstLaw_unique (θ : X → X → U) {I : Type} (b : Module.Basis I ℤ X) {f f' : X → U}
    (hf : ∀ a a', f (a + a') * θ a a' = f a * f a') (hf' : ∀ a a', f' (a + a') * θ a a' = f' a * f' a')
    (h : ∀ i, f (b i) = f' (b i)) : f = f' := by
  let g : X →+ Additive U := AddMonoidHom.mk' (fun a => Additive.ofMul (f a / f' a)) (fun a a' => by
    apply Additive.toMul.injective
    simp only [toMul_add, toMul_ofMul]
    have e := hf a a'
    have e' := hf' a a'
    rw [← eq_mul_inv_iff_mul_eq] at e e'
    rw [e, e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]
    abel)
  have hg : g.toIntLinearMap = 0 := b.ext fun i => by
    simp [g, h i]
  funext a
  have := congrArg (fun q => q a) hg
  simp only [LinearMap.zero_apply, AddMonoidHom.coe_toIntLinearMap] at this
  have e : Additive.ofMul (f a / f' a) = 0 := this
  exact div_eq_one.1 (Additive.ofMul.injective e)

def ExtCar (U X : Type) : Type := U × X

def extGroup (θ : X → X → U) (h0 : ∀ a, θ 0 a = 1) (hs : ∀ a b, θ a b = θ b a)
    (hc : ∀ a a' a'', θ (a + a') a'' * θ a a' = θ a (a' + a'') * θ a' a'') : AddCommGroup (ExtCar U X) :=
  letI : Add (ExtCar U X) :=
    ⟨fun p q => ((p : U × X).1 * (q : U × X).1 * (θ (p : U × X).2 (q : U × X).2)⁻¹, (p : U × X).2 + (q : U × X).2)⟩
  letI : Zero (ExtCar U X) := ⟨((1 : U), (0 : X))⟩
  letI : Neg (ExtCar U X) := ⟨fun p => (((p : U × X).1)⁻¹ * θ (p : U × X).2 (-(p : U × X).2), -(p : U × X).2)⟩
  { add_assoc := fun p q r => by
      refine Prod.ext ?_ (add_assoc ((p : U × X).2) _ _)
      show (p : U × X).1 * (q : U × X).1 * (θ (p : U × X).2 (q : U × X).2)⁻¹ * (r : U × X).1 *
          (θ ((p : U × X).2 + (q : U × X).2) (r : U × X).2)⁻¹ =
        (p : U × X).1 * ((q : U × X).1 * (r : U × X).1 * (θ (q : U × X).2 (r : U × X).2)⁻¹) *
          (θ (p : U × X).2 ((q : U × X).2 + (r : U × X).2))⁻¹
      have e := congrArg Additive.ofMul (hc (p : U × X).2 (q : U × X).2 (r : U × X).2)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e ⊢
      linear_combination (norm := abel) -e
    zero_add := fun p => by
      refine Prod.ext ?_ (zero_add ((p : U × X).2))
      show 1 * (p : U × X).1 * (θ 0 (p : U × X).2)⁻¹ = (p : U × X).1
      rw [h0, inv_one, _root_.mul_one, _root_.one_mul]
    add_zero := fun p => by
      refine Prod.ext ?_ (add_zero ((p : U × X).2))
      show (p : U × X).1 * 1 * (θ (p : U × X).2 0)⁻¹ = (p : U × X).1
      rw [hs, h0, inv_one, _root_.mul_one, _root_.mul_one]
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
      refine Prod.ext ?_ (neg_add_cancel ((p : U × X).2))
      show ((p : U × X).1)⁻¹ * θ (p : U × X).2 (-(p : U × X).2) * (p : U × X).1 *
          (θ (-(p : U × X).2) (p : U × X).2)⁻¹ = 1
      rw [hs (-(p : U × X).2)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    add_comm := fun p q => by
      refine Prod.ext ?_ (add_comm ((p : U × X).2) _)
      show (p : U × X).1 * (q : U × X).1 * (θ (p : U × X).2 (q : U × X).2)⁻¹ =
        (q : U × X).1 * (p : U × X).1 * (θ (q : U × X).2 (p : U × X).2)⁻¹
      rw [hs, mul_comm (p : U × X).1] }

theorem exists_firstLaw (θ : X → X → U) (h0 : ∀ a, θ 0 a = 1) (hs : ∀ a b, θ a b = θ b a)
    (hc : ∀ a a' a'', θ (a + a') a'' * θ a a' = θ a (a' + a'') * θ a' a'') {I : Type} (b : Module.Basis I ℤ X)
    (m : I → U) : ∃ f : X → U, (∀ a a', f (a + a') * θ a a' = f a * f a') ∧ ∀ i, f (b i) = m i := by
  letI : AddCommGroup (ExtCar U X) := extGroup θ h0 hs hc
  let s : X →ₗ[ℤ] ExtCar U X := b.constr ℤ (fun i => (((m i, b i) : U × X) : ExtCar U X))
  let π : ExtCar U X →+ X := { toFun := fun p => (p : U × X).2, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hπ : π.toIntLinearMap ∘ₗ s = LinearMap.id := b.ext fun i => by
    simp only [LinearMap.comp_apply, s, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply]
    erw [Module.Basis.constr_basis]
    rfl
  have h2 : ∀ a, ((s a : ExtCar U X) : U × X).2 = a := fun a => congrArg (fun q => q a) hπ
  refine ⟨fun a => ((s a : ExtCar U X) : U × X).1, fun a a' => ?_, fun i => ?_⟩
  · have e : ((s (a + a') : ExtCar U X) : U × X).1 = ((s a : ExtCar U X) : U × X).1 * ((s a' : ExtCar U X) : U × X).1 *
        (θ ((s a : ExtCar U X) : U × X).2 ((s a' : ExtCar U X) : U × X).2)⁻¹ := by
      rw [s.map_add]; rfl
    show ((s (a + a') : ExtCar U X) : U × X).1 * θ a a' = _
    rw [e, h2, h2, inv_mul_cancel_right]
  · show ((s (b i) : ExtCar U X) : U × X).1 = m i
    simp only [s]
    erw [Module.Basis.constr_basis]

theorem cub_compat (θ : X → X → X → U) (s01 : ∀ x y z, θ x y z = θ y x z) (s12 : ∀ x y z, θ x y z = θ x z y)
    (coc : ∀ x x' x'' y, θ (x + x') x'' y * θ x x' y = θ x (x' + x'') y * θ x' x'' y) (x x' y y' : X) :
    θ (x + x') y y' * θ x x' y' * θ x x' y = θ x x' (y + y') * θ x y y' * θ x' y y' := by
  have rot : ∀ p q r, θ p q r = θ r p q := fun p q r => by rw [s12, s01]
  have a := coc x x' y y'
  have b := coc x' y y' x
  rw [rot (x' + y) y' x, rot x' y x, rot x' (y + y') x, rot y y' x] at b
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a' b' ⊢
  linear_combination (norm := abel) a' + b'

theorem exists_symm_triv [Module.Free ℤ X] (θ : X → X → X → U) (face : ∀ x y, θ 0 x y = 1)
    (s01 : ∀ x y z, θ x y z = θ y x z) (s12 : ∀ x y z, θ x y z = θ x z y)
    (coc : ∀ x x' x'' y, θ (x + x') x'' y * θ x x' y = θ x (x' + x'') y * θ x' x'' y) :
    ∃ mu : X → X → U, (∀ a b, mu a b = mu b a) ∧ ∀ a a' b, mu (a + a') b * θ a a' b = mu a b * mu a' b := by
  let b := Module.Free.chooseBasis ℤ X
  have h0 : ∀ y a, θ 0 a y = 1 := fun y a => face a y
  have hs : ∀ y a a', θ a a' y = θ a' a y := fun y a a' => s01 a a' y
  have hc : ∀ y a a' a'', θ (a + a') a'' y * θ a a' y = θ a (a' + a'') y * θ a' a'' y := fun y a a' a'' => coc a a' a'' y
  choose nu hnu1 hnu2 using fun i => exists_firstLaw (fun a a' => θ a a' (b i)) (h0 _) (hs _) (hc _) b (fun _ => 1)
  choose mu hmu1 hmu2 using fun y => exists_firstLaw (fun a a' => θ a a' y) (h0 y) (hs y) (hc y) b (fun j => nu j y)
  have c1 : ∀ i a, mu (b i) a = nu i a := fun i a => congrFun (firstLaw_unique _ b (hmu1 (b i)) (hnu1 i)
    (fun j => by rw [hmu2, hnu2, hnu2])) a
  have c2 : ∀ y y' a, mu (y + y') a * θ y y' a = mu y a * mu y' a := by
    intro y y'
    have e := firstLaw_unique (fun a a' => θ a a' (y + y')) b (hmu1 (y + y'))
      (f' := fun a => mu y a * mu y' a * (θ y y' a)⁻¹) (fun a a' => by
        have e1 := hmu1 y a a'
        have e2 := hmu1 y' a a'
        have e3 := cub_compat θ s01 s12 coc a a' y y'
        have r1 : θ y y' (a + a') = θ (a + a') y y' := by rw [s12, s01]
        have r2 : θ y y' a = θ a y y' := by rw [s12, s01]
        have r3 : θ y y' a' = θ a' y y' := by rw [s12, s01]
        show mu y (a + a') * mu y' (a + a') * (θ y y' (a + a'))⁻¹ * θ a a' (y + y') =
          mu y a * mu y' a * (θ y y' a)⁻¹ * (mu y a' * mu y' a' * (θ y y' a')⁻¹)
        rw [r1, r2, r3]
        apply Additive.ofMul.injective
        have f1 := congrArg Additive.ofMul e1
        have f2 := congrArg Additive.ofMul e2
        have f3 := congrArg Additive.ofMul e3
        simp only [ofMul_mul, ofMul_inv] at f1 f2 f3 ⊢
        linear_combination (norm := abel) f1 + f2 - f3)
      (fun i => by
        show mu (y + y') (b i) = mu y (b i) * mu y' (b i) * (θ y y' (b i))⁻¹
        rw [hmu2, hmu2, hmu2, eq_mul_inv_iff_mul_eq]
        exact hnu1 i y y')
    intro a
    have := congrFun e a
    rw [this, inv_mul_cancel_right]
  have c3 : ∀ y a, mu a y = mu y a := by
    intro y
    have e := firstLaw_unique (fun a a' => θ a a' y) b (hmu1 y) (f' := fun a => mu a y) (fun a a' => c2 a a' y)
      (fun i => by rw [hmu2, c1])
    exact fun a => (congrFun e a).symm
  exact ⟨fun a b' => mu b' a, fun a b' => c3 a b', fun a a' b' => hmu1 b' a a'⟩

end Alg

section Cub

variable {A U : Type} [CommGroup A] [CommGroup U]

def cob (h : A → U) (x x' y : A) : U :=
  h (x * x' * y) * (h (x * x'))⁻¹ * (h (x * y))⁻¹ * (h (x' * y))⁻¹ * h x * h x' * h y * (h 1)⁻¹

theorem isCub_cob (h : A → U) : IsCub (cob h) where
  face x y := by
    simp only [cob, _root_.one_mul]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one]
    abel
  s01 x y z := by
    simp only [cob]
    rw [mul_comm x y]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  s12 x y z := by
    simp only [cob]
    rw [mul_right_comm x y z, mul_comm z y]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  coc x x' x'' y := by
    simp only [cob]
    rw [_root_.mul_assoc x x' x'', _root_.mul_assoc x x' y, _root_.mul_assoc x' x'' y]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem isCub_mul_inv {θ θ' : A → A → A → U} (h : IsCub θ) (h' : IsCub θ') :
    IsCub (fun x y z => θ x y z * (θ' x y z)⁻¹) where
  face x y := by simp only [h.face, h'.face, inv_one, _root_.mul_one]
  s01 x y z := by simp only [h.s01 x y z, h'.s01 x y z]
  s12 x y z := by simp only [h.s12 x y z, h'.s12 x y z]
  coc x x' x'' y := by
    have e := congrArg Additive.ofMul (h.coc x x' x'' y)
    have e' := congrArg Additive.ofMul (h'.coc x x' x'' y)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e e' ⊢
    linear_combination (norm := abel) e - e'

theorem isCub_of_inj {P : Type} {V : P → Type} [∀ p, CommGroup (V p)] (F : ∀ p, U →* V p)
    (hF : ∀ u u' : U, (∀ p, F p u = F p u') → u = u') {θ : A → A → A → U}
    (h : ∀ p, IsCub (fun x y z => F p (θ x y z))) : IsCub θ where
  face x y := hF _ _ fun p => by rw [(h p).face, map_one]
  s01 x y z := hF _ _ fun p => (h p).s01 x y z
  s12 x y z := hF _ _ fun p => (h p).s12 x y z
  coc x x' x'' y := hF _ _ fun p => by rw [map_mul, map_mul]; exact (h p).coc x x' x'' y

end Cub

section Sch

variable {X' Y' Z' : Scheme.{0}}

def trH (L : LB X') (jj : (Y' ⟶ X') → L.ι) (z : Y') (J : (Y' ⟶ X') → L.ι) (ψ : Y' ⟶ X') : (Y'.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U (jj ψ)) (L.g (J ψ) (jj ψ))

theorem val_eq_trH {L : LB X'} (jj : (Y' ⟶ X') → L.ι) (hjj : ∀ ψ y, ψ y ∈ L.U (jj ψ)) {K : Type} [Fintype K]
    {φ : K → (Y' ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    ∃ w : Γ(Y', ⊤)ˣ, ∀ (z : Y') J, Good L z J →
      val t (𝟙 Y') z J = gm (𝟙 Y') z ⊤ w * ∏ k, trH L jj z J (φ k) ^ ε k := by
  have htop : (⊤ : Y'.Opens) ≤ LB.wchart L φ (fun k => jj (φ k)) := fun y _ => Set.mem_iInter.2 fun k => hjj (φ k) y
  refine ⟨res htop (t.s (fun k => jj (φ k))), fun z J hJ => ?_⟩
  have e1 : gm (𝟙 Y') z ⊤ (res htop (t.s (fun k => jj (φ k)))) =
      gm (𝟙 Y') z (LB.wchart L φ (fun k => jj (φ k))) (t.s (fun k => jj (φ k))) := gm_res (𝟙 Y') z htop trivial _
  refine (gen_trans ht (𝟙 Y') z (hJ.mem φ (𝟙 Y')) (htop trivial)).trans ?_
  rw [mul_comm]
  refine congrArg₂ (· * ·) e1.symm (Finset.prod_congr rfl fun k _ => ?_)
  show trH L jj z J (𝟙 Y' ≫ φ k) ^ ε k = trH L jj z J (φ k) ^ ε k
  rw [Category.id_comp]

theorem val_scaleGen' {L : LB X'} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X')} {ε : K → ℤ} (w : Γ(Y', ⊤)ˣ)
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Z' ⟶ Y') (z : Z') (J : (Z' ⟶ X') → L.ι) (hJ : Good L z J) :
    val (DVR.scaleGen w t) r z J = gm r z ⊤ w * val t r z J := by
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) w) rfl)

theorem eq_of_gm {L : LB X'} (hL : L.IsLB) {w w' : Γ(Y', ⊤)ˣ}
    (h : ∀ (z : Y') (J : (Y' ⟶ X') → L.ι), Good L z J → gm (𝟙 Y') z ⊤ w = gm (𝟙 Y') z ⊤ w') : w = w' :=
  unit_ext fun z _ => by
    choose J hJ using fun ψ : Y' ⟶ X' => exists_chart hL (ψ z)
    exact h z J hJ

end Sch

section Main

variable {R : Type} [CommRing R] [IsLocalRing R] {B : Over (Sp R)} [GrpObj B] [IsCommMonObj B]

theorem exists_chart_all (M : RigLB B) :
    ∃ jj : ((𝟙_ (Over (Sp R))).left ⟶ B.left) → M.L.ι, ∀ ψ y, ψ y ∈ M.L.U (jj ψ) := by
  choose i hi using fun ψ : Sp R ⟶ B.left => exists_chart M.isLB (ψ (IsLocalRing.closedPoint R))
  refine ⟨i, fun ψ y => ?_⟩
  have e := DVR.eq_top_of_closedPoint_mem (V := R) (ψ ⁻¹ᵁ M.L.U (i ψ)) (hi ψ)
  have hy : y ∈ ψ ⁻¹ᵁ M.L.U (i ψ) := by rw [e]; trivial
  exact hy

theorem exists_tau_local (M : RigLB B) (cub : CubicalStr B M) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (c : X → (𝟙_ (Over (Sp R)) ⟶ B)) (c_add : ∀ a b, c (a + b) = c a * c b) :
    ∃ tau : ∀ a b : X, LB.Gen (LB.LinComb M.L (PolDeg.lamPts (c a) (c b)) PolDeg.negε),
      (∀ a b, (tau a b).IsGen) ∧
      (∀ a b z J, Good M.L z J → val (tau a b) (𝟙 _) z J = val (tau b a) (𝟙 _) z J) ∧
      (∀ a a' b z J, Good M.L z J →
        val (tau (a + a') b) (𝟙 _) z J * cubV cub z J (c a) (c a') (c b) =
          val (tau a b) (𝟙 _) z J * val (tau a' b) (𝟙 _) z J) := by
  obtain ⟨jj, hjj⟩ := exists_chart_all M
  have hlam : ∀ x x' y : 𝟙_ (Over (Sp R)) ⟶ B, ∃ w : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ, ∀ z J, Good M.L z J →
      cubV cub z J x x' y = gm (𝟙 _) z ⊤ w * cob (fun p : 𝟙_ (Over (Sp R)) ⟶ B => trH M.L jj z J p.left) x x' y := by
    intro x x' y
    obtain ⟨w, hw⟩ := val_eq_trH jj hjj (t := LB.pullGen M.L (thφ B (x3 B)) thε cub.t (lift x (lift x' y)).left)
      (DVR.pullGen_isGen _ _ _ _ cub.isGen (lift x (lift x' y)).left)
    refine ⟨w, fun z J hJ => ?_⟩
    have e1 := val_cub cub (𝟙 _) hJ x x' y
    rw [Over.id_left, Category.id_comp, Category.id_comp, Category.id_comp] at e1
    rw [← e1, hw z J hJ]
    exact congrArg _ (prod_cub x x' y (trH M.L jj z J))
  choose lam hlam using hlam
  have hcub : IsCub lam := by
    refine isCub_of_inj
      (P := {p : (𝟙_ (Over (Sp R))).left × (((𝟙_ (Over (Sp R))).left ⟶ B.left) → M.L.ι) // Good M.L p.1 p.2})
      (fun p => gm (𝟙 (𝟙_ (Over (Sp R))).left) p.1.1 ⊤) (fun u u' h => eq_of_gm M.isLB fun z J hJ => by
        exact h ⟨(z, J), hJ⟩) fun p => ?_
    have e : (fun x x' y => gm (𝟙 _) p.1.1 ⊤ (lam x x' y)) = fun x x' y => cubV cub p.1.1 p.1.2 x x' y *
        (cob (fun q : 𝟙_ (Over (Sp R)) ⟶ B => trH M.L jj p.1.1 p.1.2 q.left) x x' y)⁻¹ := by
      funext x x' y
      rw [hlam x x' y p.1.1 p.1.2 p.2, mul_inv_cancel_right]
    rw [e]
    exact isCub_mul_inv (isCub_cubV cub p.2) (isCub_cob _)
  have c0 : c 0 = 1 := by
    have := c_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  obtain ⟨mu, hmus, hmua⟩ := exists_symm_triv (fun a a' b => lam (c a) (c a') (c b))
    (fun x y => by simp only [c0, hcub.face]) (fun x y z => hcub.s01 _ _ _) (fun x y z => hcub.s12 _ _ _)
    (fun x x' x'' y => by simp only [c_add]; exact hcub.coc _ _ _ _)
  have hu : ∀ a b, ∃ u : LB.Gen (LB.LinComb M.L (PolDeg.lamPts (c a) (c b)) PolDeg.negε), u.IsGen := fun a b =>
    DVR.exists_gen_of_local (V := R) M.L M.isLB _ _
  choose u hu using hu
  have hw := fun a b => val_eq_trH jj hjj (hu a b)
  choose w hw using hw
  have key : ∀ a b z J, Good M.L z J →
      val (DVR.scaleGen (mu a b * (w a b)⁻¹) (u a b)) (𝟙 _) z J = gm (𝟙 _) z ⊤ (mu a b) *
        ((trH M.L jj z J (c a * c b).left)⁻¹ * trH M.L jj z J (c a).left * trH M.L jj z J (c b).left *
          (trH M.L jj z J (1 : 𝟙_ (Over (Sp R)) ⟶ B).left)⁻¹) := by
    intro a b z J hJ
    rw [val_scaleGen' _ _ _ _ _ hJ, hw a b z J hJ, map_mul, map_inv, Fin.prod_univ_four]
    simp [PolDeg.lamPts, PolDeg.negε]
  refine ⟨fun a b => DVR.scaleGen (mu a b * (w a b)⁻¹) (u a b), fun a b => DVR.scaleGen_isGen _ _ (hu a b),
    fun a b z J hJ => ?_, fun a a' b z J hJ => ?_⟩
  · rw [key a b z J hJ, key b a z J hJ, hmus a b, mul_comm (c a) (c b)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [key _ _ z J hJ, key _ _ z J hJ, key _ _ z J hJ, hlam _ _ _ z J hJ, c_add]
    have e := congrArg Additive.ofMul (congrArg (gm (𝟙 (𝟙_ (Over (Sp R))).left) z ⊤) (hmua a a' b))
    simp only [map_mul] at e
    simp only [cob]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e ⊢
    linear_combination (norm := abel) e

end Main

end GlobalTheory.TauLocal
