import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati

theorem prod_psum_eq_one {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A)
    (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  rcases hxy with rfl | rfl
  · rw [_root_.one_mul y, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]
  · rw [_root_.mul_one x, mul_left_comm (h x.left)⁻¹, inv_mul_cancel, _root_.mul_one, mul_inv_cancel]

theorem prod_mφ_eq_one {S : Scheme.{0}} {H₁ H₂ T : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (x y : T ⟶ H₁) (hxy : x = 1 ∨ y = 1) {U : Type} [CommGroup U]
    (h : (T.left ⟶ H₁.left ⨿ H₂.left) → U) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k = 1 := by
  simp only [mφ_comp]
  rw [Fintype.prod_sum_type]
  have e₁ := prod_psum_eq_one (x ≫ a) (y ≫ b)
    (hxy.imp (fun e => by rw [e, MonObj.one_comp]) (fun e => by rw [e, MonObj.one_comp]))
    (fun q => h (q ≫ coprod.inr))
  have e₂ := prod_psum_eq_one x y hxy (fun q => h (q ≫ coprod.inl))
  simp only [Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
  rw [e₁, e₂, inv_one, _root_.mul_one]

theorem push_pG_two {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map a) :
    push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ a := by
  rw [push, GtCoord.pG, GtCoord.pG, ← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (push_fstG e a)

set_option maxHeartbeats 1600000 in

theorem gen_invariant_of_mul : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ [ConnectedSpace (thickObj R I e G₁).left] (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg _ v hv hm
  have := (U₁.gt e).q_hom
  have := (U₁.gt e).i_hom
  have hM := jn_isLB D₁.toPre D₂.toPre
  have ti : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (t : Z ⟶ splitTorus _ D₁.toPre.X),
      push (U₁.gt e).pG (t ≫ (U₁.gt e).i) = 1 := fun t =>
    (TorusCoord.im_congr (U₁.gt e) (x' := 1) (by
      rw [Category.assoc, (U₁.gt e).isKernel.w, MonObj.one_comp, comp_toUnit_assoc, Hom.one_def])).trans
      (TorusCoord.im_one (U₁.gt e))
  have unit : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x y : T ⟶ thickObj R I e G₁),
      push (U₁.gt e).pG x = 1 ∨ push (U₁.gt e).pG y = 1 → ∃ ρ : Γ(T.left, ⊤)ˣ,
        ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (r : Z ⟶ T) (z : Z.left) (J),
          Good (JN D₁.toPre D₂.toPre) z J →
          gm r.left z ⊤ ρ = val v (lift (r ≫ x) (r ≫ y)).left z J := fun x y hxy => by
    obtain ⟨ρ, hρ⟩ := exists_unit_of_formal hM (fun V _ h =>
      (Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (mφ_push (U₁.gt e).pG (U₂.gt e).pG
        (TorusCoord.im_mul (U₁.gt e)) (TorusCoord.im_mul (U₂.gt e)) (push_pG_two U₁ U₂ e hf)
        (push_pG_two U₁ U₂ e hg) x y k).symm).trans
        (prod_mφ_eq_one fB gB (push (U₁.gt e).pG x) (push (U₁.gt e).pG y) hxy h))
      (LB.pullGen (JN D₁.toPre D₂.toPre) _ _ v (lift x y).left) (DVR.pullGen_isGen _ _ _ _ hv _)
    refine ⟨ρ, fun Z r z J hJ => (hρ _ r.left z J hJ).symm.trans ((val_pull hJ _ _ _).trans ?_)⟩
    rw [← Over.comp_left, comp_lift]
  have one : ∀ (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J),
      Good (JN D₁.toPre D₂.toPre) z J →
      ∀ y : T ⟶ thickObj R I e G₁, val v (lift 1 y).left z J = 1 ∧ val v (lift y 1).left z J = 1 :=
    fun T z J hJ y => by
      have := hm T z J hJ 1 1 y (TorusCoord.im_one (U₁.gt e))
      rw [_root_.mul_one] at this
      exact ⟨left_eq_mul.1 this.1, left_eq_mul.1 this.2⟩
  have gd : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good (JN D₁.toPre D₂.toPre) z J := fun {Z} z => by
    choose J hJ using fun χ : Z ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left => Geo.Tor.exists_chart hM (χ z)
    exact ⟨J, hJ⟩
  obtain ⟨ρ₁, h₁⟩ := unit (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (snd _ _) (Or.inl (ti _))
  obtain ⟨ρ₂, h₂⟩ := unit (snd _ _) (fst (splitTorus _ D₁.toPre.X) (thickObj R I e G₁) ≫ (U₁.gt e).i) (Or.inr (ti _))
  have e₁ := fun Z t y z J hJ => h₁ Z (lift t y) z J hJ
  have e₂ := fun Z t y z J hJ => h₂ Z (lift t y) z J hJ
  simp only [lift_fst_assoc, lift_snd] at e₁ e₂
  have k₁ := fun Z t y z => unit_eq_one ρ₁ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, e₁ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).1) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₁ Z t 1 z J hJ).trans (one Z z J hJ _).2) (Z := Z) t y z
  have k₂ := fun Z t y z => unit_eq_one ρ₂ (fun Z t t' y z => by
      obtain ⟨J, hJ⟩ := gd z
      rw [e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, e₂ Z _ y z J hJ, MonObj.mul_comp]
      exact (hm Z z J hJ _ _ y (ti t)).2) (fun Z t z => by
      obtain ⟨J, hJ⟩ := gd z
      exact (e₂ Z t 1 z J hJ).trans (one Z z J hJ _).1) (Z := Z) t y z
  intro T z J hJ x x' y y' hx hy
  obtain ⟨t, rfl⟩ := TorusCoord.exists_torus (U₁.gt e) x x' hx
  obtain ⟨t', rfl⟩ := TorusCoord.exists_torus (U₁.gt e) y y' hy
  rw [(hm T z J hJ _ x' _ (ti t)).1, (hm T z J hJ _ y' x' (ti t')).2, ← e₁ T t _ z J hJ, ← e₂ T t' _ z J hJ, k₁, k₂,
    _root_.one_mul, _root_.one_mul]

end GlobalTheory.HomMum

end
