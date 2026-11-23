import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BXOf

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

abbrev sig (R : Type) [CommRing R] [IsLocalRing R] :
    ((Spec (CommRingCat.of R)).presheaf.stalk (closedPoint R))ˣ →* Rˣ :=
  Units.map (stalkClosedPointIso (CommRingCat.of R)).hom.hom.toMonoidHom

section
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}

theorem top_le_of_mem (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U) :
    ⊤ ≤ r ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem r h).ge

theorem sig_gm_top (f : R →+* S) (a : Γ(Spec (CommRingCat.of R), ⊤)ˣ) :
    (sig S (gm (Spec.map (CommRingCat.ofHom f)) (closedPoint S) ⊤ a)).val =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a.val) := by
  have e1 := congrArg (fun q => q.hom (((Spec.map (CommRingCat.ofHom f)).app ⊤).hom a.val))
    (germ_stalkClosedPointIso_hom (CommRingCat.of S))
  have e2 := congrArg (fun q => q.hom a.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  refine Eq.trans ?_ (e1.trans e2)
  exact congrArg (stalkClosedPointIso (CommRingCat.of S)).hom.hom (gm_val _ _ ⊤ trivial a)

theorem sig_gm (f : R →+* S) (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U)
    (a : Γ(X, U)ˣ) :
    (sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) U a)).val =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (res (top_le_of_mem r h) (pullU r U a)).val) := by
  rw [← sig_gm_top]
  exact congrArg (fun u => (sig S u).val)
    ((gm_res (Spec.map (CommRingCat.ofHom f)) (closedPoint S) (top_le_of_mem r h) trivial _).trans
      (gm_pull (Spec.map (CommRingCat.ofHom f)) r (closedPoint S) U (top_le_of_mem r h trivial) a)).symm

theorem sig_nat (f : R →+* S) (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map f.toMonoidHom (sig R (gm r (closedPoint R) U a)) =
      sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) U a) := by
  apply Units.ext
  rw [sig_gm f r h]
  have := sig_gm (RingHom.id R) r h a
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at this
  exact congrArg f this

def del (L : LB X) (f : R →+* S) (JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι) (JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι)
    (ψ : Spec (CommRingCat.of R) ⟶ X) : Sˣ :=
  sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S)
    (L.U (JS (Spec.map (CommRingCat.ofHom f) ≫ ψ)) ⊓ L.U (JR ψ)) (L.g (JS (Spec.map (CommRingCat.ofHom f) ≫ ψ)) (JR ψ)))

theorem del_id {L : LB X} (hL : L.IsLB) {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    (ψ : Spec (CommRingCat.of R) ⟶ X) : del L (RingHom.id R) JR JR ψ = 1 := by
  rw [del, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, gm_self hL _ _ (hR ψ), map_one]

theorem del_comp {Q : Type} [CommRing Q] [IsLocalRing Q] {L : LB X} (hL : L.IsLB) (f : Q →+* R) (h : R →+* S)
    {JQ : (Spec (CommRingCat.of Q) ⟶ X) → L.ι} (hQ : Good L (closedPoint Q) JQ)
    {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    {JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι} (hS : Good L (closedPoint S) JS)
    (ψ : Spec (CommRingCat.of Q) ⟶ X) :
    del L (h.comp f) JQ JS ψ =
      Units.map h.toMonoidHom (del L f JQ JR ψ) * del L h JR JS (Spec.map (CommRingCat.ofHom f) ≫ ψ) := by
  have mQ : (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint R) ∈ L.U (JQ ψ) := top_le_of_mem ψ (hQ ψ) trivial
  have mQ' : (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S) ∈ L.U (JQ ψ) :=
    top_le_of_mem ψ (hQ ψ) trivial
  have mR : (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint S) ∈
      L.U (JR (Spec.map (CommRingCat.ofHom f) ≫ ψ)) := top_le_of_mem _ (hR _) trivial
  have mm : (Spec.map (CommRingCat.ofHom f) ≫ ψ) (closedPoint R) ∈
      L.U (JR (Spec.map (CommRingCat.ofHom f) ≫ ψ)) ⊓ L.U (JQ ψ) := ⟨hR _, mQ⟩
  have c := gm_cocycle hL _ _ (hS (Spec.map (CommRingCat.ofHom h) ≫ Spec.map (CommRingCat.ofHom f) ≫ ψ)) mR mQ'
  rw [del, del, del, sig_nat h _ mm, ← map_mul, mul_comm, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  exact congrArg (sig S) c.symm

theorem val_nat {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (f : R →+* S)
    {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    {JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι} (hS : Good L (closedPoint S) JS) (r : Spec (CommRingCat.of R) ⟶ Y) :
    sig S (val t (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) JS) =
      (∏ k, del L f JR JS (r ≫ φ k) ^ ε k) * Units.map f.toMonoidHom (sig R (val t r (closedPoint R) JR)) := by
  have m := hR.mem φ r
  have g := gen_trans ht (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) (hS.mem φ _) (top_le_of_mem r m trivial)
  refine (congrArg (sig S) g).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (sig_nat f r m _).symm))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact congrArg (fun q => sig S (gm q (closedPoint S) (L.U (JS q) ⊓ L.U (JR (r ≫ φ k))) (L.g (JS q) (JR (r ≫ φ k)))))
    (Category.assoc _ _ _)

end

section
variable {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)
  {T : Over S₀} {z : T.left} {J : (T.left ⟶ (G ⊗ G).left) → P.ι}

theorem val_pull3 {K : Type} [Fintype K] {φ : K → ((G3 G).left ⟶ (G ⊗ G).left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb P φ ε)) (hJ : Good P z J) {T' : Over S₀} (ρ : T ⟶ T') (x x' y : T' ⟶ G) :
    val (LB.pullGen P φ ε t (lift x (lift x' y)).left) ρ.left z J =
      val t (lift (ρ ≫ x) (lift (ρ ≫ x') (ρ ≫ y))).left z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift]

omit [GrpObj G] [IsCommMonObj G] in
theorem lift_four_points_comp_projections (x x' x'' y : T ⟶ G) : lift x (lift x' (lift x'' y)) ≫ x4 G 0 = x ∧
    lift x (lift x' (lift x'' y)) ≫ x4 G 1 = x' ∧ lift x (lift x' (lift x'' y)) ≫ x4 G 2 = x'' ∧
    lift x (lift x' (lift x'' y)) ≫ x4 G 3 = y := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [x4]

omit [GrpObj G] [IsCommMonObj G] in
theorem onObjOf3_x_eq (x x' y : T ⟶ G) : lift x (lift x' y) ≫ x3 G 0 = x ∧
    lift x (lift x' y) ≫ x3 G 1 = x' ∧ lift x (lift x' y) ≫ x3 G 2 = y := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [x3]

omit [IsCommMonObj G] in
theorem comp_padd {T' : Over S₀} (ρ : T ⟶ T') (a b : T' ⟶ G) : ρ ≫ padd G a b = (ρ ≫ a) * (ρ ≫ b) :=
  MonObj.comp_mul _ _ _

theorem biextension_firstLaw_associativity_value (hJ : Good P z J) (x x' x'' y : T ⟶ G) :
    val β.law1 (lift (x * x') (lift x'' y)).left z J * val β.law1 (lift x (lift x' y)).left z J =
      val β.law1 (lift x (lift (x' * x'') y)).left z J * val β.law1 (lift x' (lift x'' y)).left z J := by
  have := val_corr hJ β.assoc1 (lift x (lift x' (lift x'' y))).left
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))).symm.trans
    (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))))
  obtain ⟨a₀, a₁, a₂, a₃⟩ := lift_four_points_comp_projections x x' x'' y
  rwa [comp_padd, comp_padd, a₀, a₁, a₂, a₃] at e

theorem biextension_secondLaw_associativity_value (hJ : Good P z J) (x y y' y'' : T ⟶ G) :
    val β.law2 (lift x (lift (y * y') y'')).left z J * val β.law2 (lift x (lift y y')).left z J =
      val β.law2 (lift x (lift y (y' * y''))).left z J * val β.law2 (lift x (lift y' y'')).left z J := by
  have := val_corr hJ β.assoc2 (lift x (lift y (lift y' y''))).left
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))).symm.trans
    (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))))
  obtain ⟨a₀, a₁, a₂, a₃⟩ := lift_four_points_comp_projections x y y' y''
  rwa [comp_padd, comp_padd, a₀, a₁, a₂, a₃] at e

theorem biextension_firstLaw_commutativity_value (hJ : Good P z J) (x x' y : T ⟶ G) :
    val β.law1 (lift x (lift x' y)).left z J = val β.law1 (lift x' (lift x y)).left z J := by
  have e := (val_corr hJ β.comm1 (lift x (lift x' y)).left).trans (val_pull3 _ hJ _ _ _ _)
  obtain ⟨a₀, a₁, a₂⟩ := onObjOf3_x_eq x x' y
  rwa [a₀, a₁, a₂] at e

theorem biextension_secondLaw_commutativity_value (hJ : Good P z J) (x y y' : T ⟶ G) :
    val β.law2 (lift x (lift y y')).left z J = val β.law2 (lift x (lift y' y)).left z J := by
  have e := (val_corr hJ β.comm2 (lift x (lift y y')).left).trans (val_pull3 _ hJ _ _ _ _)
  obtain ⟨a₀, a₁, a₂⟩ := onObjOf3_x_eq x y y'
  rwa [a₀, a₁, a₂] at e

theorem law_compat (hJ : Good P z J) (x x' y y' : T ⟶ G) :
    val β.law1 (lift x (lift x' (y * y'))).left z J * val β.law2 (lift x (lift y y')).left z J *
        val β.law2 (lift x' (lift y y')).left z J =
      val β.law2 (lift (x * x') (lift y y')).left z J * val β.law1 (lift x (lift x' y)).left z J *
        val β.law1 (lift x (lift x' y')).left z J := by
  have := val_corr hJ β.compat (lift x (lift x' (lift y y'))).left
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))) (val_pull3 _ hJ _ _ _ _))).symm.trans
    (this.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_pull3 _ hJ _ _ _ _) (val_pull3 _ hJ _ _ _ _))) (val_pull3 _ hJ _ _ _ _))))
  obtain ⟨a₀, a₁, a₂, a₃⟩ := lift_four_points_comp_projections x x' y y'
  rwa [comp_padd, comp_padd, a₀, a₁, a₂, a₃] at e

omit [IsCommMonObj G] in
theorem biextension_first_law_product (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((lift x (lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  obtain ⟨a₀, a₁, a₂⟩ := onObjOf3_x_eq x x' y
  refine (Fintype.prod_equiv (Equiv.ulift : ULift (Fin 3) ≃ Fin 3) _
    (fun k => h ((lift x (lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, comp_padd, a₀, a₁, a₂, zpow_one, _root_.zpow_neg_one, _root_.zpow_neg_one]

omit [IsCommMonObj G] in
theorem biextension_second_law_product (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((lift x (lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  obtain ⟨a₀, a₁, a₂⟩ := onObjOf3_x_eq x y y'
  refine (Fintype.prod_equiv (Equiv.ulift : ULift (Fin 3) ≃ Fin 3) _
    (fun k => h ((lift x (lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨k⟩) ^ lawε ⟨k⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, comp_padd, a₀, a₁, a₂, zpow_one, _root_.zpow_neg_one, _root_.zpow_neg_one]

omit [GrpObj G] [IsCommMonObj G] in
theorem prod_swap (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k : Fin 2, h ((lift x y).left ≫ (![(lift (snd G G) (fst G G)).left, 𝟙 (G ⊗ G).left] k)) ^ (![1, -1] k : ℤ) =
      h (lift y x).left * (h (lift x y).left)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (lift x y ≫ lift (snd G G) (fst G G)).left ^ (1 : ℤ) * h ((lift x y).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
  rw [comp_lift, lift_fst, lift_snd, Category.comp_id, zpow_one, _root_.zpow_neg_one]

end

theorem alg_three {U : Type} [CommGroup U] {a b c d t : U} (h : t = a * b⁻¹ * c⁻¹ * d) : d * a = b * c * t := by
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg_two {U : Type} [CommGroup U] {a b d t : U} (h : t = a * b⁻¹ * d) : d * a = b * t := by
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∃ (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x)) →
  (∀ {R₀ : Type} [CommRing R₀] (B₀ : BX R₀) (δ : ∀ {R S : LAlg R₀}, LHom R S → B₀.G R → B₀.G R → (S : Type)ˣ)
    (t₁ t₂ : ∀ R : LAlg R₀, B₀.G R → B₀.G R → B₀.G R → (R : Type)ˣ) (w : ∀ R : LAlg R₀, B₀.G R → B₀.G R → (R : Type)ˣ),
    (∀ R x y, δ (LHom.id R) x y = 1) →
    (∀ {Q R S : LAlg R₀} (f : LHom Q R) (h : LHom R S) x y, δ (h.comp f) x y = Units.map (h.1 : (R : Type) →* (S : Type)) (δ f x y) * δ h (B₀.map f x) (B₀.map f y)) →
    (∀ R x x' x'' y, t₁ R (x + x') x'' y * t₁ R x x' y = t₁ R x (x' + x'') y * t₁ R x' x'' y) → (∀ R x x' y, t₁ R x x' y = t₁ R x' x y) →
    (∀ R x y y' y'', t₂ R x (y + y') y'' * t₂ R x y y' = t₂ R x y (y' + y'') * t₂ R x y' y'') → (∀ R x y y', t₂ R x y y' = t₂ R x y' y) →
    (∀ R x x' y y', t₁ R x x' (y + y') * t₂ R x y y' * t₂ R x' y y' = t₂ R (x + x') y y' * t₁ R x x' y * t₁ R x x' y') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x x' y, Units.map (f.1 : (R : Type) →* (S : Type)) (t₁ R x x' y) * δ f (x + x') y =
      δ f x y * δ f x' y * t₁ S (B₀.map f x) (B₀.map f x') (B₀.map f y)) →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y y', Units.map (f.1 : (R : Type) →* (S : Type)) (t₂ R x y y') * δ f x (y + y') =
      δ f x y * δ f x y' * t₂ S (B₀.map f x) (B₀.map f y) (B₀.map f y')) →
    (∀ R x y, w R x y * w R y x = 1) → (∀ R x x' y, t₁ R x x' y * w R (x + x') y = w R x y * w R x' y * t₂ R y x x') →
    (∀ {R S : LAlg R₀} (f : LHom R S) x y, Units.map (f.1 : (R : Type) →* (S : Type)) (w R x y) * δ f y x = δ f x y * w S (B₀.map f x) (B₀.map f y)) →
    ∃ (B : BX R₀) (κ : ∀ R, B.G R ≃+ B₀.G R) (b : ∀ R x y, B.P R x y),
      (∀ {R S : LAlg R₀} (f : LHom R S) x, κ S (B.map f x) = B₀.map f (κ R x)) ∧
      (∀ R x x' y, B.add1 (b R x y) (b R x' y) = B.smul (t₁ R (κ R x) (κ R x') (κ R y)) (b R (x + x') y)) ∧
      (∀ R x y y', B.add2 (b R x y) (b R x y') = B.smul (t₂ R (κ R x) (κ R y) (κ R y')) (b R x (y + y'))) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) x y, B.pmap f (b R x y) = B.smul (δ f (κ R x) (κ R y)) (b S (B.map f x) (B.map f y)))) →
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] [IsLocalRing R₀] (g : ℕ), SmoothOfRelativeDimension g G.hom →
    ∀ (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (s : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := Fin 2) ![(lift (snd G G) (fst G G)).left, 𝟙 (G ⊗ G).left] ![1, -1])),
    (s.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R₀))) (z : T.left) (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ x x' y : T ⟶ G,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift y x).left z J = 1 ∧
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift (x * x') y).left z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val s (lift x' y).left z J * ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift y (lift x x')).left z J) →
    ∃ (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) ∧ (∀ R x y, e R (x + y) = e R x * e R y) ∧
      (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) ∧
      ∃ (b : ∀ R x y, B.P R x y) (J : ∀ R : LAlg R₀, ((sp (R₀ := R₀) (R : Type)).left ⟶ (G ⊗ G).left) → P.1),
        (∀ R : LAlg R₀, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P (Z := (sp (R₀ := R₀) (R : Type)).left) (IsLocalRing.closedPoint (R : Type)) (J R)) ∧
        (∀ (R : LAlg R₀) x x' y, B.add1 (b R x y) (b R x' y) =
          B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R (x + x') y)) ∧
        (∀ (R : LAlg R₀) x y y', B.add2 (b R x y) (b R x y') =
          B.smul (Units.map (stalkClosedPointIso (CommRingCat.of (R : Type))).hom.hom.toMonoidHom (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (IsLocalRing.closedPoint (R : Type)) (J R))) (b R x (y + y')))) := by
  intro GRP CyclotomicNorms R₀ _ G _ _ _ g hg P β s hs
  obtain ⟨hs, hsym⟩ := hs
  obtain ⟨B₀, e, he, hadd, hnat⟩ := GRP G g hg
  have hex : ∀ R : LAlg R₀, ∃ J : (Spec (CommRingCat.of (R : Type)) ⟶ (G ⊗ G).left) → P.ι,
      Good P (closedPoint (R : Type)) J := fun R => by
    choose I hI using fun χ : Spec (CommRingCat.of (R : Type)) ⟶ (G ⊗ G).left =>
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart β.isLB (χ (closedPoint (R : Type)))
    exact ⟨I, hI⟩
  choose J hJ using hex
  have n2 : ∀ {R S : LAlg R₀} (f : LHom R S) (x y : B₀.G R),
      (lift (e S (B₀.map f x)) (e S (B₀.map f y))).left =
        Spec.map (CommRingCat.ofHom f.1.toRingHom) ≫ (lift (e R x) (e R y)).left := fun f x y => by
    rw [hnat, hnat, ← comp_lift]; rfl
  have n3 : ∀ {R S : LAlg R₀} (f : LHom R S) (x y w : B₀.G R),
      (lift (e S (B₀.map f x)) (lift (e S (B₀.map f y)) (e S (B₀.map f w)))).left =
        Spec.map (CommRingCat.ofHom f.1.toRingHom) ≫ (lift (e R x) (lift (e R y) (e R w))).left := fun f x y w => by
    rw [hnat, hnat, hnat, ← comp_lift, ← comp_lift]; rfl
  obtain ⟨B, κ, b, hκ, h1, h2, -⟩ := CyclotomicNorms B₀
    (fun {R S} f x y => del P f.1.toRingHom (J R) (J S) (lift (e R x) (e R y)).left)
    (fun R x x' y => sig R (val β.law1 (lift (e R x) (lift (e R x') (e R y))).left (closedPoint (R : Type)) (J R)))
    (fun R x y y' => sig R (val β.law2 (lift (e R x) (lift (e R y) (e R y'))).left (closedPoint (R : Type)) (J R)))
    (fun R x y => sig R (val s (lift (e R x) (e R y)).left (closedPoint (R : Type)) (J R)))
    (fun R x y => del_id β.isLB (hJ R) _)
    (fun {Q R S} f h x y => by
      rw [n2 f x y]
      exact del_comp β.isLB f.1.toRingHom h.1.toRingHom (hJ Q) (hJ R) (hJ S) _)
    (fun R x x' x'' y => by
      rw [hadd, hadd, ← map_mul, ← map_mul]
      exact congrArg (sig R) (biextension_firstLaw_associativity_value β (T := sp (R : Type)) (hJ R) _ _ _ _))
    (fun R x x' y => congrArg (sig R) (biextension_firstLaw_commutativity_value β (T := sp (R : Type)) (hJ R) _ _ _))
    (fun R x y y' y'' => by
      rw [hadd, hadd, ← map_mul, ← map_mul]
      exact congrArg (sig R) (biextension_secondLaw_associativity_value β (T := sp (R : Type)) (hJ R) _ _ _ _))
    (fun R x y y' => congrArg (sig R) (biextension_secondLaw_commutativity_value β (T := sp (R : Type)) (hJ R) _ _ _))
    (fun R x x' y y' => by
      rw [hadd, hadd, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg (sig R) (law_compat β (T := sp (R : Type)) (hJ R) _ _ _ _))
    (fun {R S} f x x' y => by
      rw [n3 f x x' y, hadd]
      exact alg_three ((val_nat β.isGen1 f.1.toRingHom (hJ R) (hJ S) _).trans
        (congrArg₂ (· * ·) (biextension_first_law_product (T := sp (R : Type)) _ _ _ (del P f.1.toRingHom (J R) (J S))) rfl)))
    (fun {R S} f x y y' => by
      rw [n3 f x y y', hadd]
      exact alg_three ((val_nat β.isGen2 f.1.toRingHom (hJ R) (hJ S) _).trans
        (congrArg₂ (· * ·) (biextension_second_law_product (T := sp (R : Type)) _ _ _ (del P f.1.toRingHom (J R) (J S))) rfl)))
    (fun R x y => by
      rw [← map_mul]
      exact (congrArg (sig R) (hsym (sp (R : Type)) _ _ (hJ R) (e R x) (e R x) (e R y)).1).trans (map_one _))
    (fun R x x' y => by
      rw [hadd, ← map_mul, ← map_mul, ← map_mul]
      exact congrArg (sig R) (hsym (sp (R : Type)) _ _ (hJ R) (e R x) (e R x') (e R y)).2)
    (fun {R S} f x y => by
      rw [n2 f x y]
      exact alg_two ((val_nat hs f.1.toRingHom (hJ R) (hJ S) _).trans
        (congrArg₂ (· * ·) (prod_swap (T := sp (R : Type)) _ _ (del P f.1.toRingHom (J R) (J S))) rfl)))
  refine ⟨B, fun R x => e R (κ R x), fun R => (he R).comp (κ R).bijective, fun R x y => ?_, fun f x => ?_,
    b, J, hJ, h1, h2⟩
  · show e R (κ R (x + y)) = _
    rw [map_add, hadd]
  · show e _ (κ _ (B.map f x)) = _
    rw [hκ, hnat]

end GlobalTheory.BXOf
