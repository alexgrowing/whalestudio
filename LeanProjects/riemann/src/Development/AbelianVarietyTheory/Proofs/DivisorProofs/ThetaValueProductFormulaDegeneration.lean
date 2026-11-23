import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteNormalising
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TensPer

theorem prod_psum_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {U : Type} [CommGroup U]
    (H : ((G ⊗ G).left ⟶ G.left) → U) :
    ∏ K : ULift.{0} (Finset (Fin 2)), H (psum G (x2 G) K.down).left ^ ((-1 : ℤ) ^ (2 - K.down.card)) =
      H (psum G (x2 G) {0, 1}).left * (H (psum G (x2 G) {0}).left)⁻¹ * (H (psum G (x2 G) {1}).left)⁻¹ *
        H (psum G (x2 G) ∅).left := by
  refine (Fintype.prod_equiv Equiv.ulift _
    (fun I => H (psum G (x2 G) I).left ^ ((-1 : ℤ) ^ (2 - I.card))) fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : (-1 : ℤ) ^ (2 - ({0} : Finset (Fin 2)).card) = -1 := by decide
  have q₂ : (-1 : ℤ) ^ (2 - ({1} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₂, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem periods_alg {U : Type} [CommGroup U] {X : Type} [AddCommGroup X] {P : Type} [Mul P] (c : X → P)
    (c_add : ∀ x y, c (x + y) = c x * c y) (t : X → X → U) (θ : P → P → P → U) (symm : ∀ x y, t x y = t y x)
    (add : ∀ x x' y, t (x + x') y * θ (c x) (c x') (c y) = t x y * t x' y) {r : ℕ}
    (W : Matrix (Fin r) (Fin r) ℤ) (a b : Fin r → X) :
    (∏ i, ∏ j, t (a i + b i) (a j + b j) ^ W i j) * (∏ i, ∏ j, t (a i) (a j) ^ W i j)⁻¹ *
        (∏ i, ∏ j, t (b i) (b j) ^ W i j)⁻¹ =
      (∏ i, ∏ j, (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j)) * ∏ i, ∏ j, t (a i) (b j) ^ ((W + W.transpose) i j) := by
  have base : ∀ x x' y y' : X, t (x + x') (y + y') * (t x y)⁻¹ * (t x' y')⁻¹ =
      (θ (c x) (c x') (c y * c y') * θ (c y) (c y') (c x) * θ (c y) (c y') (c x'))⁻¹ * (t x y' * t y x') := by
    intro x x' y y'
    have e₁ := add x x' (y + y')
    have e₂ := add y y' x
    have e₃ := add y y' x'
    rw [c_add] at e₁
    have s₁ := symm x (y + y')
    have s₂ := symm x' (y + y')
    have s₃ := symm y x
    have s₄ := symm y' x
    have s₅ := symm y' x'
    apply Additive.ofMul.injective
    have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃
    have b₁ := E s₁; have b₂ := E s₂; have b₃ := E s₃; have b₄ := E s₄; have b₅ := E s₅
    simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ b₁ b₂ b₃ b₄ b₅ ⊢
    linear_combination (norm := abel) a₁ + a₂ + a₃ + b₁ + b₂ + b₃ + b₄ + b₅
  have hij : ∀ i j, t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ * (t (b i) (b j) ^ W i j)⁻¹ =
      (θ (c (a i)) (c (b i)) (c (a j) * c (b j)) * θ (c (a j)) (c (b j)) (c (a i)) *
        θ (c (a j)) (c (b j)) (c (b i))) ^ (-W i j) * (t (a i) (b j) ^ W i j * t (a j) (b i) ^ W i j) := by
    intro i j
    rw [← inv_zpow, ← inv_zpow, ← mul_zpow, ← mul_zpow, base, zpow_neg, ← inv_zpow, ← mul_zpow, mul_zpow]
  have hc : ∏ i, ∏ j, t (a j) (b i) ^ W i j = ∏ i, ∏ j, t (a i) (b j) ^ W j i := Finset.prod_comm
  calc _ = ∏ i, ∏ j, (t (a i + b i) (a j + b j) ^ W i j * (t (a i) (a j) ^ W i j)⁻¹ *
        (t (b i) (b j) ^ W i j)⁻¹) := by simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    _ = _ := Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hij i j
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Matrix.add_apply, Matrix.transpose_apply, zpow_add]
      rw [hc]

end GlobalTheory.Mum.TensPer

namespace GlobalTheory.Mum.TensPer
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem groupSchemePartialSum_twoPoints_empty : psum G (x2 G) ∅ = 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_first : psum G (x2 G) {0} = fst G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_second : psum G (x2 G) {1} = snd G G * 1 := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] by decide]
  rfl

theorem groupSchemePartialSum_twoPoints_both : psum G (x2 G) {0, 1} = fst G G * (snd G G * 1) := by
  unfold psum
  rw [show (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] by decide]
  rfl

end GlobalTheory.Mum.TensPer

open GlobalTheory.Mum.TensPer in

theorem GlobalTheory.Mum.Tens.tau_periods : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (a b : D'.toPre.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : ((TK R).left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = (∏ K : ULift.{0} (Finset (Fin 2)), gm ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left) z _ (T.w.s (fun k => J ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left ≫ tensφ T.pr k), J' ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) K.down).left))) ^ ((-1 : ℤ) ^ (2 - K.down.card))) * (∏ i, ∏ j, (cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) ((lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) * (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j)) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i) * cubV D.toPre.cub z J (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr j) (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i)) ^ (-W i j)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe a i) (T.xe b j)) (𝟙 _) z J ^ ((W + W.transpose) i j) := by
  intro R _ _ I D D' r W T a b z J J' hJ hJ'
  have twist_vector_at_zero : ∀ (E : DegData R I) (K : ((TK R).left ⟶ E.toPre.P.A.left) → E.toPre.P.L.ι),
      Good E.toPre.P.L z K → val (E.toPre.tau 0 0) (𝟙 _) z K = 1 := by
    intro E K hK
    have e := GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hK E.tau_bimult 0 0 0
    have f : th E.toPre z K (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) (cP E.toPre (TK R) 0) = 1 := by
      rw [cPoint_zero]; exact (isCub_cubV E.toPre.cub hK).face 1 1
    rw [f, _root_.mul_one] at e
    have h0 : val (E.toPre.tau (0 + 0) 0) (𝟙 _) z K = val (E.toPre.tau 0 0) (𝟙 _) z K :=
      congrArg (fun x => val (E.toPre.tau x 0) (𝟙 _) z K) (add_zero 0)
    exact mul_eq_left.1 (e.symm.trans h0)
  have hadd : ∀ x x' y : D.toPre.X, val (D.toPre.tau (x + x') y) (𝟙 _) z J *
      cubV D.toPre.cub z J (cP D.toPre (TK R) x) (cP D.toPre (TK R) x') (cP D.toPre (TK R) y) =
      val (D.toPre.tau x y) (𝟙 _) z J * val (D.toPre.tau x' y) (𝟙 _) z J :=
    fun x x' y => GlobalTheory.TauTwist.val_tau_add (𝟙 (TK R)) hJ D.tau_bimult x x' y
  have hsym : ∀ x y : D.toPre.X, val (D.toPre.tau x y) (𝟙 _) z J = val (D.toPre.tau y x) (𝟙 _) z J :=
    fun x y => GlobalTheory.TauTwist.val_tau_symm (𝟙 (TK R)) hJ x y
  set ρ : TK R ⟶ D'.toPre.P.A ⊗ D'.toPre.P.A :=
    lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b) with hρ
  have wv : ∀ (q : (D'.toPre.P.A ⊗ D'.toPre.P.A).left ⟶ D'.toPre.P.A.left) (y : D'.toPre.X),
      ρ.left ≫ q = D'.toPre.xK y →
      gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))) =
      gm (D'.toPre.xK y) z _ (T.w.s (fun k => J (D'.toPre.xK y ≫ tensφ T.pr k), J' (D'.toPre.xK y))) := by
    intro q y h
    have gen : ∀ m m' j j', m = m' → j = j' → gm m z _ (T.w.s j) = gm m' z _ (T.w.s j') := by
      rintro _ _ _ _ rfl rfl; rfl
    refine gen _ _ _ _ h ?_
    refine Prod.ext ?_ ?_
    · dsimp only
      funext k
      rw [← Category.assoc, h]
    · dsimp only
      rw [h]
  have hE : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) ∅).left = D'.toPre.xK 0 := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) 0).left
    rw [groupSchemePartialSum_twoPoints_empty, cPoint_zero, MonObj.comp_one]
  have h₀ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0}).left = D'.toPre.xK a := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) a).left
    rw [groupSchemePartialSum_twoPoints_first, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst]; rfl
  have h₁ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {1}).left = D'.toPre.xK b := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) b).left
    rw [groupSchemePartialSum_twoPoints_second, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_snd]; rfl
  have h₂ : ρ.left ≫ (psum D'.toPre.P.A (x2 D'.toPre.P.A) {0, 1}).left = D'.toPre.xK (a + b) := by
    rw [← Over.comp_left]
    show _ = (cP D'.toPre (TK R) (a + b)).left
    rw [groupSchemePartialSum_twoPoints_both, MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, _root_.mul_one, hρ, lift_fst, lift_snd, cPoint_add]; rfl
  have hA : ∀ i, ρ ≫ fst D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe a i) := fun i => by
    rw [hρ, lift_fst_assoc, Category.assoc, T.c_pr]; rfl
  have hB : ∀ i, ρ ≫ snd D'.toPre.P.A D'.toPre.P.A ≫ T.pr i = cP D.toPre (TK R) (T.xe b i) := fun i => by
    rw [hρ, lift_snd_assoc, Category.assoc, T.c_pr]; rfl
  have P := prod_psum_two (G := D'.toPre.P.A)
    (fun q => gm (ρ.left ≫ q) z _ (T.w.s (fun k => J (ρ.left ≫ q ≫ tensφ T.pr k), J' (ρ.left ≫ q))))
  beta_reduce at P
  rw [P]
  rw [wv _ _ h₂, wv _ _ h₀, wv _ _ h₁, wv _ _ hE]
  simp only [hA, hB]
  rw [GlobalTheory.TauBalBox.tau_val D'.toPre hJ' a b (𝟙 _)]
  have hrig : (val D'.toPre.rigK (𝟙 _) z J')⁻¹ = val (D'.toPre.psi 0) (𝟙 _) z J' := by
    have e := GlobalTheory.TauBalBox.tau_val D'.toPre hJ' 0 0 (𝟙 _)
    rw [twist_vector_at_zero D' J' hJ'] at e
    have h0 : val (D'.toPre.psi (0 + 0)) (𝟙 _) z J' = val (D'.toPre.psi 0) (𝟙 _) z J' :=
      congrArg (fun x => val (D'.toPre.psi x) (𝟙 _) z J') (add_zero 0)
    rw [h0, mul_inv_cancel, _root_.one_mul] at e
    exact (inv_mul_eq_one.1 e.symm).symm
  rw [hrig, T.psi (a + b) z J J' hJ hJ', T.psi a z J J' hJ hJ', T.psi b z J J' hJ hJ', T.psi 0 z J J' hJ hJ']
  have hQ0 : ∏ i, ∏ j, val (D.toPre.tau (T.xe 0 i) (T.xe 0 j)) (𝟙 _) z J ^ W i j = 1 :=
    Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
      rw [show T.xe 0 = 0 from map_zero _]
      exact (congrArg (· ^ W i j) (twist_vector_at_zero D J hJ)).trans (one_zpow _)
  have hQab : ∏ i, ∏ j, val (D.toPre.tau (T.xe (a + b) i) (T.xe (a + b) j)) (𝟙 _) z J ^ W i j =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe a i + T.xe b i) (T.xe a j + T.xe b j)) (𝟙 _) z J ^ W i j := by
    rw [map_add]; rfl
  rw [hQ0, hQab]
  have key := periods_alg (cP D.toPre (TK R)) (cPoint_add D.toPre (TK R))
    (fun x y => val (D.toPre.tau x y) (𝟙 _) z J) (cubV D.toPre.cub z J) hsym hadd W (T.xe a) (T.xe b)
  beta_reduce at key
  apply Additive.ofMul.injective
  have k := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at k ⊢
  linear_combination (norm := abel) k
