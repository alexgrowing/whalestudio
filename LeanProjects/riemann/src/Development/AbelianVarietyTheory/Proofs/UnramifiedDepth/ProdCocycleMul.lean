import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionGen

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

theorem cocycle_four (t : A → A → U) (coc : ∀ y y' y'', t (y * y') y'' * t y y' = t y (y' * y'') * t y' y'')
    (sym : ∀ y y', t y y' = t y' y) (p q a b : A) :
    t (p * q) (a * b) * t p q * t a b = t (p * a) (q * b) * t p a * t q b := by
  have e₁ := coc p q (a * b)
  have e₂ := coc q a b
  have e₃ := coc p a (q * b)
  have e₄ := coc a q b
  rw [_root_.mul_left_comm a q b] at e₃
  rw [_root_.mul_comm a q, sym a q] at e₄
  rw [e₁, e₃, _root_.mul_assoc, _root_.mul_assoc, ← e₂, ← e₄]

theorem prod_cocycle_mul (t : A → A → U) (coc : ∀ y y' y'', t (y * y') y'' * t y y' = t y (y' * y'') * t y' y'')
    (sym : ∀ y y', t y y' = t y' y) (a y : A) (n : ℕ) :
    (∏ k ∈ Finset.range n, t ((a * y) ^ k) (a * y)) * t a y ^ n * t 1 1 =
      (∏ k ∈ Finset.range n, t (a ^ k) a) * (∏ k ∈ Finset.range n, t (y ^ k) y) * t (a ^ n) (y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have c := cocycle_four t coc sym (a ^ n) (y ^ n) a y
    rw [← mul_pow] at c
    simp only [Finset.prod_range_succ]
    rw [pow_succ a, pow_succ y, pow_succ (t a y)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem prod_interchange (t₁ t₂ : A → A → A → U)
    (ic : ∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')
    (x a y : A) (n : ℕ) :
    (∏ k ∈ Finset.range n, t₁ (x ^ k) x (a * y)) * t₂ x a y ^ n * t₂ 1 a y =
      t₂ (x ^ n) a y * (∏ k ∈ Finset.range n, t₁ (x ^ k) x a) * (∏ k ∈ Finset.range n, t₁ (x ^ k) x y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have c := ic (x ^ n) x a y
    simp only [Finset.prod_range_succ]
    rw [pow_succ x, pow_succ (t₂ x a y)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem ratio_translate (t₁ t₂ : A → A → A → U)
    (coc : ∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'')
    (sym : ∀ x y y', t₂ x y y' = t₂ x y' y)
    (ic : ∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')
    (x a y : A) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : ∏ k ∈ Finset.range n, t₁ (x ^ k) x y = ∏ k ∈ Finset.range n, t₂ x (y ^ k) y) :
    (∏ k ∈ Finset.range n, t₂ x ((a * y) ^ k) (a * y)) * (∏ k ∈ Finset.range n, t₁ (x ^ k) x (a * y))⁻¹ =
      (∏ k ∈ Finset.range n, t₂ x (a ^ k) a) * (∏ k ∈ Finset.range n, t₁ (x ^ k) x a)⁻¹ := by
  have e₁ := prod_cocycle_mul (t₂ x) (coc x) (sym x) a y n
  have e₂ := prod_interchange t₁ t₂ ic x a y n
  have e₃ := coc x (a ^ n) 1 1
  rw [hy] at e₁
  rw [hx] at e₂
  rw [_root_.mul_one, _root_.mul_one] at e₃
  apply Additive.ofMul.injective
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₃ := congrArg Additive.ofMul e₃
  have a₄ := congrArg Additive.ofMul h
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ ⊢
  linear_combination (norm := abel) a₁ - a₂ + a₃ - a₄

end Alg

theorem exists_telescope {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : ℕ → (Y ⟶ X))
    (χ : Y ⟶ X) (φ : ℕ → K → (Y ⟶ X)) (ε : K → ℤ) (u : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (hu : ∀ i, (u i).IsGen)
    (hF : ∀ (i : ℕ) (U : Type) [CommGroup U] (h : (Y ⟶ X) → U),
      ∏ k, h (φ i k) ^ ε k = h (ψ (i + 1)) * (h (ψ i))⁻¹ * (h χ)⁻¹) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 3) ![ψ n, ψ 0, χ] ![1, -1, -n]), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t r z J = ∏ i ∈ Finset.range n, val (u i) r z J := by
  induction n with
  | zero =>
    obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![ψ 0, ψ 0, χ]) (ε' := ![1, -1, -(0 : ℕ)])
      (fun U _ h => by simp [Fin.prod_univ_succ]) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t, ht, fun Z r z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  | succ n ih =>
    obtain ⟨t, ht, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := ![ψ (n + 1), ψ 0, χ]) (ε' := ![1, -1, -(n + 1 : ℕ)]) (fun U _ h => by
        refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl (hF n U h))).trans ?_
        apply Additive.ofMul.injective
        simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
        module)
      (LB.mulGen L _ _ _ _ t (u n)) (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (hu n))
    refine ⟨t', ht', fun Z r z J hJ => ?_⟩
    rw [hv' _ _ z J hJ, val_mul hJ, hv Z r z J hJ, Finset.prod_range_succ]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {P : LB (G ⊗ G).left} (β : IsBiext G P)

theorem prod_law₁ {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((lift x (lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (x * x') y).left * (h (lift x y).left)⁻¹ * (h (lift x' y).left)⁻¹ := by
  have a₀ : lift x (lift x' y) ≫ x3 G 0 = x := by simp [x3]
  have a₁ : lift x (lift x' y) ≫ x3 G 1 = x' := by simp [x3]
  have a₂ : lift x (lift x' y) ≫ x3 G 2 = y := by simp [x3]
  have b : lift x (lift x' y) ≫ padd G (x3 G 0) (x3 G 1) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [a₀, a₁])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift x' y)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift x' y) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (lift x (lift x' y) ≫ lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

theorem prod_law₂ {T : Over S} (x y y' : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G ⊗ G).left) → U) :
    ∏ k, h ((lift x (lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift x (y * y')).left * (h (lift x y).left)⁻¹ * (h (lift x y').left)⁻¹ := by
  have a₀ : lift x (lift y y') ≫ x3 G 0 = x := by simp [x3]
  have a₁ : lift x (lift y y') ≫ x3 G 1 = y := by simp [x3]
  have a₂ : lift x (lift y y') ≫ x3 G 2 = y' := by simp [x3]
  have b : lift x (lift y y') ≫ padd G (x3 G 1) (x3 G 2) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [a₁, a₂])
  refine (Fintype.prod_equiv (Equiv.ulift : ULift (Fin 3) ≃ Fin 3) _
    (fun i => h ((lift x (lift y y')).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift x (lift y y') ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (lift x (lift y y') ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, b, a₀, a₁, a₂]
  simp only [_root_.zpow_neg, _root_.zpow_one]

omit [IsCommMonObj G] in
theorem comp_pow' {T T' : Over S} (ρ : T' ⟶ T) (a : T ⟶ G) (k : ℕ) : ρ ≫ a ^ k = (ρ ≫ a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem exists_first {T : Over S} (x a : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 3) ![(lift (x ^ n) a).left, (lift (x ^ 0) a).left, (lift x a).left] ![1, -1, -n]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J → val t ρ.left z J =
        ∏ k ∈ Finset.range n, val β.law1 (lift ((ρ ≫ x) ^ k) (lift (ρ ≫ x) (ρ ≫ a))).left z J := by
  obtain ⟨t, ht, hv⟩ := exists_telescope β.isLB (fun k => (lift (x ^ k) a).left) (lift x a).left _ _
    (fun k => LB.pullGen P _ _ β.law1 (lift (x ^ k) (lift x a)).left)
    (fun k => DVR.pullGen_isGen _ _ _ _ β.isGen1 _) (fun k U _ h => by
      refine (prod_law₁ (x ^ k) x a h).trans ?_
      rw [pow_succ]) n
  refine ⟨t, ht, fun T' ρ z J hJ => (hv _ _ z J hJ).trans (Finset.prod_congr rfl fun k _ => ?_)⟩
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, comp_pow']

theorem exists_second {T : Over S} (x a : T ⟶ G) (n : ℕ) :
    ∃ t : LB.Gen (LB.LinComb P (K := Fin 3) ![(lift x (a ^ n)).left, (lift x (a ^ 0)).left, (lift x a).left] ![1, -1, -n]),
      t.IsGen ∧ ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J → val t ρ.left z J =
        ∏ k ∈ Finset.range n, val β.law2 (lift (ρ ≫ x) (lift ((ρ ≫ a) ^ k) (ρ ≫ a))).left z J := by
  obtain ⟨t, ht, hv⟩ := exists_telescope β.isLB (fun k => (lift x (a ^ k)).left) (lift x a).left _ _
    (fun k => LB.pullGen P _ _ β.law2 (lift x (lift (a ^ k) a)).left)
    (fun k => DVR.pullGen_isGen _ _ _ _ β.isGen2 _) (fun k U _ h => by
      refine (prod_law₂ x (a ^ k) a h).trans ?_
      rw [pow_succ]) n
  refine ⟨t, ht, fun T' ρ z J hJ => (hv _ _ z J hJ).trans (Finset.prod_congr rfl fun k _ => ?_)⟩
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_lift, comp_lift, comp_pow']

theorem spread {T : Over S} (x y : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : ∀ (z : T.left) (J), Good P z J → ∏ k ∈ Finset.range n, val β.law1 (lift (x ^ k) (lift x y)).left z J =
      ∏ k ∈ Finset.range n, val β.law2 (lift x (lift (y ^ k) y)).left z J)
    (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J) (hJ : Good P z J) :
    ∏ k ∈ Finset.range n, val β.law1 (lift ((ρ ≫ x) ^ k) (lift (ρ ≫ x) (ρ ≫ y))).left z J =
      ∏ k ∈ Finset.range n, val β.law2 (lift (ρ ≫ x) (lift ((ρ ≫ y) ^ k) (ρ ≫ y))).left z J := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_first β x y n
  obtain ⟨t₂, g₂, v₂⟩ := exists_second β x y n
  rw [← v₁ T' ρ z J hJ, ← v₂ T' ρ z J hJ]
  refine gen_unique' β.isLB (fun U _ k => ?_) (𝟙 T.left) (𝟙 T.left) (Category.id_comp _)
    (fun a => ⟨a, by simp⟩) g₁ g₂ (fun w I hI => ?_) _ ρ.left z J hJ
  · rw [hx, hy]
    simp [Fin.prod_univ_succ]
  · have e₁ := v₁ T (𝟙 T) w I hI
    have e₂ := v₂ T (𝟙 T) w I hI
    simp only [Category.id_comp] at e₁ e₂
    exact e₁.trans ((h w I hI).trans e₂.symm)

theorem exists_sigma {T : Over S} (x a : T ⟶ G) (n : ℕ) (hx : x ^ n = 1) (ψ : T.left ⟶ (G ⊗ G).left)
    (hψ : ψ = (lift x (a ^ n)).left) :
    ∃ σ : LB.Gen (LB.LinComb P (K := PUnit) (fun _ => ψ) (fun _ => 1)), σ.IsGen ∧
      ∀ (T' : Over S) (ρ : T' ⟶ T) (z : T'.left) (J), Good P z J → val σ ρ.left z J =
        (∏ k ∈ Finset.range n, val β.law2 (lift (ρ ≫ x) (lift ((ρ ≫ a) ^ k) (ρ ≫ a))).left z J) *
          (∏ k ∈ Finset.range n, val β.law1 (lift ((ρ ≫ x) ^ k) (lift (ρ ≫ x) (ρ ≫ a))).left z J)⁻¹ *
          (val β.law2 (lift (ρ ≫ x) (lift (1 : T' ⟶ G) (1 : T' ⟶ G))).left z J)⁻¹ := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_first β x a n
  obtain ⟨t₂, g₂, v₂⟩ := exists_second β x a n
  obtain ⟨σ, hσ, hv⟩ := exists_gen β.isLB (K' := PUnit) (φ' := fun _ => ψ) (ε' := fun _ => 1) (fun U _ h => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 3 ⊕ Fin 3) (K' := ULift (Fin 3)) (U := U) _
        (DVR.prod_sum₂ (K := Fin 3) (K' := Fin 3) (U := U) _ rfl (DVR.prod_neg _ _ rfl))
        (DVR.prod_neg _ _ (prod_law₂ x 1 1 h))) ?_
      rw [hx, hψ]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      try module)
    (LB.mulGen P _ _ _ _ (LB.mulGen P _ _ _ _ t₂ (LB.invGen P _ _ t₁))
      (LB.invGen P _ _ (LB.pullGen P _ _ β.law2 (lift x (lift (1 : T ⟶ G) (1 : T ⟶ G))).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ g₂ (DVR.invGen_isGen _ _ _ _ g₁))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ β.isGen2 _)))
  refine ⟨σ, hσ, fun T' ρ z J hJ => ?_⟩
  refine (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (v₂ T' ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹) (v₁ T' ρ z J hJ)))))
    ((val_inv _ _).trans (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans ?_)))))
  rw [← Over.comp_left, comp_lift, comp_lift, MonObj.comp_one]

theorem main :
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (T : Over S) (z : T.left)
    (J : (T.left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J → ∀ t₁ t₂ : (T ⟶ G) → (T ⟶ G) → (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
    (∀ x x' y, t₁ x x' y = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift x (lift x' y)).left z J) → (∀ x y y', t₂ x y y' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift y y')).left z J) →
    (∀ x x' x'' y, t₁ (x * x') x'' y * t₁ x x' y = t₁ x (x' * x'') y * t₁ x' x'' y) ∧ (∀ x x' y, t₁ x x' y = t₁ x' x y) ∧
    (∀ x y y' y'', t₂ x (y * y') y'' * t₂ x y y' = t₂ x y (y' * y'') * t₂ x y' y'') ∧ (∀ x y y', t₂ x y y' = t₂ x y' y) ∧
    (∀ x x' y y', t₁ x x' (y * y') * t₂ x y y' * t₂ x' y y' = t₂ (x * x') y y' * t₁ x x' y * t₁ x x' y')) →
  (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (P : ReciprocityTheory.ChartRestriction.G.Semi.LB (G ⊗ G).left) (β : ReciprocityTheory.ChartRestriction.G.Semi.IsBiext G P) (x : Over.mk f ⟶ G), x ^ N = 1 →
    ∃ σ : ReciprocityTheory.ChartRestriction.G.Semi.LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.LB.LinComb P (K := PUnit) (fun _ => (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (fun _ => 1)), σ.IsGen ∧
      ∀ y : Over.mk f ⟶ G, y ^ N = 1 → (∀ (z : (Over.mk f).left) (J : ((Over.mk f).left ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law1 (lift (x ^ k) (lift x y)).left z J = ∏ k ∈ Finset.range N, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val β.law2 (lift x (lift (y ^ k) y)).left z J) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (G ⊗ Over.mk f).left) (z : Z) (J : (Z ⟶ (G ⊗ G).left) → P.1), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good P z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ (r ≫ (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) z J = ReciprocityTheory.ChartRestriction.G.Geo.Tor.val σ r z J) := by
  intro H S G _ _ K _ _ f N P β x hx
  obtain ⟨σ, hσ, hv⟩ := exists_sigma β (snd G (Over.mk f) ≫ x) (fst G (Over.mk f)) N
    (by rw [← comp_pow', hx, MonObj.comp_one])
    ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ≫ (lift (snd G (Over.mk f) ≫ x) (fst G (Over.mk f))).left) (by
      rw [← Over.comp_left, comp_lift, whiskerRight_fst, whiskerRight_snd_assoc, comp_pow', Category.comp_id])
  refine ⟨σ, hσ, fun y hy h Z r z J hJ => ?_⟩
  let T' : Over S := Over.mk (r ≫ (G ⊗ Over.mk f).hom)
  let ρ : T' ⟶ G ⊗ Over.mk f := Over.homMk r rfl
  have e₁ := hv T' (ρ ≫ lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))) z J hJ
  have e₂ := hv T' ρ z J hJ
  have a₁ : (ρ ≫ lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))) ≫ snd G (Over.mk f) ≫ x =
      (ρ ≫ snd G (Over.mk f)) ≫ x := by simp
  have a₂ : (ρ ≫ lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))) ≫ fst G (Over.mk f) =
      (ρ ≫ fst G (Over.mk f)) * ((ρ ≫ snd G (Over.mk f)) ≫ y) := by
    rw [Category.assoc, lift_fst, MonObj.comp_mul, Category.assoc]
  rw [a₁, a₂] at e₁
  rw [← Category.assoc] at e₂
  obtain ⟨-, -, c₃, c₄, c₅⟩ := H S G P β T' z J hJ (fun a b c => val β.law1 (lift a (lift b c)).left z J)
    (fun a b c => val β.law2 (lift a (lift b c)).left z J) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  refine e₁.trans (Eq.trans (congrArg (· * _) ?_) e₂.symm)
  exact ratio_translate (fun a b c : T' ⟶ G => val β.law1 (lift a (lift b c)).left z J)
    (fun a b c : T' ⟶ G => val β.law2 (lift a (lift b c)).left z J) c₃ c₄ c₅ ((ρ ≫ snd G (Over.mk f)) ≫ x)
    (ρ ≫ fst G (Over.mk f)) ((ρ ≫ snd G (Over.mk f)) ≫ y) N
    ((comp_pow' _ x N).symm.trans ((congrArg _ hx).trans (MonObj.comp_one _)))
    ((comp_pow' _ y N).symm.trans ((congrArg _ hy).trans (MonObj.comp_one _))) (spread β x y N hx hy h T' (ρ ≫ snd G (Over.mk f)) z J hJ)

end GlobalTheory.TorsionGen

end
