import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinProdIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumBil

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

def lamH {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U)
    (x y : T ⟶ B) : U :=
  h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left

theorem prod_lam {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U)
    (x y : T ⟶ B) (e : ℤ) : ∏ i : Fin 4, h (GlobalTheory.PolDeg.lamPts x y i) ^ (e * Oε i) = lamH h x y ^ e := by
  rw [Fin.prod_univ_four]
  show h (x * y).left ^ (e * 1) * h x.left ^ (e * -1) * h y.left ^ (e * -1) * h (1 : T ⟶ B).left ^ (e * 1) = _
  apply Additive.ofMul.injective
  simp only [lamH, ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem prod_lam₁ {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U)
    (x y : T ⟶ B) : ∏ i : Fin 4, h (GlobalTheory.PolDeg.lamPts x y i) ^ Oε i = lamH h x y := by
  simpa using prod_lam h x y 1

theorem prod_lam_neg {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U)
    (x y : T ⟶ B) (e : ℤ) : ∏ i : Fin 4, h (GlobalTheory.PolDeg.lamPts x y i) ^ (-(e * Oε i)) = (lamH h x y ^ e)⁻¹ := by
  rw [← prod_lam h x y e, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun i _ => zpow_neg _ _

theorem lamH_comm {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] {U : Type} [CommGroup U]
    (h : (T.left ⟶ B.left) → U) (x y : T ⟶ B) : lamH h x y = lamH h y x := by
  simp only [lamH, mul_comm x y]
  rw [mul_right_comm (h (y * x).left)]

theorem lamH_one {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U]
    (h : (T.left ⟶ B.left) → U) (y : T ⟶ B) : lamH h 1 y = 1 := by
  rw [lamH, _root_.one_mul, mul_right_comm (h y.left), mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem exists_cube (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (a b u : T ⟶ D.P.A) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (a * b) u)
      (Sum.elim (GlobalTheory.PolDeg.lamPts a u) (GlobalTheory.PolDeg.lamPts b u)))
      (Sum.elim Oε (Sum.elim (fun i => -(1 * Oε i)) (fun i => -(1 * Oε i))))), t.IsGen ∧
    ∀ (ρ : TK R ⟶ T) (α β c : D.X), ρ ≫ a = DVR.cP D (TK R) α → ρ ≫ b = DVR.cP D (TK R) β →
      ρ ≫ u = DVR.cP D (TK R) c → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val t ρ.left z J = (val (D.tau (α + β) c) (𝟙 _) z J)⁻¹ *
        (val (D.tau α c) (𝟙 _) z J * val (D.tau β c) (𝟙 _) z J) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K' := Fin 4 ⊕ (Fin 4 ⊕ Fin 4))
    (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (a * b) u) (Sum.elim (GlobalTheory.PolDeg.lamPts a u) (GlobalTheory.PolDeg.lamPts b u)))
    (ε' := Sum.elim Oε (Sum.elim (fun i => -(1 * Oε i)) (fun i => -(1 * Oε i)))) (fun U _ h => by
      refine (prod_cub a b u h).trans ?_
      rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [prod_lam₁, prod_lam_neg, prod_lam_neg]
      apply Additive.ofMul.injective
      simp only [lamH, ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one]
      abel)
    (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift b u)).left)
    (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _)
  refine ⟨t, ht, fun ρ α β c ha hb hu z J hJ => ?_⟩
  rw [hv _ _ z J hJ, val_cub D.cub ρ hJ, ha, hb, hu]
  exact eq_inv_mul_of_mul_eq (DVR.tauK_mul hJ hB α β c)

theorem prodNeg {K : Type} [Fintype K] {U : Type} [CommGroup U] (f : K → U) (ε : K → ℤ) :
    ∏ k, f k ^ (-ε k) = (∏ k, f k ^ ε k)⁻¹ := by
  rw [← Finset.prod_inv_distrib]; exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem tau_zero (hB : D.TauBimult) {z : (TK R).left} {J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) (b : D.X) : val (D.tau 0 b) (𝟙 _) z J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) z J) := isCub_cubV D.cub hJ
  have t := DVR.tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact (mul_eq_left.1 t.symm)

theorem exists_powN (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (x u : T ⟶ D.P.A) (k : ℕ) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (x ^ k) u) (GlobalTheory.PolDeg.lamPts x u))
      (Sum.elim Oε (fun i => -((k : ℤ) * Oε i)))), t.IsGen ∧
    ∀ (ρ : TK R ⟶ T) (y b : D.X), ρ ≫ x = DVR.cP D (TK R) y → ρ ≫ u = DVR.cP D (TK R) b →
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val t ρ.left z J = (val (D.tau (k • y) b) (𝟙 _) z J)⁻¹ * val (D.tau y b) (𝟙 _) z J ^ k := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_cubN D.cub (1 : T ⟶ D.P.A) x u k
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K' := Fin 4 ⊕ Fin 4)
    (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (x ^ k) u) (GlobalTheory.PolDeg.lamPts x u))
    (ε' := Sum.elim Oε (fun i => -((k : ℤ) * Oε i))) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [prod_lam₁, prod_lam_neg]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.one_mul,
        _root_.mul_one]
      apply Additive.ofMul.injective
      simp only [lamH, ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one]
      module) t₀ ht₀
  refine ⟨t, ht, fun ρ y b hx hu z J hJ => ?_⟩
  rw [hv _ _ z J hJ, hv₀ _ _ z J hJ, MonObj.comp_one, hx, hu]
  exact eq_inv_mul_of_mul_eq (DVR.tauK_nsmul hJ hB y b k)

def cPm (T : Over (Spec (CommRingCat.of R))) : D.X →+ Additive (T ⟶ D.P.A) where
  toFun a := Additive.ofMul (DVR.cP D T a)
  map_zero' := by rw [cPoint_zero]; rfl
  map_add' a b := by rw [DVR.cPoint_add]; rfl

theorem cPoint_zsmul (T : Over (Spec (CommRingCat.of R))) (n : ℤ) (a : D.X) : DVR.cP D T (n • a) = DVR.cP D T a ^ n :=
  congrArg Additive.toMul (map_zsmul (cPm T) n a)

theorem cPoint_sum (T : Over (Spec (CommRingCat.of R))) {κ : Type} (s : Finset κ) (f : κ → D.X) :
    DVR.cP D T (∑ k ∈ s, f k) = ∏ k ∈ s, DVR.cP D T (f k) :=
  congrArg Additive.toMul (map_sum (cPm T) f s)

theorem comp_zpow {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) (n : ℤ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := map_zpow (preHom ρ) x n

theorem comp_prod {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S} (ρ : T' ⟶ T) {κ : Type}
    (s : Finset κ) (x : κ → (T ⟶ G)) : ρ ≫ ∏ k ∈ s, x k = ∏ k ∈ s, ρ ≫ x k := map_prod (preHom ρ) x s

theorem exists_powZ (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (x u : T ⟶ D.P.A) (m : ℤ) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (x ^ m) u) (GlobalTheory.PolDeg.lamPts x u))
      (Sum.elim Oε (fun i => -(m * Oε i)))), t.IsGen ∧
    ∀ (ρ : TK R ⟶ T) (y b : D.X), ρ ≫ x = DVR.cP D (TK R) y → ρ ≫ u = DVR.cP D (TK R) b →
      ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J → val t ρ.left z J = (val (D.tau (m • y) b) (𝟙 _) z J)⁻¹ * val (D.tau y b) (𝟙 _) z J ^ m := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · obtain ⟨t, ht, hv⟩ := exists_powN hB x u k
    rw [zpow_natCast]
    refine ⟨t, ht, fun ρ y b hx hu z J hJ => ?_⟩
    rw [hv ρ y b hx hu z J hJ, natCast_zsmul, zpow_natCast]
  · obtain ⟨c, hc, hcv⟩ := exists_cube hB (x ^ (-(k : ℤ))) (x ^ k) u
    obtain ⟨p, hp, hpv⟩ := exists_powN hB x u k
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K' := Fin 4 ⊕ Fin 4)
      (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (x ^ (-(k : ℤ))) u) (GlobalTheory.PolDeg.lamPts x u))
      (ε' := Sum.elim Oε (fun i => -(-(k : ℤ) * Oε i))) (fun U _ h => by
        have e : x ^ (-(k : ℤ)) * x ^ k = 1 := by rw [zpow_neg, zpow_natCast, inv_mul_cancel]
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, prodNeg, prod_lam₁, prod_lam, prod_lam_neg, e, lamH_one]
        apply Additive.ofMul.injective
        simp only [lamH, ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one, ofMul_one]
        module)
      (LB.mulGen D.P.L _ _ _ _ (LB.invGen D.P.L _ _ c) (LB.invGen D.P.L _ _ p))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ hc) (DVR.invGen_isGen _ _ _ _ hp))
    refine ⟨t, ht, fun ρ y b hx hu z J hJ => ?_⟩
    have h₁ : ρ ≫ x ^ (-(k : ℤ)) = DVR.cP D (TK R) ((-(k : ℤ)) • y) := by rw [comp_zpow, hx, cPoint_zsmul]
    have h₂ : ρ ≫ x ^ k = DVR.cP D (TK R) (k • y) := by rw [DVR.cPoint_nsmul, ← hx]; exact map_pow (preHom ρ) x k
    rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_inv, hcv ρ _ _ b h₁ h₂ hu z J hJ, hpv ρ y b hx hu z J hJ]
    have e₀ : (-(k : ℤ)) • y + k • y = 0 := by rw [neg_smul, natCast_zsmul, neg_add_cancel]
    rw [e₀, tau_zero hB hJ, zpow_neg, zpow_natCast]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
    abel

theorem comp_combo {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) {r : ℕ} (p : Fin r → (T ⟶ D.P.A))
    (m : Fin r → ℤ) (y : Fin r → D.X) (hp : ∀ k, ρ ≫ p k = DVR.cP D T' (y k)) :
    ρ ≫ ∏ k, p k ^ m k = DVR.cP D T' (∑ k, m k • y k) := by
  rw [comp_prod, cPoint_sum]
  exact Finset.prod_congr rfl fun k _ => by rw [comp_zpow, hp, cPoint_zsmul]

theorem exists_generator_lambda_linear_first_position (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} : ∀ {r : ℕ} (p : Fin r → (T ⟶ D.P.A))
    (m : Fin r → ℤ) (u : T ⟶ D.P.A),
    ∃ t : LB.Gen (LB.LinComb D.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) u)
      (fun q : Fin r × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1) u q.2)) (Sum.elim Oε (fun q : Fin r × Fin 4 => -(m q.1 * Oε q.2)))),
      t.IsGen ∧ ∀ (ρ : TK R ⟶ T) (y : Fin r → D.X) (b : D.X), (∀ k, ρ ≫ p k = DVR.cP D (TK R) (y k)) →
        ρ ≫ u = DVR.cP D (TK R) b → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι),
        Good D.P.L z J → val t ρ.left z J =
          (val (D.tau (∑ k, m k • y k) b) (𝟙 _) z J)⁻¹ * ∏ k, val (D.tau (y k) b) (𝟙 _) z J ^ m k := by
  intro r
  induction r with
  | zero =>
    intro p m u
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K' := Fin 4 ⊕ (Fin 0 × Fin 4))
      (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) u) (fun q : Fin 0 × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1) u q.2))
      (ε' := Sum.elim Oε (fun q : Fin 0 × Fin 4 => -(m q.1 * Oε q.2))) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, prod_lam₁, Finset.univ_eq_empty, Finset.prod_empty, lamH_one,
          _root_.mul_one])
      (LB.oneGen D.P.L (Y := T.left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    refine ⟨t, ht, fun ρ y b _ _ z J hJ => ?_⟩
    rw [hv _ _ z J hJ, val_one]
    rw [Fin.sum_univ_zero, Fin.prod_univ_zero, tau_zero hB hJ, inv_one, _root_.mul_one]
  | succ r ih =>
    intro p m u
    obtain ⟨c, hc, hcv⟩ := exists_cube hB (p 0 ^ m 0) (∏ k : Fin r, p k.succ ^ m k.succ) u
    obtain ⟨a, ha, hav⟩ := exists_powZ hB (p 0) u (m 0)
    obtain ⟨i, hi, hiv⟩ := ih (fun k => p k.succ) (fun k => m k.succ) u
    obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (K' := Fin 4 ⊕ (Fin (r + 1) × Fin 4))
      (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) u)
        (fun q : Fin (r + 1) × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1) u q.2))
      (ε' := Sum.elim Oε (fun q : Fin (r + 1) × Fin 4 => -(m q.1 * Oε q.2))) (fun U _ h => by
        simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, prodNeg, prod_lam₁,
          prod_lam, prod_lam_neg]
        simp only [Fin.prod_univ_succ]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one, ofMul_prod]
        module)
      (LB.mulGen D.P.L _ _ _ _ c (LB.mulGen D.P.L _ _ _ _ a i))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ hc (DVR.mulGen_isGen _ _ _ _ _ _ _ ha hi))
    refine ⟨t, ht, fun ρ y b hp hu z J hJ => ?_⟩
    have h₀ : ρ ≫ p 0 ^ m 0 = DVR.cP D (TK R) (m 0 • y 0) := by rw [comp_zpow, hp, cPoint_zsmul]
    have h₁ := comp_combo ρ (fun k : Fin r => p k.succ) (fun k => m k.succ) (fun k => y k.succ) (fun k => hp k.succ)
    rw [hv _ _ z J hJ, val_mul hJ, val_mul hJ, hcv ρ _ _ b h₀ h₁ hu z J hJ, hav ρ (y 0) b (hp 0) hu z J hJ,
      hiv ρ (fun k => y k.succ) b (fun k => hp k.succ) hu z J hJ, Fin.sum_univ_succ, Fin.prod_univ_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

theorem prod_lam_mneg {S : Scheme.{0}} {B T : Over S} [GrpObj B] {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U)
    (x y : T ⟶ B) (e f : ℤ) : ∏ i : Fin 4, h (GlobalTheory.PolDeg.lamPts x y i) ^ (e * -(f * Oε i)) = (lamH h x y ^ (e * f))⁻¹ := by
  rw [← prod_lam_neg h x y (e * f)]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_neg, _root_.mul_assoc]

theorem formKey {U A : Type} [CommGroup U] {r : ℕ} (f : A → A → U) (hsym : ∀ x y, f x y = f y x) (P Q : A)
    (p : Fin r → A) (m n : Fin r → ℤ) :
    f P Q * (∏ k, (f (p k) Q ^ m k)⁻¹) *
      ∏ k, (f Q (p k) ^ m k * ∏ l, (f (p l) (p k) ^ (m k * n l))⁻¹) =
    f P Q * ∏ k, ∏ l, (f (p k) (p l) ^ (m k * n l))⁻¹ := by
  rw [_root_.mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hsym Q (p k), inv_mul_cancel_left]
  exact Finset.prod_congr rfl fun l _ => by rw [hsym (p l) (p k)]

theorem valKey {U : Type} [CommGroup U] {r : ℕ} (F G' : Fin r → U) (H : Fin r → Fin r → U) (m n : Fin r → ℤ)
    (hG : ∀ k, G' k = F k) (hH : ∀ k l, H l k = H k l) :
    (∏ k, F k ^ m k) * ∏ k, ((G' k)⁻¹ * ∏ l, H l k ^ n l) ^ m k = ∏ k, ∏ l, H k l ^ (m k * n l) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hG, mul_zpow, inv_zpow', ← _root_.mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, _root_.one_mul, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun l _ => by rw [hH, ← zpow_mul, mul_comm (n l)]

end GlobalTheory.MumBil

namespace GlobalTheory.MumBil
open GlobalTheory.MumSide in

theorem lam_bilin : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (T : Over (Spec (CommRingCat.of R))) {r : ℕ} (p : Fin r → (T ⟶ D.toPre.P.A)) (m n : Fin r → ℤ), ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) (∏ l, p l ^ n l)) (fun q : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1.1) (p q.1.2) q.2)) (Sum.elim Oε (fun q : (Fin r × Fin r) × Fin 4 => -(m q.1.1 * n q.1.2 * Oε q.2)))), t.IsGen ∧ ∀ (ρ : TK R ⟶ T) (y : Fin r → D.toPre.X), (∀ k, ρ ≫ p k = toUnit (TK R) ≫ D.toPre.c (y k)) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t ρ.left z J = (val (D.toPre.tau (∑ k, m k • y k) (∑ l, n l • y l)) (𝟙 _) z J)⁻¹ * ∏ k, ∏ l, val (D.toPre.tau (y k) (y l)) (𝟙 _) z J ^ (m k * n l) := by
  intro R _ _ I D T r p m n
  have hB := D.tau_bimult
  obtain ⟨g, hg, hgv⟩ := exists_generator_lambda_linear_first_position hB p m (∏ l, p l ^ n l)
  have hk := fun k => exists_generator_lambda_linear_first_position hB p n (p k)
  choose s hs hsv using hk
  have hz := fun k => exists_zpow D.toPre.P.isLB (s k) (hs k) (m k)
  choose w hw hwv using hz
  obtain ⟨t, ht, hv⟩ := exists_gen D.toPre.P.isLB (K' := Fin 4 ⊕ ((Fin r × Fin r) × Fin 4))
    (φ' := Sum.elim (GlobalTheory.PolDeg.lamPts (∏ k, p k ^ m k) (∏ l, p l ^ n l))
      (fun q : (Fin r × Fin r) × Fin 4 => GlobalTheory.PolDeg.lamPts (p q.1.1) (p q.1.2) q.2))
    (ε' := Sum.elim Oε (fun q : (Fin r × Fin r) × Fin 4 => -(m q.1.1 * n q.1.2 * Oε q.2))) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, prod_lam₁, prod_lam,
        prod_lam_neg, prod_lam_mneg]
      exact formKey _ (lamH_comm h) _ _ _ _ _)
    (LB.mulGen D.toPre.P.L _ _ _ _ g (GeneratorPullback.finProdGen D.toPre.P.L _ _ w))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hg (finProd_isGen _ _ w hw))
  refine ⟨t, ht, fun ρ y hp z J hJ => ?_⟩
  have hQ := comp_combo ρ p n y hp
  rw [hv _ _ z J hJ, val_mul hJ, val_finProd _ _ _ _ _ hJ, hgv ρ y _ hp hQ z J hJ]
  simp only [fun k => hwv k _ ρ.left z J hJ, fun k => hsv k ρ y (y k) hp (hp k) z J hJ]
  rw [_root_.mul_assoc]
  congr 1
  exact valKey _ _ _ m n (fun k => DVR.tauK_symm hJ _ _) (fun k l => DVR.tauK_symm hJ _ _)

end GlobalTheory.MumBil
