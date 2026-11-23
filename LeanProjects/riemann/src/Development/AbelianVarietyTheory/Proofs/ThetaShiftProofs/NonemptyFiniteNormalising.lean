import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

theorem exists_ratio {F : Type} [Field F] {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Sp F ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp F ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ x : Fˣ, ∀ y J, Good L y J → val t (𝟙 _) y J = unitAt (𝟙 _) y x * val t' (𝟙 _) y J := by
  let y : Sp F := IsLocalRing.closedPoint F
  choose I hI using fun q : Sp F ⟶ X => exists_chart hL (q y)
  refine ⟨(stalkUnits y).symm (val t (𝟙 _) y I * (val t' (𝟙 _) y I)⁻¹), fun y' J hJ => ?_⟩
  obtain rfl : y = y' := Subsingleton.elim (α := PrimeSpectrum F) y y'
  refine (val_eq_of_val_eq hF ht (scaleGen_isGen _ _ ht') hI hJ (Eq.trans ?_ (val_scale _ t' _ hI).symm)).trans
    (val_scale _ t' _ hJ)
  rw [unitAt_apply, gm_unitOn, MulEquiv.apply_symm_apply, inv_mul_cancel_right]

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

section Values

variable {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem val_tau_symm (a b : D.X) : val (D.tau a b) κ.left z J = val (D.tau b a) κ.left z J := by
  rw [val_tau D a b _ hJ, val_tau D b a _ hJ, add_comm b a, mul_right_comm (val (D.psi (a + b)) _ z J)]

variable (hB : D.TauBimult)
include hB

theorem val_tau_add (a a' b : D.X) :
    val (D.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (D.tau a b) κ.left z J * val (D.tau a' b) κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) κ.left).trans (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

theorem val_tau_nsmul (k : ℕ) (a b : D.X) :
    val (D.tau (k • a) b) κ.left z J * cubN (th D z J) k 1 (cP D T a) (cP D T b) = val (D.tau a b) κ.left z J ^ k := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  induction k with
  | zero =>
    have e := val_tau_add κ hJ hB 0 0 b
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at e
    rw [zero_nsmul, pow_zero, mul_eq_left.1 e.symm]
    exact _root_.mul_one _
  | succ k ih =>
    have e := val_tau_add κ hJ hB (k • a) a b
    rw [cPoint_nsmul] at e
    rw [succ_nsmul, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, _root_.one_mul, e, pow_succ,
      ← ih, cubN, mul_right_comm]

end Values

variable (D) in

def canφ (y y' : D.X) : Fin 4 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left) :=
  ![(D.c y * D.c y').left, (D.c y).left, (D.c y').left, (1 : 𝟙_ (Over (Sp R)) ⟶ D.P.A).left]

def canε (n : ℕ) : Fin 4 → ℤ := ![-(n ^ 2 : ℕ), (n ^ 2 : ℕ), (n ^ 2 : ℕ), -(n ^ 2 : ℕ)]

variable {n : ℕ} (hc : ∀ y, D.c y ^ n = 1)
include hc

theorem exists_canGen (y y' : D.X) : ∃ t : LB.Gen (LB.LinComb D.P.L (canφ D y y') (canε n)), t.IsGen ∧
    ∀ (T : Over (Sp R)) (z : T.left) (J), Good D.P.L z J →
      val t (toUnit T).left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub 1 (D.c y) (D.c y') n
  obtain ⟨t', ht', hv'⟩ := exists_gen D.P.isLB (φ' := canφ D y y') (ε' := canε n) (fun U _ h => by
      rw [hc y]
      apply Additive.ofMul.injective
      simp [canφ, canε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module) (GeneratorPullback.powGen D.P.L _ _ t n) (powGen_isGen _ _ _ _ ht n)
  refine ⟨t', ht', fun T z J hJ => (hv' _ _ z J hJ).trans ((val_powGen _ _ _ _ _).trans (congrArg (· ^ n) ?_))⟩
  refine (hv T (toUnit T) z J hJ).trans ?_
  rw [MonObj.comp_one]
  rfl

def canGen (y y' : D.X) : LB.Gen (LB.LinComb D.P.L (canφ D y y') (canε n)) := (exists_canGen hc y y').choose

theorem val_canGen (y y' : D.X) (T : Over (Sp R)) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (canGen hc y y') (toUnit T).left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n :=
  (exists_canGen hc y y').choose_spec.2 T z J hJ

def canK (y y' : D.X) := LB.pullGen D.P.L _ _ (canGen hc y y') (toUnit (TK R)).left

theorem val_canK (y y' : D.X) {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (canK hc y y') κ.left z J = cubN (th D z J) n 1 (cP D T y) (cP D T y') ^ n := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [← Over.comp_left, comp_toUnit]
  exact val_canGen hc y y' T hJ

theorem cPoint_nsmul_eq_one (T : Over (Sp R)) (y : D.X) : cP D T (n • y) = 1 := by
  rw [cPoint_nsmul, cP, ← MonObj.comp_pow, hc, MonObj.comp_one]

theorem val_tau_pow (hB : D.TauBimult) (a b : D.X) {T : Over (Sp R)} (κ : T ⟶ TK R) {z : T.left} {J}
    (hJ : Good D.P.L z J) :
    val (D.tau a b) κ.left z J ^ n ^ 2 = val (D.tau (n • a) (n • b)) κ.left z J * val (canK hc a b) κ.left z J := by
  have C : IsCub (th D (T := T) z J) := isCub_cubV D.cub hJ
  have e := val_tau_nsmul κ hJ hB n b (n • a)
  rw [cPoint_nsmul_eq_one hc, C.N_one, _root_.mul_one, val_tau_symm κ hJ, val_tau_symm κ hJ b] at e
  rw [val_canK hc a b κ hJ, e, ← mul_pow, val_tau_nsmul κ hJ hB, ← pow_mul, sq]

theorem exists_tau_const (a b : D.X) : ∃ x : (FractionRing R)ˣ, ∀ y J, Good D.P.L y J →
    val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) y J = unitAt (𝟙 (TK R).left) y x := by
  obtain ⟨x, hx⟩ := exists_ratio (F := FractionRing R) D.P.isLB (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    have a₁ : ∀ w : D.X, ptK (D.c (n • w)) = (1 : TK R ⟶ D.P.A).left := fun w =>
      congrArg (fun q => q.left) (cPoint_nsmul_eq_one hc (TK R) w)
    have a₀ : (toUnit (TK R)).left ≫ eSec D.P.A = (1 : TK R ⟶ D.P.A).left := rfl
    simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one,
      ← nsmul_add, a₁, a₀, Fintype.prod_empty]
    simp) (tau_isGen D (n • a) (n • b)) oneGen_isGen
  exact ⟨x, fun y J hJ => (hx y J hJ).trans ((congrArg₂ (· * ·) rfl (val_one _)).trans (_root_.mul_one _))⟩

def kappa (a b : D.X) : (FractionRing R)ˣ := (exists_tau_const hc a b).choose

theorem unitAt_kappa (a b : D.X) {y : (TK R).left} {J} (hJ : Good D.P.L y J) :
    unitAt (𝟙 (TK R).left) y (kappa hc a b) = val (D.tau (n • a) (n • b)) (𝟙 (TK R).left) y J :=
  ((exists_tau_const hc a b).choose_spec y J hJ).symm

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]

end GlobalTheory.TauTwist
