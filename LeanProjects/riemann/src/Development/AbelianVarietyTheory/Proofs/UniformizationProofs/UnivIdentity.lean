import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.SymFrame

section Rep
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)

def GRep (P : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ X) → L.ι), (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (s : LB.Gen (LB.LinComb L φ ε)), s.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = P U h) ∧
    ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → val s r.left z J = v T r z J

variable {L Y}

theorem GRep.mul {P P' v v'} (h : GRep L Y P v) (h' : GRep L Y P' v') :
    GRep L Y (fun U _ h => P U h * P' U h) (fun T r z J => v T r z J * v' T r z J) := by
  obtain ⟨K, _, φ, ε, s, hs, hP, hv⟩ := h
  obtain ⟨K', _, φ', ε', s', hs', hP', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ s s', mulGen_isGen _ _ _ _ _ _ _ hs hs',
    fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · exact prod_sum₂ _ (hP U h) (hP' U h)
  · rw [val_mul hJ, hv T r z J hJ, hv' T r z J hJ]

theorem GRep.inv {P v} (h : GRep L Y P v) :
    GRep L Y (fun U _ h => (P U h)⁻¹) (fun T r z J => (v T r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, s, hs, hP, hv⟩ := h
  exact ⟨K, inferInstance, _, _, LB.invGen L _ _ s, invGen_isGen _ _ _ _ hs,
    fun U _ h => prod_neg _ _ (hP U h), fun T r z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (hv T r z J hJ))⟩

theorem GRep.pow {P v} (h : GRep L Y P v) (n : ℕ) :
    GRep L Y (fun U _ h => P U h ^ n) (fun T r z J => v T r z J ^ n) := by
  obtain ⟨K, _, φ, ε, s, hs, hP, hv⟩ := h
  refine ⟨K, inferInstance, _, _, GeneratorPullback.powGen L _ _ s n, powGen_isGen _ _ _ _ hs n,
    fun U _ h => ?_, fun T r z J hJ => (map_pow _ _ _).trans (congrArg (· ^ n) (hv T r z J hJ))⟩
  show _ = P U h ^ n
  rw [← hP U h, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun k _ => by rw [mul_comm, zpow_mul, zpow_natCast]

theorem GRep.congr {P P' v v'} (h : GRep L Y P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = P' U h)
    (hv : ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → v T r z J = v' T r z J) : GRep L Y P' v' := by
  obtain ⟨K', _, φ', ε', s', hs', hP', hv'⟩ := h
  exact ⟨K', inferInstance, φ', ε', s', hs', fun U _ h => (hP' U h).trans (hP U h),
    fun T r z J hJ => (hv' T r z J hJ).trans (hv T r z J hJ)⟩

theorem GRep.out (hL : L.IsLB) {P v} (h : GRep L Y P v) {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = ∏ k, h (φ k) ^ ε k) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J →
      val s r.left z J = v T r z J := by
  obtain ⟨K', _, φ', ε', s', hs', hP', hv'⟩ := h
  obtain ⟨s, hs, vs⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => (hP' U h).trans (hP U h)) s' hs'
  exact ⟨s, hs, fun T r z J hJ => (vs _ _ z J hJ).trans (hv' T r z J hJ)⟩

theorem grep_gen {Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (q : Y.left ⟶ Y') :
    GRep L Y (fun _ _ h => ∏ k, h (q ≫ φ k) ^ ε k) (fun _ r z J => val t (r.left ≫ q) z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t q, pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

end Rep

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}

theorem eta_eq : (η[D.P.A]) = (1 : 𝟙_ _ ⟶ D.P.A) := by simp [Hom.one_def]

theorem normd_iff {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (u : LB.Gen (LB.LinComb D.P.L φ ε)) :
    Normd u ↔ u.IsGen ∧ ∀ y J, Good D.P.L y J → val u (eSec D.P.A) y J = 1 :=
  and_congr Iff.rfl ⟨fun h y J hJ => by
      have := val_corr hJ h (𝟙 _)
      rwa [val_pull hJ, Category.id_comp, val_one] at this,
    fun h => corr_of_val D.P.isLB fun y J hJ => by rw [val_pull hJ, Category.id_comp, val_one]; exact h y J hJ⟩

theorem normd_one {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) {T : Over (Spec (CommRingCat.of R))} {z : T.left} {J}
    (hJ : Good D.P.L z J) : val u (1 : T ⟶ D.P.A).left z J = 1 :=
  (val_pull hJ u (eSec D.P.A) T.hom).symm.trans ((val_corr hJ hu.2 _).trans (val_one _))

theorem normd_unique (hG : GlobalFnsSt) {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    {u u' : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (hu' : Normd u') {Z : Scheme.{0}} (r : Z ⟶ D.P.A.left) (z : Z) (J)
    (hJ : Good D.P.L z J) : val u r z J = val u' r z J :=
  gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1 hu'.1
    (fun y I hI => (((normd_iff u).1 hu).2 y I hI).trans (((normd_iff u').1 hu').2 y I hI).symm) _ r z J hJ

theorem GRep.normd {P v} (h : GRep D.P.L D.P.A P v) {K : Type} [Fintype K] (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), P U h = ∏ k, h (φ k) ^ ε k)
    (h₁ : ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1) :
    ∃ s : LB.Gen (LB.LinComb D.P.L φ ε), Normd s ∧ ∀ (T : Over _) (r : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
      val s r.left z J = v T r z J := by
  obtain ⟨s, hs, vs⟩ := h.out D.P.isLB φ ε hP
  refine ⟨s, (normd_iff s).2 ⟨hs, fun y J hJ => (vs _ η[D.P.A] y J hJ).trans ?_⟩, vs⟩
  rw [eta_eq]; exact h₁ y J hJ

theorem GRep.triv (hG : GlobalFnsSt) {P v} (h : GRep D.P.L D.P.A P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U), P U h = 1)
    (h₁ : ∀ y J, Good D.P.L y J → v (𝟙_ _) 1 y J = 1) (T : Over _) (r : T ⟶ D.P.A) (z : T.left) (J)
    (hJ : Good D.P.L z J) : v T r z J = 1 := by
  obtain ⟨s, hs, vs⟩ := h.normd (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun U _ h => (hP U h).trans (Fintype.prod_empty _).symm) h₁
  have h1 : Normd (D := D) (LB.oneGen D.P.L) := (normd_iff _).2
    ⟨fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
      fun _ _ _ => val_one _⟩
  exact (vs T r z J hJ).symm.trans ((normd_unique hG hs h1 _ z J hJ).trans (val_one _))

theorem left_pow (x : Y ⟶ D.P.A) (n : ℕ) : x.left ≫ (𝟙 D.P.A ^ n).left = (x ^ n).left :=
  congrArg (fun q : Y ⟶ D.P.A => q.left) ((map_pow (preHom x) _ _).trans (congrArg (· ^ n) (Category.comp_id x)))

theorem left_one (x : Y ⟶ D.P.A) : x.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : Y ⟶ D.P.A).left :=
  congrArg (fun q : Y ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) x)

theorem grep_kap {n : ℕ} (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)) (hκ : κ.IsGen) (x : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h x.left ^ ((n : ℤ) ^ 2) * (h (x ^ n).left)⁻¹ * h (1 : Y ⟶ D.P.A).left ^ (1 - (n : ℤ) ^ 2))
      (fun _ r z J => val κ (r ≫ x).left z J) :=
  (grep_gen κ hκ x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_three]
    show h (x.left ≫ 𝟙 _) ^ ((n ^ 2 : ℕ) : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-((1 : ℕ) : ℤ)) *
      h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)) = _
    rw [Category.comp_id, left_pow, left_one, Nat.cast_pow, Nat.cast_one, zpow_neg_one]) (fun _ _ _ _ _ => rfl)

abbrev nuLB (D : DegPre R) (N : ℕ) : LB D.P.A.left := LB.LinComb D.P.L (K := Fin 4)
  ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
  ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]

theorem grep_nu {n : ℕ} (ν : LB.Gen (nuLB D n)) (hν : ν.IsGen) (x : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h (x ^ n * x).left * (h (x ^ n).left)⁻¹ * h x.left ^ (-(2 * (n : ℤ) + 1)) *
      h (1 : Y ⟶ D.P.A).left ^ (2 * (n : ℤ) + 1)) (fun _ r z J => val ν (r ≫ x).left z J) :=
  (grep_gen ν hν x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_four]
    show h (x.left ≫ (𝟙 D.P.A ^ (n + 1)).left) ^ (1 : ℤ) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-1 : ℤ) *
      h (x.left ≫ 𝟙 _) ^ (-(2 * (n : ℤ) + 1)) * h (x.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ (2 * (n : ℤ) + 1) = _
    rw [Category.comp_id, left_pow, left_pow, left_one, zpow_neg_one, zpow_one, pow_succ]) (fun _ _ _ _ _ => rfl)

theorem exists_kap [IsNoetherianRing R] (hM : MulPullSt) (n : ℕ) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1), Normd κ := by
  obtain ⟨α, hα⟩ := hM _ D.P n
  have ra : ∀ x : D.P.A ⟶ D.P.A, GRep D.P.L D.P.A (fun _ _ h => h x.left ^ ((n : ℤ) ^ 2) * (h (x ^ n).left)⁻¹)
      (fun _ r z J => val α (r ≫ x).left z J) := fun x => (grep_gen α hα x.left).congr (fun _ _ h => by
    rw [Fin.prod_univ_two]
    show h (x.left ≫ 𝟙 _) ^ ((n : ℤ) ^ 2) * h (x.left ≫ (𝟙 D.P.A ^ n).left) ^ (-1 : ℤ) = _
    rw [Category.comp_id, left_pow, zpow_neg_one]) (fun _ _ _ _ _ => rfl)
  obtain ⟨s, hs, -⟩ := ((ra (𝟙 _)).mul (ra 1).inv).normd
    ![𝟙 _, (𝟙 D.P.A ^ n).left, (1 : D.P.A ⟶ D.P.A).left] ![((n ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - ((n ^ 2 : ℕ) : ℤ)]
    (fun U _ h => by
      rw [Fin.prod_univ_three, one_pow]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, MonObj.comp_one, mul_inv_cancel])
  exact ⟨s, hs⟩

theorem exists_nu [IsNoetherianRing R] (hM : MulPullSt) (n : ℕ) : ∃ ν : LB.Gen (nuLB D n), Normd ν := by
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) hM n
  obtain ⟨κ', hκ'⟩ := exists_kap (D := D) hM (n + 1)
  obtain ⟨s, hs, -⟩ := ((grep_kap κ hκ.1 (𝟙 _)).mul (grep_kap κ' hκ'.1 (𝟙 _)).inv).normd
    ![(𝟙 D.P.A ^ (n + 1)).left, (𝟙 D.P.A ^ n).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
    ![1, -1, -(2 * (n : ℤ) + 1), 2 * (n : ℤ) + 1]
    (fun U _ h => by
      rw [Fin.prod_univ_four]
      apply Additive.ofMul.injective
      simp [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hκ hJ, normd_one hκ' hJ, mul_inv_cancel])
  exact ⟨s, hs⟩

theorem comp_id_pow (x : Y ⟶ D.P.A) (n : ℕ) : x ≫ 𝟙 D.P.A ^ n = x ^ n :=
  (map_pow (preHom x) _ _).trans (congrArg (· ^ n) (Category.comp_id x))

theorem grep_cub (x x' y : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
        h x.left * h x'.left * h y.left * (h (1 : Y ⟶ D.P.A).left)⁻¹)
      (fun _ r z J => cubV D.cub z J (r ≫ x) (r ≫ x') (r ≫ y)) :=
  (grep_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t D.cub.isGen (lift x (lift x' y)).left).congr
    (fun _ _ h => prod_cub x x' y h)
    (fun _ r z J _ => by rw [← Over.comp_left, comp_lift, comp_lift]; rfl)

theorem grep_sym (y : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h (y⁻¹).left * (h y.left)⁻¹) (fun _ r z J => val D.sym (r ≫ y).left z J) :=
  (grep_gen D.sym D.sym_gen y.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show h (y⁻¹).left ^ (1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (-1 : ℤ) = _
      rw [Category.comp_id, zpow_one, zpow_neg_one])
    (fun _ _ _ _ _ => rfl)

theorem grep_cubN (m x : Y ⟶ D.P.A) (k : ℕ) :
    GRep D.P.L Y (fun _ _ h => h (m ^ k * x).left * (h (m ^ k).left)⁻¹ * (h x.left)⁻¹ * h (1 : Y ⟶ D.P.A).left *
        (h (m * x).left ^ k)⁻¹ * h m.left ^ k * h x.left ^ k * (h (1 : Y ⟶ D.P.A).left ^ k)⁻¹)
      (fun _ r z J => cubN (cubV D.cub z J) k 1 (r ≫ m) (r ≫ x)) := by
  obtain ⟨t, ht, vt⟩ := exists_cubN D.cub 1 m x k
  refine ⟨_, inferInstance, _, _, t, ht, fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · rw [Fin.prod_univ_eight]
    simp
  · rw [vt T r z J hJ, MonObj.comp_one]

theorem univ_identity (hG : GlobalFnsSt) {N : ℕ} {ν : LB.Gen (nuLB D N)} (hν : Normd ν)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ) (b : Y ⟶ D.P.A) (z : Y.left) (J)
    (hJ : Good D.P.L z J) :
    cubV D.cub z J (b ^ N) (b ^ N)⁻¹ (b ^ N) * (val D.sym (b ^ N).left z J)⁻¹ * cubN (cubV D.cub z J) N 1 b (b ^ N) *
      val ν b.left z J ^ N * val κ b.left z J ^ 2 = 1 := by
  have key := (((((grep_cub (D := D) (𝟙 D.P.A ^ N) (𝟙 D.P.A ^ N)⁻¹ (𝟙 D.P.A ^ N)).mul
    (grep_sym (𝟙 D.P.A ^ N)).inv).mul (grep_cubN (𝟙 _) (𝟙 D.P.A ^ N) N)).mul ((grep_nu ν hν.1 (𝟙 _)).pow N)).mul
    ((grep_kap κ hκ.1 (𝟙 _)).pow 2)).triv hG (fun U _ h => by
      rw [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, mul_comm (𝟙 D.P.A) (𝟙 D.P.A ^ N)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y J) := isCub_cubV D.cub hJ
      have e : (1 : 𝟙_ _ ⟶ D.P.A) ≫ 𝟙 D.P.A ^ N = 1 :=
        (comp_id_pow _ _).trans (one_pow _)
      beta_reduce
      rw [e, C.face₃, C.N_one, Category.comp_id, normd_one hν hJ, normd_one hκ hJ,
        normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ]
      simp) Y b z J hJ
  have e : b ≫ 𝟙 D.P.A ^ N = b ^ N := comp_id_pow _ _
  have e' : b ≫ (𝟙 D.P.A ^ N)⁻¹ = (b ^ N)⁻¹ := by rw [← e]; exact map_inv (preHom (G := D.P.A) b) (𝟙 D.P.A ^ N)
  beta_reduce at key
  rwa [e', e, Category.comp_id] at key

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem cPoint_neg (T : Over (Spec (CommRingCat.of R))) (y : D.X) : cP D T (-y) = (cP D T y)⁻¹ := by
  have := cPoint_add D T y (-y)
  rw [add_neg_cancel, cPoint_zero] at this
  exact (inv_eq_of_mul_eq_one_right this.symm).symm

theorem tau_self (hE : D.PsiEven) (hB : D.TauBimult) (y : D.X) {z : (TF (R := R) F).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau y y) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J =
      cubV D.cub z J (cP D (TF (R := R) F) y) (cP D _ y)⁻¹ (cP D _ y) * (val D.sym (cP D (TF (R := R) F) y).left z J)⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) *
          rigV D (TF (R := R) F).hom z J) ^ 2 := by
  let ρ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  have vτ : ∀ a b : D.X, val (D.tau a b) ρ.left z J =
      val (D.psi (a + b)) ρ.left z J * (val (D.psi a) ρ.left z J)⁻¹ * (val (D.psi b) ρ.left z J)⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have tm : ∀ a a' b : D.X, val (D.tau (a + a') b) ρ.left z J * th D z J (cP D _ a) (cP D _ a') (cP D _ b) =
      val (D.tau a b) ρ.left z J * val (D.tau a' b) ρ.left z J := fun a a' b => by
    have := tau_mul (𝟙 (TF (R := R) F)) hJ hB a a' b
    rw [Over.id_left, Category.id_comp] at this
    exact this
  have t₀ : val (D.tau 0 y) ρ.left z J = 1 := by
    have t := tm 0 0 y
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
    exact mul_eq_left.1 t.symm
  have t₁ := tm y (-y) y
  rw [add_neg_cancel, t₀, cPoint_neg, vτ (-y), neg_add_cancel] at t₁
  rw [vτ, zero_add] at t₀
  have ev := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) ρ.left)
  rw [val_pull hJ, show ρ.left ≫ D.xK y = (cP D (TF (R := R) F) y).left from
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (comp_cP D ρ y)] at ev
  rw [Over.id_left, Category.id_comp]
  show val (D.tau y y) ρ.left z J = th D z J _ _ _ * _ * (val (D.psi y) ρ.left z J * _) ^ 2
  apply Additive.ofMul.injective
  have a₀ := congrArg Additive.ofMul t₀
  have a₁ := congrArg Additive.ofMul t₁
  have a₂ := congrArg Additive.ofMul ev
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a₀ a₁ a₂ ⊢
  linear_combination (norm := module) - a₁ + a₀ + a₂

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ p : QkPt D.toPre F N, (∃ w, TXFrame N p w) ∧ ∀ w w', TXFrame N p w → TXFrame N p w' → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  rintro ⟨hL, -⟩ R _ _ _ I hI D F _ _ _ N ⟨k, hk⟩ p
  haveI : IsNoetherianRing R := hI.1
  obtain ⟨ν, hν⟩ := exists_nu (D := D.toPre) hL.mulPull N
  obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.mulPull N
  have alg : ∀ {U : Type} [CommGroup U] (x y : U), x ^ 2 = y ^ 2 → x ^ N = y ^ N → x = y := fun x y h₂ hN => by
    rw [hk, pow_succ, pow_succ, pow_mul, pow_mul, h₂] at hN
    exact mul_left_cancel hN
  refine ⟨?_, fun w w' hw hw' z J hJ => alg _ _ ((hw.2.1 ν hν z J hJ).trans (hw'.2.1 ν hν z J hJ).symm)
    (mul_right_cancel ((hw.2.2 κ hκ z J hJ).trans (hw'.2.2 κ hκ z J hJ).symm))⟩
  let ρ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
  have hy : cP D.toPre _ p.y = p.g.b ^ N := cPoint_y p
  have rs : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => (h (p.g.b ^ N * p.g.b).left)⁻¹ * h (p.g.b ^ N).left *
      h p.g.b.left * (h (1 : TF (R := R) F ⟶ D.toPre.P.A).left)⁻¹) (fun _ r z J => val (p.g.s p.y) r.left z J) :=
    ⟨_, inferInstance, _, _, p.g.s p.y, p.g.isGen _, fun U _ h => by rw [prod_gt, hy], fun _ _ _ _ _ => rfl⟩
  have rψ : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => (h (p.g.b ^ N).left)⁻¹)
      (fun _ r z J => val (D.toPre.psi p.y) (r.left ≫ ρ.left) z J) :=
    (grep_gen (D.toPre.psi p.y) (D.toPre.psi_gen _) ρ.left).congr (fun U _ h => by
      rw [Fintype.prod_unique, zpow_neg_one, ← hy, ← comp_cP D.toPre ρ]; rfl) (fun _ _ _ _ _ => rfl)
  have rr : GRep D.toPre.P.L (TF (R := R) F) (fun _ _ h => h (1 : TF (R := R) F ⟶ D.toPre.P.A).left)
      (fun T r z J => rigV D.toPre (r.left ≫ (TF (R := R) F).hom) z J) :=
    (grep_gen (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1) D.toPre.rig D.toPre.rig_gen
      (TF (R := R) F).hom).congr (fun U _ h => by rw [Fintype.prod_unique, zpow_one]; rfl) (fun _ _ _ _ _ => rfl)
  obtain ⟨w, hw, vw⟩ := (((rψ.mul rr).mul (grep_kap κ hκ.1 p.g.b).inv).mul
    ((rs.mul (grep_nu ν hν.1 p.g.b)).pow k).inv).out D.toPre.P.isLB (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε N)
    (fun U _ h => by
      rw [Fin.prod_univ_two]
      show _ = h (1 : TF (R := R) F ⟶ D.toPre.P.A).left ^ (N : ℤ) * h p.g.b.left ^ (-(N : ℤ))
      have hk' : (N : ℤ) = 2 * k + 1 := by exact_mod_cast hk
      rw [hk']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
  have key : ∀ z J, Good D.toPre.P.L z J →
      val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J ∧
      val w (𝟙 _) z J ^ N * val κ p.g.b.left z J =
        @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.toPre.psi p.y) (jFK (R := R) F) z J) *
          rigV D.toPre (TF (R := R) F).hom z J := fun z J hJ => by
    have e₀ := vw _ (𝟙 _) z J hJ
    beta_reduce at e₀
    rw [Over.id_left, Category.id_comp, Category.id_comp, Category.id_comp] at e₀
    have e₁ := (congrArg₂ (· * ·) (tau_self D.psi_even D.tau_bimult p.y hJ) rfl).symm.trans
      (chain_val (𝟙 (TF (R := R) F)) hJ p p.y)
    rw [Category.id_comp, hy] at e₁
    have e₂ := univ_identity hL.globalFns hν hκ p.g.b z J hJ
    have alg₂ : ∀ {U : Type} [CommGroup U] (w ψ r κ s ν c σ c' : U), w = ψ * r * κ⁻¹ * ((s * ν) ^ k)⁻¹ →
        c * σ * (ψ * r) ^ 2 * c' = s ^ N → c * σ * c' * ν ^ N * κ ^ 2 = 1 → w ^ 2 = s * ν ∧ w ^ N * κ = ψ * r := by
      intro U _ w ψ r κ s ν c σ c' h₀ h₁ h₂
      have a₁ := congrArg Additive.ofMul h₁
      have a₂ := congrArg Additive.ofMul h₂
      subst h₀ hk
      constructor <;> apply Additive.ofMul.injective <;>
        simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a₁ a₂ ⊢
      · linear_combination (norm := module) a₁ - a₂
      · linear_combination (norm := module) k • a₁ - k • a₂
    exact alg₂ _ _ _ _ _ _ _ _ _ e₀ e₁ e₂
  exact ⟨w, hw, fun ν' hν' z J hJ => (key z J hJ).1.trans
      (congrArg _ (normd_unique hL.globalFns hν hν' _ z J hJ)),
    fun κ' hκ' z J hJ => (congrArg _ (normd_unique hL.globalFns hκ' hκ _ z J hJ)).trans (key z J hJ).2⟩

end GlobalTheory.UT.SymFrame
end
