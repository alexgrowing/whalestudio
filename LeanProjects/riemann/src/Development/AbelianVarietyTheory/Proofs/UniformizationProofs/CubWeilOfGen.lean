import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.KerPair

theorem exists_pow_gen {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℕ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val t' r z J = val t r z J ^ n := by
  induction n with
  | zero =>
    obtain ⟨t', ht', hv⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (0 : ℕ))
      (fun U _ h => by simp) (LB.oneGen L (Y := Y))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨t', ht', fun Z r z J hJ => (hv _ _ z J hJ).trans ((val_one _).trans (pow_zero _).symm)⟩
  | succ n ih =>
    obtain ⟨s, hs, hv⟩ := ih
    obtain ⟨t', ht', hv'⟩ := exists_gen hL (φ' := φ) (ε' := fun k => ε k * (n + 1 : ℕ)) (fun U _ h => by
        refine (Fintype.prod_sum_type _).trans ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [← zpow_add]
        congr 1
        push_cast
        ring)
      (LB.mulGen L _ _ _ _ s t) (DVR.mulGen_isGen _ _ _ _ _ _ _ hs ht)
    refine ⟨t', ht', fun Z r z J hJ => (hv' _ _ z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
    rw [hv Z r z J hJ, pow_succ]

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B} (c : CubicalStr B L)
  {T : Over S} {x : T ⟶ B}

abbrev trφ (x : T ⟶ B) : Fin 2 → ((T ⊗ B).left ⟶ B.left) := ![((fst T B ≫ x) * snd T B).left, (snd T B).left]

omit [IsCommMonObj B] in

theorem prod_tr {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) (m : ℤ) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ ((![1, -1] : Fin 2 → ℤ) k * m) =
      h ((ρ ≫ x) * b).left ^ m * h b.left ^ (-m) := by
  have e₀ : (lift ρ b).left ≫ trφ x 0 = ((ρ ≫ x) * b).left := by
    show (lift ρ b ≫ ((fst T B ≫ x) * snd T B)).left = _
    rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]
  have e₁ : (lift ρ b).left ≫ trφ x 1 = b.left := by
    show (lift ρ b ≫ snd T B).left = _
    rw [lift_snd]
  rw [Fin.prod_univ_two, e₀, e₁]
  simp

omit [IsCommMonObj B] in

theorem prod_tr_one {T' : Over S} (ρ : T' ⟶ T) (b : T' ⟶ B) {U : Type} [CommGroup U] (h : (T'.left ⟶ B.left) → U) :
    ∏ k : Fin 2, h ((lift ρ b).left ≫ trφ x k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h ((ρ ≫ x) * b).left * (h b.left)⁻¹ := by
  simpa using prod_tr (x := x) ρ b h 1

theorem val_mul_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) (a b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    val u (lift (𝟙 T) (a * b)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J =
      cubV c z J x a b * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) b).left z J := by
  let p := fst T B
  let q := snd T B
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ u (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hu _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans (by rw [← Over.comp_left, comp_lift])
  let t₁ := LB.mulGen L.L _ _ _ _ (uu ((p ≫ a) * q)) (uu 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _
    (LB.pullGen L.L (thφ B (x3 B)) thε c.t (lift (p ≫ x) (lift (p ≫ a) q)).left) (uu (p ≫ a))) (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J =
        val u (lift (𝟙 T) (a * w)).left z J * val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ∧
      val t₂ (lift (𝟙 T) w).left z J =
        cubV c z J x a w * val u (lift (𝟙 T) a).left z J * val u (lift (𝟙 T) w).left z J := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vu _ hJ _) (vu _ hJ _))).trans ?_
      rw [MonObj.comp_mul, MonObj.comp_one, hp, hq, hp']
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (val_cub c _ hJ _ _ _) (vu _ hJ _))) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp', hp']
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gu _) (gu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _) (gu _)) (gu _))
    (fun y I hI => ?_) _ _ z J hJ
  · refine (DVR.prod_sum₂ (K := thK ⊕ Fin 2) (K' := Fin 2) (U := V) _
      (DVR.prod_sum₂ (K := thK) (K' := Fin 2) (U := V) _ (prod_cub (p ≫ x) (p ≫ a) q k) (prod_tr_one p (p ≫ a) k))
      (prod_tr_one p q k)).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_tr_one p ((p ≫ a) * q) k) (prod_tr_one p 1 k)).symm)
    rw [_root_.mul_one, ← _root_.mul_assoc (p ≫ x)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [_root_.mul_one, (isCub_cubV c hI).face₃, _root_.one_mul]

theorem val_pow_pt (hG : GlobalFnsSt) (hB : IsAbelianScheme B) (u : LB.Gen (LB.LinComb L.L (trφ x) ![1, -1]))
    (hu : u.IsGen) {N : ℕ} (hx : x ^ N = 1) (b : T ⟶ B) (z : T.left) (J) (hJ : Good L.L z J) :
    cubN (cubV c z J) N 1 x b * val u (lift (𝟙 T) b).left z J ^ N = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := by
  let p := fst T B
  let q := snd T B
  have hx' : (p ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, hv⟩ := WeilCube.exists_gen_torsion c N (p ≫ x) q hx'
  obtain ⟨s, hs, hsv⟩ := exists_pow_gen L.isLB u hu N
  let uu := fun w : T ⊗ B ⟶ B => LB.pullGen L.L _ _ s (lift p w).left
  have gu : ∀ w, (uu w).IsGen := fun w => DVR.pullGen_isGen _ _ _ _ hs _
  have vu : ∀ {T' : Over S} (σ : T' ⟶ T ⊗ B) {z : T'.left} {J}, Good L.L z J → ∀ w,
      val (uu w) σ.left z J = val u (lift (σ ≫ p) (σ ≫ w)).left z J ^ N := fun σ z J hJ w =>
    (val_pull hJ _ _ _).trans ((hsv _ _ z J hJ).trans (by rw [← Over.comp_left, comp_lift]))
  let t₁ := LB.mulGen L.L _ _ _ _ t (uu q)
  have ev : ∀ (w : T ⟶ B) {z : T.left} {J}, Good L.L z J →
      val t₁ (lift (𝟙 T) w).left z J = cubN (cubV c z J) N 1 x w * val u (lift (𝟙 T) w).left z J ^ N ∧
      val (uu 1) (lift (𝟙 T) w).left z J = val u (lift (𝟙 T) (1 : T ⟶ B)).left z J ^ N := fun w z J hJ => by
    have hp : lift (𝟙 T) w ≫ p = 𝟙 T := lift_fst _ _
    have hq : lift (𝟙 T) w ≫ q = w := lift_snd _ _
    have hp' : ∀ v : T ⟶ B, lift (𝟙 T) w ≫ p ≫ v = v := fun v => by rw [← Category.assoc, hp, Category.id_comp]
    constructor
    · refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv _ _ z J hJ) (vu _ hJ _))).trans ?_
      rw [hp, hq, hp']
    · refine (vu _ hJ _).trans ?_
      rw [MonObj.comp_one, hp]
  refine (ev b hJ).1.symm.trans (Eq.trans ?_ (ev b hJ).2)
  refine gen_unique' L.isLB (fun V _ k => ?_) p.left (lift (𝟙 T) (1 : T ⟶ B)).left
    (by rw [← Over.comp_left, lift_fst, Over.id_left]) (WeilCube.surj_fst hG hB T)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (gu _)) (gu _) (fun y I hI => ?_) _ _ z J hJ
  · refine (prod_tr p 1 k N).trans (Eq.trans ?_
      (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 2) (U := V) _ rfl (prod_tr p q k N)).symm)
    rw [_root_.mul_one]
    simp only [Fin.prod_univ_succ, Sum.elim_inl, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · refine (ev 1 hI).1.trans (Eq.trans ?_ (ev 1 hI).2.symm)
    rw [(isCub_cubV c hI).N_one, _root_.one_mul]

theorem cubWeil_of_gen : (GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ) (T : Over S) (x y : T ⟶ B), x ^ N = 1 → y ^ N = 1 → (∃ u : LB.Gen (translDiff B L.L x), u.IsGen) → CubWeil c N x y 1) := by
  intro hG S B _ _ hB L c N T x y hx hy ⟨u, hu⟩
  refine ⟨hx, hy, fun z J hJ => ?_⟩
  have C := isCub_cubV c hJ
  obtain ⟨U, hU⟩ : ∃ U : (T ⟶ B) → (T.left.presheaf.stalk z)ˣ,
      ∀ b, U b = val (L := L.L) (φ := trφ x) (ε := ![1, -1]) u (lift (𝟙 T) b).left z J := ⟨_, fun _ => rfl⟩
  have m : ∀ a b, U (a * b) * U 1 = cubV c z J x a b * U a * U b := fun a b => by
    simp only [hU]; exact val_mul_pt c hG hB u hu a b z J hJ
  have k : cubN (cubV c z J) N 1 x y * U y ^ N = U 1 ^ N := by
    simp only [hU]; exact val_pow_pt c hG hB u hu hx y z J hJ
  have b : ∀ n : ℕ, U (y ^ n) * U 1 ^ n = U 1 * (cubN (cubV c z J) n 1 y x * U y ^ n) := fun n => by
    induction n with
    | zero => simp [cubN]
    | succ n ih =>
      have e := m (y ^ n) y
      rw [C.s01, C.s12] at e
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
      rw [pow_succ, pow_succ, pow_succ]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e
      have ih' := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at e' ih' ⊢
      linear_combination (norm := abel) e' + ih'
  have b' := b N
  rw [hy] at b'
  rw [map_one, _root_.one_mul]
  exact mul_right_cancel (k.trans (mul_left_cancel b'))

end GlobalTheory.UU.KerPair
end
