import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaCosetNonvanishingOfHasTh

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelSquare

theorem biadd_eq_zero {M U : Type} [AddCommGroup M] [AddCommGroup U] {n r : ℕ} (hn : Odd n) (B : M →+ M →+ U)
    (hB : ∀ x y, B x y = B y x) (hr : ∀ x y, n ^ r • B x y = 0) (T : Set M)
    (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + n • a) (c : U) (hc : ∀ t ∈ T, B t t = c) (x y : M) : B x y = 0 := by
  induction r generalizing x y with
  | zero => simpa using hr x y
  | succ r ih =>
    refine ih (fun x y => ?_) x y
    have h₁ : ∀ z, n ^ r • B z z = n ^ r • c := fun z => by
      obtain ⟨t, ht, a, rfl⟩ := hT z
      have a₁ := hr t a
      have a₂ := hr a t
      have a₃ := hr a (n • a)
      simp only [map_add, map_nsmul, AddMonoidHom.add_apply, AddMonoidHom.nsmul_apply, hc t ht, pow_succ] at a₁ a₂ a₃ ⊢
      linear_combination (norm := module) a₁ + a₂ + a₃
    have h₀ : ∀ z, n ^ r • B z z = 0 := fun z => (h₁ z).trans ((h₁ 0).symm.trans (by simp))
    have h₂ := h₀ (x + y)
    have h₃ := h₀ x
    have h₄ := h₀ y
    have h₅ := hr x y
    obtain ⟨l, rfl⟩ := hn
    simp only [map_add, AddMonoidHom.add_apply, hB y x, pow_succ] at h₂ h₅
    linear_combination (norm := module) h₅ - l • (h₂ - h₃ - h₄)

theorem div_prod_pow_eq_one {H I : Type} [CommGroup H] [Fintype I] {k : ℕ} {y z : I → H} (hk : ∀ i, y i ^ k = z i ^ k)
    (a : I → ℤ) : ((∏ i, y i ^ a i) / ∏ i, z i ^ a i) ^ k = 1 := by
  rw [div_pow, ← Finset.prod_pow, ← Finset.prod_pow, div_eq_one]
  exact Finset.prod_congr rfl fun i _ => by
    rw [← zpow_natCast, ← zpow_natCast, zpow_comm, zpow_comm (z i), zpow_natCast, zpow_natCast, hk]

theorem eq_of_pairing_const {H U I : Type} [CommGroup H] [CommGroup U] [Fintype I] {n r k : ℕ} (hn : Odd n)
    (e : H →* H →* U) (skew : ∀ x y, e y x = (e x y)⁻¹) (hH : ∀ x : H, x ^ n ^ r = 1)
    (iso : ∀ x y, x ^ k = 1 → y ^ k = 1 → e x y = 1) (nd : ∀ x, (∀ y, e x y = 1) → x = 1) (y z : I → H)
    (hyz : ∀ i j, e (y i) (y j) = e (z i) (z j)) (hk : ∀ i, y i ^ k = z i ^ k)
    (span : ∀ x, ∃ a : I → ℤ, x = ∏ i, y i ^ a i) (T : Set (I → ℤ)) (hT : ∀ x, ∃ t ∈ T, ∃ a, x = t + n • a) (c : U)
    (hc : ∀ t ∈ T, e (∏ i, z i ^ t i) ((∏ i, y i ^ t i) / ∏ i, z i ^ t i) = c) : y = z := by
  let Y : (I → ℤ) → H := fun a => ∏ i, y i ^ a i
  let Z : (I → ℤ) → H := fun a => ∏ i, z i ^ a i
  have hD : ∀ a, (Y a / Z a) ^ k = 1 := div_prod_pow_eq_one hk
  have hYZ : ∀ a b, e (Y a) (Y b) = e (Z a) (Z b) := fun a b => by
    simp only [Y, Z, map_prod, map_zpow, MonoidHom.finsetProd_apply, MonoidHom.zpow_apply, hyz]
  have hY : ∀ a b, e (Y a) (Y b / Z b) = e (Z a) (Y b / Z b) := fun a b => by
    rw [← div_eq_one, ← MonoidHom.div_apply, ← map_div]
    exact iso _ _ (hD a) (hD b)
  let B : (I → ℤ) →+ (I → ℤ) →+ Additive U := AddMonoidHom.mk' (fun a => AddMonoidHom.mk'
    (fun b => Additive.ofMul (e (Z a) (Y b / Z b))) fun b b' => by
      simp only [Y, Z, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, mul_div_mul_comm, map_mul, ofMul_mul])
    fun a a' => AddMonoidHom.ext fun b => by
      simp only [Z, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, map_mul, MonoidHom.mul_apply, ofMul_mul,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
  have hB := biadd_eq_zero (r := r) hn B (fun a b => by
      refine congrArg Additive.ofMul (show e (Z a) (Y b / Z b) = e (Z b) (Y a / Z a) from ?_)
      rw [← hY b a, map_div, map_div, hYZ, skew (Z a) (Y b), skew (Z a) (Z b), inv_div_inv])
    (fun a b => by
      show Additive.ofMul (e (Z a) (Y b / Z b) ^ n ^ r) = 0
      rw [← map_pow, hH, map_one, ofMul_one]) T hT (Additive.ofMul c) fun t ht => congrArg Additive.ofMul (hc t ht)
  classical
  funext i
  refine div_eq_one.1 (nd _ fun x => ?_)
  obtain ⟨a, rfl⟩ := span x
  have h := (hY a (Pi.single i 1)).trans (congrArg Additive.toMul (hB a (Pi.single i 1)))
  have s : ∀ w : I → H, ∏ j, w j ^ (Pi.single i 1 : I → ℤ) j = w i := fun w => by
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero]) (by simp)]
    simp
  simp only [Y, Z, s] at h
  rw [skew, h]
  exact inv_one

open Out ThetaCoord CommPairing VVRank in

theorem exists_twist (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) {T : Over S} {k : ℕ} (hk : Odd k) {I : Type}
    {x a : I → (T ⟶ P.A)} (ha : ∀ i, a i ^ k = 1) {c : I → Γ(T.left, ⊤)ˣ}
    (hc : ∀ i, WeilIs P.A P.L ((k : ℤ) ^ 2) (x i) (a i) (c i)) {v v' : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P k x v) (H' : IsThetaPtOver P k (fun i => a i * x i) v') :
    ∃ κ : Γ(T.left, ⊤), ∀ i, v i = κ * (c i ^ ((k ^ 2 + 1) / 2) : Γ(T.left, ⊤)ˣ) * v' i := by
  have hL := P.isLB
  have := P.isAb.comm
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, -, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨th', s₁', α', τ', U', s₂', w', u', hth', hα', hτ', hs₁', hU', hs₂', hw', hv'⟩ := H'
  obtain ⟨ρ, hρ⟩ := hth' th
  obtain ⟨ν, hν⟩ := exists_gen_negLB hG S P 1 T
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν (k ^ 2)
  obtain ⟨d, hd⟩ := CommutatorPairing.exists_ratio hL (fun _ _ _ => rfl) (fst T P.A).left (lift (𝟙 T) 1).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG P.isAb T) hα hα'
  obtain ⟨d', hd'⟩ := CommutatorPairing.exists_ratio hL (fun _ _ _ => rfl) (𝟙 T.left) (𝟙 T.left)
    (Category.comp_id _) (fun v => ⟨v, rfl⟩) hτ hτ'
  have main : ∀ i, w i * d' = ρ * d * (c i ^ ((k ^ 2 + 1) / 2) : Γ(T.left, ⊤)ˣ) * w' i := fun i => fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart hL (χ z)
    have hai : a i ^ k ^ 2 = 1 := by rw [sq, pow_mul, ha, one_pow]
    obtain ⟨θ, hθ, vθ⟩ := exists_symLift_mulPull P.isAb hL dvd_rfl hα' hai (ha i ▸ ho)
    have a₁ := tval_mul hG P.isAb hL hk.pow hai (hU i) hθ (hU' i) (hc i) (𝟙 T) hJ 1
    have a₂ := hd _ (lift (𝟙 T) (x i)).left z J hJ
    have a₃ := hd' _ (𝟙 _) z J hJ
    have b₁ := sv_act (hU i).pt_eq (hs₂ i) (𝟙 T) hJ 1
    have b₂ := sv_act (hU' i).pt_eq (hs₂' i) (𝟙 T) hJ 1
    have b₃ := sv_of_isValueAt (hw i) (𝟙 T) hJ
    have b₄ := sv_of_isValueAt (hw' i) (𝟙 T) hJ
    have b₅ := ThetaPtMove.sv_of_eq_mul hρ (lift (𝟙 T) (x i ^ k)).left z hJ
    rw [Category.id_comp, _root_.mul_one, vθ _ _ z J hJ, vo _ _ z J hJ, Category.id_comp, _root_.mul_one] at a₁
    rw [Category.id_comp, _root_.mul_one, sv_mulPull hs₁ _ hJ, b₅, lift_fst_left] at b₁
    rw [Category.id_comp, _root_.mul_one, sv_mulPull hs₁' _ hJ, mul_pow, ha, _root_.one_mul] at b₂
    rw [Category.id_comp, b₁] at b₃
    rw [Category.id_comp, b₂] at b₄
    rw [lift_fst_left] at a₂
    rw [Category.id_comp] at a₃
    have key : tval (U i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * bval (b := 1) α (lift (𝟙 T) (x i)).left z J =
        gm (𝟙 T.left) z ⊤ d * gm (𝟙 T.left) z ⊤ (c i) ^ ((k ^ 2 + 1) / 2) *
          (tval (U' i) (lift (𝟙 T) (1 : T ⟶ P.A)).left z J * bval (b := 1) α' (lift (𝟙 T) (a i * x i)).left z J) := by
      apply Additive.ofMul.injective
      replace a₁ := congrArg Additive.ofMul a₁
      replace a₂ := congrArg Additive.ofMul a₂
      simp only [ofMul_mul, ofMul_inv, Over.id_left] at a₁ a₂ ⊢
      linear_combination (norm := abel) a₁ + a₂
    replace key := congrArg Units.val key
    replace a₃ := congrArg Units.val a₃
    simp only [Units.val_mul, Over.id_left] at key a₃ b₃ b₄
    refine (Units.mul_left_inj (val τ' (𝟙 T.left) z J)).1 ?_
    rw [gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial,
      gs_unit _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial, map_pow]
    linear_combination (gs (𝟙 T.left) z ⊤ ρ * sv P.A th' (lift (𝟙 T) (x i ^ k)).left z J) * key - b₃ -
      gs (𝟙 T.left) z ⊤ (w i) * a₃ + (gs (𝟙 T.left) z ⊤ ρ * (gm (𝟙 T.left) z ⊤ d).val *
        (gm (𝟙 T.left) z ⊤ (c i) ^ ((k ^ 2 + 1) / 2)).val) * b₄
  refine ⟨u * ρ * d * (d'⁻¹ * u'⁻¹ : Γ(T.left, ⊤)ˣ), fun i => ?_⟩
  rw [hv, hv', (Units.eq_mul_inv_iff_mul_eq _).2 (main i), Units.val_mul]
  have := u'.inv_mul
  linear_combination (-(u * ρ * d * (d'⁻¹ : Γ(T.left, ⊤)ˣ) * (c i ^ ((k ^ 2 + 1) / 2) : Γ(T.left, ⊤)ˣ) * w' i : Γ(T.left, ⊤))) * this

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r M : ℕ}
    {y : Fin r → (T ⟶ A)} (h : ∀ i, y i ^ M = 1) (a : Fin r → ℕ) : Out.linComb y a ^ M = 1 := by
  rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

theorem linComb_val {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r M : ℕ} [NeZero M]
    {y : Fin r → (T ⟶ A)} (h : ∀ i, y i ^ M = 1) (a : Fin r → ℤ) :
    Out.linComb y (fun i => (a i : ZMod M).val) = ∏ i, y i ^ a i := by
  rw [Out.linComb, List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' _ (h i)]

open Out in

theorem eq_of_isThetaPt (hLaw : Laws) {g n j : ℕ} (hn : Odd n) (hj : 2 ≤ j) {K : Type} [Field K] [IsAlgClosed K]
    (P : PolAV (Sp K)) {y z : Fin (2 * g) → (baseOver (Sp K) ⟶ P.A)} (hy : ∀ i, y i ^ (n ^ j) ^ 2 = 1)
    (hz : ∀ i, z i ^ (n ^ j) ^ 2 = 1) (hk : ∀ i, y i ^ n ^ j = z i ^ n ^ j)
    (span : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ (n ^ j) ^ 2 = 1 →
      ∃ c : Ix g ((n ^ j) ^ 2), linComb y (fun i => (c i).val) = x)
    (hyz : ∀ i i', ∃ c, WeilIs P.A P.L ((n ^ j) ^ 2 : ℕ) (y i) (y i') c ∧ WeilIs P.A P.L ((n ^ j) ^ 2 : ℕ) (z i) (z i') c)
    {v : Ix g ((n ^ j) ^ 2) → Γ((baseOver (Sp K)).left, ⊤)}
    (Hy : IsThetaPt P (n ^ j) (fun a : Ix g ((n ^ j) ^ 2) => linComb y fun i => (a i).val) v)
    (Hz : IsThetaPtOver P (n ^ j) (fun a : Ix g ((n ^ j) ^ 2) => linComb z fun i => (a i).val) v)
    (hv : ∀ a, ∃ c, v (a + (n ^ j / n) • c) ≠ 0) : y = z := by
  have := P.isAb.comm
  let ε : K ≃+* Γ((baseOver (Sp K)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have : IsDomain Γ((baseOver (Sp K)).left, ⊤) := ε.symm.toMulEquiv.isDomain K
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')⟩
  have hu : IsUnit (((n ^ j) ^ 2 : ℕ) : Γ((baseOver (Sp K)).left, ⊤)) := by rw [Nat.cast_pow]; exact Hy.2.1.pow 2
  have hM : (((n ^ j) ^ 2 : ℕ) : K) ≠ 0 := fun h => hu.ne_zero (by rw [← map_natCast ε, h, map_zero])
  obtain ⟨w₁, w₂, -, -⟩ := hLaw.weil _ P ((n ^ j) ^ 2) (baseOver (Sp K))
  obtain ⟨u₁, u₂, -, u₄⟩ := hLaw.weil _ P (n ^ j) (baseOver (Sp K))
  let H : Subgroup (baseOver (Sp K) ⟶ P.A) := (powMonoidHom ((n ^ j) ^ 2)).ker
  have hH : ∀ x : H, x.1 ^ (n ^ j) ^ 2 = 1 := fun x => x.2
  choose c hc hc' using fun x y : H => w₁ x.1 y.1 (hH x) (hH y)
  have l : ∀ x x' y, c (x * x') y = c x y * c x' y := fun x x' y => (hc' _ _ _ (w₂ _ _ _ _ _ (hc x y) (hc x' y))).symm
  have s : ∀ x y, c y x = (c x y)⁻¹ := fun x y => (hc' _ _ _ (CommPairing.weilIs_symm P.isLB (hc x y))).symm
  let e : H →* H →* Γ((baseOver (Sp K)).left, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (c x) fun y y' => by
    rw [s (y * y'), l, mul_inv, ← s, ← s]) fun x x' => MonoidHom.ext fun y => l x x' y
  let y' : Fin (2 * g) → H := fun i => ⟨y i, hy i⟩
  let z' : Fin (2 * g) → H := fun i => ⟨z i, hz i⟩
  have cy : ∀ a : Fin (2 * g) → ℤ, (∏ i, y' i ^ a i : H).1 = linComb y fun i => (a i : ZMod ((n ^ j) ^ 2)).val :=
    fun a => by rw [linComb_val hy]; simp [y']
  have cz : ∀ a : Fin (2 * g) → ℤ, (∏ i, z' i ^ a i : H).1 = linComb z fun i => (a i : ZMod ((n ^ j) ^ 2)).val :=
    fun a => by rw [linComb_val hz]; simp [z']
  let q : (Fin (2 * g) → ℤ) → Ix g ((n ^ j) ^ 2) := fun a i => (a i : ZMod ((n ^ j) ^ 2))
  have sub : ∀ {x : (Fin (2 * g) → ℤ) → (baseOver (Sp K) ⟶ P.A)} {x₀ : Ix g ((n ^ j) ^ 2) → (baseOver (Sp K) ⟶ P.A)},
      (∀ a, x a = x₀ (q a)) → IsThetaPtOver P (n ^ j) x₀ v → IsThetaPtOver P (n ^ j) x fun a => v (q a) := by
    intro x x₀ h H
    obtain rfl : x = _ := funext h
    obtain ⟨th, s₁, α, τ, U, s₂, w, u, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := H
    exact ⟨th, s₁, α, τ, _, _, _, u, h₁, h₂, h₃, h₄, fun a => h₅ _, fun a => h₆ _, fun a => h₇ _, fun a => h₈ _⟩
  have hk' : ∀ i, y' i ^ n ^ j = z' i ^ n ^ j := fun i => Subtype.ext (hk i)
  obtain ⟨κ, hκ⟩ := exists_twist hLaw.globalFns P (hn.pow (n := j))
    (x := fun a : Fin (2 * g) → ℤ => (∏ i, z' i ^ a i : H).1)
    (a := fun a => ((∏ i, y' i ^ a i) / ∏ i, z' i ^ a i : H).1)
    (fun a => congrArg Subtype.val (div_prod_pow_eq_one hk' a)) (c := fun a => e _ _)
    (fun a => by rw [← Nat.cast_pow]; exact hc _ _) (sub cz Hz)
    (sub (fun a => by rw [← Subgroup.coe_mul, div_mul_cancel]; exact cy a) (ThetaCoord.isThetaPtOver_of_subsingleton P Hy))
  have hT : ∀ x : Fin (2 * g) → ℤ, ∃ t ∈ {a | v (q a) ≠ 0}, ∃ a, x = t + n • a := fun x => by
    obtain ⟨c, hc⟩ := hv (q x)
    choose c' hc' using fun i => ZMod.intCast_surjective (c i)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
    have e₁ : n ^ (m + 2) / n = n * n ^ m := by rw [pow_succ, Nat.mul_div_cancel _ hn.pos, pow_succ']
    refine ⟨x + (n * n ^ m) • c', ?_, -(n ^ m • c'), by rw [mul_smul, smul_neg, add_neg_cancel_right]⟩
    show v _ ≠ 0
    convert hc using 2
    funext i
    simp [q, e₁, hc']
  have sq' : ∀ x x' : H, (e x x' ^ (((n ^ j) ^ 2 + 1) / 2)) ^ 2 = e x x' := fun x x' => by
    rw [← pow_mul, Nat.div_mul_cancel (hn.pow.pow.add_one).two_dvd, pow_succ, ← map_pow,
      show x' ^ (n ^ j) ^ 2 = 1 from Subtype.ext (hH x'), map_one, _root_.one_mul]
  have one : ∀ t, v (q t) ≠ 0 → κ * (e (∏ i, z' i ^ t i) ((∏ i, y' i ^ t i) / ∏ i, z' i ^ t i) ^
      (((n ^ j) ^ 2 + 1) / 2) : Γ((baseOver (Sp K)).left, ⊤)ˣ) = 1 := fun t ht =>
    mul_right_cancel₀ ht ((hκ t).symm.trans (_root_.one_mul _).symm)
  obtain ⟨t₀, ht₀, -⟩ := hT 0
  have := eq_of_pairing_const (r := j * 2) (k := n ^ j) hn e s (fun x => by rw [pow_mul]; exact Subtype.ext (hH x))
    (fun x x' hx hx' => ?_) (fun x h => Subtype.ext
      (hLaw.weilNondeg K P _ hM x.1 (hH x) fun y hy => (show c x ⟨y, hy⟩ = 1 from h ⟨y, hy⟩) ▸ hc x ⟨y, hy⟩))
    y' z' (fun i i' => ?_) hk' (fun x => ?_) _ hT _ (fun t ht => ?_ : ∀ t ∈ _, _ =
      e (∏ i, z' i ^ t₀ i) ((∏ i, y' i ^ t₀ i) / ∏ i, z' i ^ t₀ i))
  · exact funext fun i => congrArg Subtype.val (congrFun this i)
  · have hx₁ : x.1 ^ n ^ j = 1 := congrArg Subtype.val hx
    have hx₂ : x'.1 ^ n ^ j = 1 := congrArg Subtype.val hx'
    have h := (u₄ (n ^ j) x.1 x'.1 (c x x') (by rw [← sq]; exact hu) (by rw [← sq]; exact hH x) hx₂).1
      (by rw [← Nat.cast_mul, ← sq]; exact hc x x')
    rw [hx₁] at h
    show c x x' = 1
    exact mul_eq_left.1 ((u₁ 1 x'.1 (one_pow _) hx₂).unique (by simpa using u₂ _ _ _ _ _ h h) h)
  · obtain ⟨c₀, h₁, h₂⟩ := hyz i i'
    exact (hc' (y' i) (y' i') _ h₁).symm.trans (hc' (z' i) (z' i') _ h₂)
  · obtain ⟨c₀, h₀⟩ := span x.1 (hH x)
    choose c' hc' using fun i => ZMod.intCast_surjective (c₀ i)
    exact ⟨c', Subtype.ext (by rw [cy, ← h₀]; simp only [hc'])⟩
  · rw [← sq', ← sq' (∏ i, z' i ^ t₀ i)]
    exact congrArg (· ^ 2) (Units.ext (mul_left_cancel₀ (left_ne_zero_of_mul_eq_one (one t ht))
      ((one t ht).trans (one t₀ ht₀).symm)))

end GlobalTheory.LevelSquare

namespace GlobalTheory

open LevelSquare ThetaPtMove in

theorem level_eq_of_pow_eq_of_hasTh : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ Sp o) (t t' : TObj g ((n ^ j) ^ 2) J b s) (φ : t'.A.left ⟶ t.A.left) (v : Ix g ((n ^ j) ^ 2) → K), IsGrpPullback t'.A t.A (𝟙 _) φ → LBIso t'.L (t.L.pull φ) → (∀ i, (t'.pt i ^ n ^ j).left ≫ φ = (t.pt i ^ n ^ j).left) → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → ∀ i, (t'.pt i).left ≫ φ = (t.pt i).left := by
  intro hLaw hLaw₂ g n j J hp hn hj o _ b K _ _ s t t' φ v hφ hw hk H H'
  have hc := GlobalTheory.coset_of_hasTh hLaw hLaw₂ o g (n ^ j) J b _ s t n K (𝟙 _) v ⊥ hp.two_le (dvd_pow_self n (by omega)) H
    Ideal.isPrime_bot
  have := t.ab.comm
  have := t'.ab.comm
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')⟩
  let B := Out.baseOver (Sp K)
  have : Subsingleton B.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty B.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have hid : ∀ (A : Over (Sp K)) h (x : Out.baseOver (Sp K) ⟶ A),
      (Over.homMk (𝟙 (Sp K)) h : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) ≫ x = x := fun _ _ x => Category.id_comp x
  have hτ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 _ := (Category.id_comp _).trans (Category.comp_id _).symm
  have inj : ∀ {x y : B ⟶ t'.A}, x.left ≫ φ = y.left ≫ φ → x = y := fun h =>
    Over.OverMorphism.ext (hφ.1.hom_ext h (by rw [Over.w, Over.w]))
  have ex : ∀ x₀ : B ⟶ t.A, ∃ x : B ⟶ t'.A, 𝟙 B.left ≫ x₀.left = x.left ≫ φ := fun x₀ =>
    ⟨Over.homMk (hφ.1.lift x₀.left B.hom ((Over.w x₀).trans (Category.comp_id _).symm)) (hφ.1.lift_snd _ _ _),
      (Category.id_comp _).trans (hφ.1.lift_fst _ _ _).symm⟩
  choose z hz using fun i => ex (t.pt i)
  have hzN : ∀ i, z i ^ (n ^ j) ^ 2 = 1 := fun i => inj ((over_pow hφ _ hτ (hz i) _).symm.trans
    ((congrArg (fun y : B ⟶ t.A => 𝟙 B.left ≫ y.left) (t.torsion i)).trans (over_one hφ _ hτ)))
  have hlab : ∀ a : Ix g ((n ^ j) ^ 2),
      𝟙 B.left ≫ (t.lab a).left = (Out.linComb z fun i => (a i).val).left ≫ φ := fun a =>
    (over_iff hφ _ hτ _ _).2 (by
      rw [TObj.lab, Out.linComb, Out.linComb, List.prod_ofFn, List.prod_ofFn, map_prod, map_prod]
      exact Finset.prod_congr rfl fun i _ => by rw [map_pow, map_pow, (over_iff hφ _ hτ _ _).1 (hz i)])
  unfold TObj.HasTh at H H'
  simp only [hid] at H H'
  have Hz : Out.IsThetaPtOver t'.pol (n ^ j) (fun a : Ix g ((n ^ j) ^ 2) => Out.linComb z fun i => (a i).val) _ :=
    isThetaPtOver_move (P₀ := t.pol) (P := t'.pol) (𝟙 B.left) hφ hw (B := B) (𝟙 _) (𝟙 B) (Category.id_comp _) hτ
      (fun _ => ThetaCoord.isGenSec_pullS t.isLB _ _ (Category.id_comp _)) hlab
      (fun a => linComb_pow hzN _)
      (ThetaCoord.isThetaPtOver_of_subsingleton _ H)
  have key : t'.pt = z := eq_of_isThetaPt hLaw hn hj t'.pol t'.torsion hzN
    (fun i => inj ((hk i).trans ((Category.id_comp _).symm.trans (over_pow hφ _ hτ (hz i) _))))
    (fun x hx => (t'.bij K (𝟙 _) x hx).exists.imp fun c h =>
      (congrArg (Out.linComb · _) (funext fun i => hid _ _ _)).symm.trans h)
    (fun i i' => ⟨_, t'.pairing i i', by
      let U : Over.mk (B.hom ≫ 𝟙 _) ⟶ B := Over.homMk (𝟙 _) hτ
      exact (weilIs_grpPullback_of_comm' _ _ _ _ _ _ _ _ t.isLB t'.isLB hφ hw B _ _ _ (U ≫ t.pt i) (U ≫ t.pt i') _
        (hz i) (hz i')).2 (CommPairing.weilIs_pull hLaw.globalFns t.ab t.isLB U (t.pairing i i'))⟩)
    H' Hz
    (fun a => (hc a).imp fun c h h₀ => h ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective
      (h₀.trans (map_zero _).symm)))
  intro i
  rw [key, ← hz, Category.id_comp]

end GlobalTheory
