import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SymmetricLiftOddOrderExistsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaCoord

open CommPairing GlobalLift VVRank

theorem scalar_eq {G U : Type} [CommGroup G] [CommGroup U] (f g e ν : G → U) (X Y : G) (c d : U) (l : ℕ)
    (hY : Y ^ (2 * l + 1) = 1)
    (hf : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), f (X ^ j * m) = 1)
    (hg : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), g (Y ^ j * m) = 1)
    (he : ∀ m, ∏ j ∈ Finset.range (2 * l + 1), e ((Y * X) ^ j * m) = 1)
    (sf : ∀ m, f (X⁻¹ * m) * ν m * (f m⁻¹ * (ν (X⁻¹ * m))⁻¹) = 1)
    (sg : ∀ m, g (Y⁻¹ * m) * ν m * (g m⁻¹ * (ν (Y⁻¹ * m))⁻¹) = 1)
    (se : ∀ m, e ((Y * X)⁻¹ * m) * ν m * (e m⁻¹ * (ν ((Y * X)⁻¹ * m))⁻¹) = 1)
    (hc : ∀ m, f m * g (X * m) = g m * f (Y * m) * c) (hd : ∀ m, f m * g (X * m) = d * e m) :
    d = c ^ (l + 1) := by
  have h₁ : ∀ n m, f m * ∏ j ∈ Finset.range n, g (Y ^ j * (X * m)) =
      (∏ j ∈ Finset.range n, g (Y ^ j * m)) * f (Y ^ n * m) * c ^ n := fun n m => by
    induction n with
    | zero => simp
    | succ n ih =>
      have := hc (Y ^ n * m)
      rw [mul_left_comm X, ← _root_.mul_assoc Y, ← pow_succ'] at this
      rw [Finset.prod_range_succ, Finset.prod_range_succ, ← _root_.mul_assoc, ih, pow_succ c]
      apply Additive.ofMul.injective
      replace this := congrArg Additive.ofMul this
      simp only [ofMul_mul] at this ⊢
      linear_combination (norm := abel) this
  have h₂ : ∀ n m, d ^ n * (∏ j ∈ Finset.range n, e ((Y * X) ^ j * m)) * c ^ (n.choose 2) =
      (∏ j ∈ Finset.range n, f (X ^ j * m)) * ∏ j ∈ Finset.range n, g (Y ^ j * (X ^ n * m)) := fun n m => by
    induction n with
    | zero => simp
    | succ n ih =>
      have a := h₁ n (X ^ n * m)
      have b := hd ((Y * X) ^ n * m)
      have e₁ : X * (X ^ n * m) = X ^ (n + 1) * m := by rw [pow_succ', _root_.mul_assoc]
      have e₂ : X * ((Y * X) ^ n * m) = Y ^ n * (X ^ (n + 1) * m) := by rw [mul_pow, pow_succ']; ac_rfl
      have e₃ : Y ^ n * (X ^ n * m) = (Y * X) ^ n * m := by rw [mul_pow, _root_.mul_assoc]
      rw [e₁, e₃] at a
      rw [e₂] at b
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Nat.choose_succ_succ',
        Nat.choose_one_right, pow_add c, pow_succ d]
      apply Additive.ofMul.injective
      replace a := congrArg Additive.ofMul a
      replace b := congrArg Additive.ofMul b
      replace ih := congrArg Additive.ofMul ih
      simp only [ofMul_mul] at a b ih ⊢
      linear_combination (norm := abel) ih - a - b
  have cq : c ^ (2 * l + 1) = 1 := by
    have := h₁ (2 * l + 1) 1
    rw [hg, hg, hY, _root_.one_mul, _root_.one_mul, _root_.mul_one] at this
    exact left_eq_mul.1 this
  have dq : d ^ (2 * l + 1) = 1 := by
    have := h₂ (2 * l + 1) 1
    have e₁ : (2 * l + 1).choose 2 = (2 * l + 1) * l := by
      rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
    rwa [he, hf, hg, e₁, pow_mul, cq, one_pow, _root_.mul_one, _root_.mul_one, _root_.mul_one] at this
  have d2 : d ^ 2 = c := by
    have a₁ := sf 1
    have a₂ := sg X⁻¹
    have a₃ := se 1
    have a₄ := hc (Y * X)⁻¹
    have a₅ := hd (Y * X)⁻¹
    have a₆ := hd 1
    have e₁ : Y⁻¹ * X⁻¹ = (Y * X)⁻¹ := (mul_inv _ _).symm
    have e₂ : Y * (Y * X)⁻¹ = X⁻¹ := by rw [mul_inv, mul_inv_cancel_left]
    rw [e₂] at a₄
    rw [e₁] at a₂
    simp only [_root_.mul_one, inv_one, inv_inv] at a₁ a₂ a₃ a₆
    apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    replace a₄ := congrArg Additive.ofMul a₄
    replace a₅ := congrArg Additive.ofMul a₅
    replace a₆ := congrArg Additive.ofMul a₆
    simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_pow] at a₁ a₂ a₃ a₄ a₅ a₆ ⊢
    linear_combination (norm := module) a₁ + a₂ - a₃ + a₄ - a₅ - a₆
  rw [← d2, ← pow_mul, show 2 * (l + 1) = 2 * l + 1 + 1 by ring, pow_succ, dq, _root_.one_mul]

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}

theorem lift_translT (π : T' ⟶ T) (x : T ⟶ A) (p : T' ⟶ A) :
    (lift π p).left ≫ (translT A x).left = (lift π ((π ≫ x) * p)).left := by
  rw [← Over.comp_left, translT, translPt, comp_lift, lift_fst, comp_lift_assoc, lift_fst_assoc, lift_snd]; rfl

theorem lift_negT (π : T' ⟶ T) (p : T' ⟶ A) : (lift π p).left ≫ (negT A T).left = (lift π p⁻¹).left := by
  rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc]; rfl

theorem lift_mulT (π : T' ⟶ T) (n : ℕ) (p : T' ⟶ A) :
    (lift π p).left ≫ (mulT A T n).left = (lift π (p ^ n)).left := by
  rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]

omit [GrpObj A] in
theorem lift_fst_left (π : T' ⟶ T) (p : T' ⟶ A) : (lift π p).left ≫ (fst T A).left = π.left := by
  rw [← Over.comp_left, lift_fst]

theorem prod_tval {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    ∏ j ∈ Finset.range n, tval θ (lift π ((π ≫ x) ^ j * p)).left z J = 1 := by
  have q := val_corr hJ H.pow_eq (lift π p).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q
  rw [Finset.prod_range]
  refine Eq.trans (Finset.prod_congr rfl fun i _ => ?_) q
  rw [lift_translT, H.pt_eq, MonObj.comp_pow]

theorem sym_tval (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    tval θ (lift π ((π ≫ x)⁻¹ * p)).left z J * nval ν (lift π p).left z J *
      (tval θ (lift π p⁻¹).left z J * (nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹) = 1 := by
  obtain ⟨ν', hν', hs⟩ := H.sym
  have q := val_corr hJ hs (lift π p).left
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at q
  have w : nval ν (lift π p).left z J * (nval ν' (lift π p).left z J)⁻¹ =
      nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J * (nval ν' (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹ :=
    val_div_eq hL (fst T A).left (surj_fst hG hA T) hν hν' _ _ (by rw [lift_fst_left, lift_fst_left]) z J hJ
  apply Additive.ofMul.injective
  replace q := congrArg Additive.ofMul q
  replace w := congrArg Additive.ofMul w
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at q w ⊢
  linear_combination (norm := abel) q + w

theorem symLift_of_tval (hL : L.IsLB) {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T} (hx : θ.pt = x)
    {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen)
    (h₁ : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      ∏ j ∈ Finset.range n, tval θ (lift π ((π ≫ x) ^ j * p)).left z J = 1)
    (h₂ : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      tval θ (lift π ((π ≫ x)⁻¹ * p)).left z J * nval ν (lift π p).left z J *
        (tval θ (lift π p⁻¹).left z J * (nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹) = 1) :
    SymLift A L k n x θ := by
  refine ⟨hx, corr_of_val hL fun y J hJ => ?_, ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  · rw [val_one, SymLiftOdd.id_eq_lift]
    exact (SymLiftOdd.val_powGen θ n hx hJ _).trans (h₁ _ _ y J hJ _)
  · rw [val_one, SymLiftOdd.id_eq_lift]
    exact (SymLiftOdd.val_symGen θ ν hx hJ _).trans (h₂ _ _ y J hJ _)

theorem tval_mul (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    tval θx (lift π p).left z J * tval θy (lift π ((π ≫ x) * p)).left z J =
      gm π.left z ⊤ c ^ ((q + 1) / 2) * tval θ (lift π p).left z J := by
  have := hA.comm
  obtain ⟨l, rfl⟩ := hq
  obtain rfl := Hx.pt_eq
  obtain rfl := Hy.pt_eq
  obtain ⟨θ', hp, hv⟩ := ThetaAct.exists_mul hL θx θy
  obtain ⟨d, hd⟩ := ThetaAct.exists_ratio hG hA hL θ θ' (H.pt_eq.trans hp.symm)
  have hd' : ∀ p : T' ⟶ A, tval θx (lift π p).left z J * tval θy (lift π ((π ≫ θx.pt) * p)).left z J =
      gm π.left z ⊤ d * tval θ (lift π p).left z J := fun p => by
    rw [← lift_translT, ← hv _ _ z J hJ]
    apply Units.ext
    rw [hd _ _ z J hJ, lift_fst_left, Units.val_mul, gs_unit _ _ ⊤ trivial]
  obtain ⟨ν, hν, -⟩ := H.sym
  have hc' := (commIsOf_iff hL _ _ _).1 ((weilIs_iff_commIsOf hG hA hL _ _ _).1 hc)
  rw [hd', show (2 * l + 1 + 1) / 2 = l + 1 by omega]
  refine congrArg (· * _) (scalar_eq (fun p : T' ⟶ A => tval θx (lift π p).left z J)
    (fun p => tval θy (lift π p).left z J) (fun p => tval θ (lift π p).left z J)
    (fun p => nval ν (lift π p).left z J) (π ≫ θx.pt) (π ≫ θy.pt) _ _ l
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) (prod_tval Hx π hJ) (prod_tval Hy π hJ)
    (fun m => by rw [← MonObj.comp_mul]; exact prod_tval H π hJ m)
    (sym_tval hG hA hL Hx hν π hJ) (sym_tval hG hA hL Hy hν π hJ)
    (fun m => by rw [← MonObj.comp_mul]; exact sym_tval hG hA hL H hν π hJ m) (fun m => ?_) hd')
  have := hc' _ (lift π m).left z J hJ
  rwa [lift_translT, lift_translT, lift_fst_left] at this

abbrev bval {a b : ℤ} {r : ℕ} (β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b]))
    {Z : Scheme.{0}} (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val β ρ z J

theorem exists_conj (hL : L.IsLB) {a b : ℤ} {r : ℕ}
    {β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b])} (hβ : β.IsGen)
    (ψ : T ⊗ A ⟶ T ⊗ A) {m m' : T ⊗ A ⟶ A} (h₁ : ψ ≫ snd T A = m') (h₂ : mulT A T r ≫ m = m' ^ r)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![b, -b])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m'.left] ![a, -a]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val u' ρ z J = bval β ρ z J * val u (ρ ≫ (mulT A T r).left) z J * (bval β (ρ ≫ ψ.left) z J)⁻¹ := by
  have e₁ : mulT A T r ≫ snd T A = snd T A ^ r := lift_snd _ _
  have e₂ : ψ ≫ snd T A ^ r = m' ^ r := by rw [MonObj.comp_pow, h₁]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, m'.left]) (ε' := ![a, -a])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, ← Over.comp_left, e₁, e₂, h₁, h₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (LB.mulGen L _ _ _ _ β (LB.pullGen L _ _ u (mulT A T r).left))
      (LB.invGen L _ _ (LB.pullGen L _ _ β ψ.left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ hu _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _)))
  exact ⟨t, ht, fun Z ρ z J hJ => (hv Z ρ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (_ * ·) (val_pull hJ _ _ _)))
    ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))⟩

theorem exists_symLift_mulPull (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {r q q' : ℕ} (hq : q ∣ q')
    {β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b])} (hβ : β.IsGen)
    {y : T ⟶ A} (hy : y ^ q' = 1) {θ : ThetaGrp A L b T} (H : SymLift A L b q (y ^ r) θ) :
    ∃ θ' : ThetaGrp A L a T, SymLift A L a q' y θ' ∧
      ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
        tval θ' (lift π p).left z J = bval β (lift π p).left z J * tval θ (lift π (p ^ r)).left z J *
          (bval β (lift π ((π ≫ y) * p)).left z J)⁻¹ := by
  have := hA.comm
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨u, hu, hv⟩ := exists_conj hL hβ (translT A y) (m := translPt A θ.pt) (m' := translPt A y) (lift_snd _ _)
    (by
      rw [mulT, SymLiftOdd.lift_translPt, H.pt_eq, MonObj.comp_pow, ← mul_pow]; rfl) θ.isGen
  obtain ⟨ν', hν', hw⟩ := exists_conj hL hβ (negT A T) (m := snd T A ≫ (GrpObj.inv : A ⟶ A))
    (m' := snd T A ≫ (GrpObj.inv : A ⟶ A)) (lift_snd _ _)
    (by
      rw [mulT, lift_snd_assoc]
      exact (inv_pow (snd T A) r).symm) hν
  have hv' : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      tval (⟨y, u, hu⟩ : ThetaGrp A L a T) (lift π p).left z J =
        bval β (lift π p).left z J * tval θ (lift π (p ^ r)).left z J *
          (bval β (lift π ((π ≫ y) * p)).left z J)⁻¹ := fun T' π z J hJ p => by
    rw [← lift_mulT, ← lift_translT]; exact hv _ _ z J hJ
  have hw' : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      nval ν' (lift π p).left z J = bval β (lift π p).left z J * nval ν (lift π (p ^ r)).left z J *
          (bval β (lift π p⁻¹).left z J)⁻¹ := fun T' π z J hJ p => by
    rw [← lift_mulT, ← lift_negT]; exact hw _ _ z J hJ
  refine ⟨⟨y, u, hu⟩, symLift_of_tval hL rfl hν' (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · let B : ℕ → (T'.left.presheaf.stalk z)ˣ := fun j => (bval β (lift π ((π ≫ y) ^ j * p)).left z J)⁻¹
    have e : ∀ j ∈ Finset.range q', tval (⟨y, u, hu⟩ : ThetaGrp A L a T) (lift π ((π ≫ y) ^ j * p)).left z J =
        tval θ (lift π ((π ≫ y ^ r) ^ j * p ^ r)).left z J * (B (j + 1) / B j) := fun j _ => by
      rw [hv' _ _ z J hJ, mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, SymLiftOdd.comp_pow' π y r, ← _root_.mul_assoc (π ≫ y),
        ← pow_succ', div_inv_eq_mul]
      exact (fun x t w : (T'.left.presheaf.stalk z)ˣ => (by ac_rfl : x * t * w = t * (w * x))) _ _ _
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_range_div]
    have e₂ : B q' = B 0 := by
      simp only [B]
      rw [← MonObj.comp_pow, hy, MonObj.comp_one, pow_zero]
    rw [e₂, div_self', _root_.mul_one]
    obtain ⟨n, rfl⟩ := hq
    clear e e₂ hy
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, Finset.prod_range_add, ih, _root_.one_mul]
      refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) (prod_tval H π hJ ((π ≫ y ^ r) ^ (q * n) * p ^ r))
      rw [pow_add, mul_comm (_ ^ (q * n)), _root_.mul_assoc]
  · have s := val_corr hJ hs (lift π (p ^ r)).left
    rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at s
    rw [hv' _ _ z J hJ, hv' _ _ z J hJ, hw' _ _ z J hJ, hw' _ _ z J hJ, mul_inv_cancel_left, mul_pow, inv_pow, inv_pow,
      ← MonObj.comp_pow, mul_inv (π ≫ y)⁻¹, inv_inv]
    apply Additive.ofMul.injective
    replace s := congrArg Additive.ofMul s
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at s ⊢
    linear_combination (norm := abel) s

theorem sv_act {θ : ThetaGrp A L k T} {x : T ⟶ A} (hx : θ.pt = x) {s s' : LB.Sec (LPow A L k T)}
    (H : IsActOf A L k θ s s') (π : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    sv A s' (lift π p).left z J = (tval θ (lift π p).left z J).val * sv A s (lift π ((π ≫ x) * p)).left z J := by
  rw [← hx, ← lift_translT]
  exact sv_of_isTwistPull A H _ z hJ

theorem sv_mulPull {a b : ℤ} {r : ℕ}
    {β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b])}
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (H : IsTwistPull A L (mulT A T r) (snd T A ^ r) (lift_snd _ _) a b β s s') (π : T' ⟶ T) {z : T'.left} {J}
    (hJ : Good L z J) (p : T' ⟶ A) :
    sv A s' (lift π p).left z J = (bval β (lift π p).left z J).val * sv A s (lift π (p ^ r)).left z J := by
  rw [← lift_mulT]
  exact sv_of_isTwistPull A H _ z hJ

theorem sv_of_isValueAt {s : LB.Sec (LPow A L k T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L k s w τ v) (π : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) :
    sv A s (lift π (π ≫ w)).left z J = gs π.left z ⊤ v * (val τ π.left z J).val := by
  have e₀ : (lift π (π ≫ w)).left = π.left ≫ (ptSecT A w).left := by
    rw [← Over.comp_left, ptSecT, comp_lift, Category.comp_id]
  have e : (ptSecT A w).left ≫ (snd T A).left = w.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  have hz := hJ.mem (fun _ : Fin 1 => w.left) π.left
  rw [e₀]
  refine (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ z J
    (fun _ => J (π.left ≫ w.left)) (fun _ => by rw [Category.assoc, e])).trans ?_
  have key : ∀ j : Fin 1 → L.ι, π.left z ∈ LB.wchart L (fun _ : Fin 1 => w.left) j →
      gs (π.left ≫ (ptSecT A w).left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) =
        gs π.left z ⊤ v * (gm π.left z (LB.wchart L (fun _ : Fin 1 => w.left) j) (τ.s j)).val := fun j hz =>
    ((gs_res π.left z (val_le A L w j) hz _).trans (gs_pull π.left (ptSecT A w).left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (val_le A L w j hz) (s.f j))).symm.trans
    ((congrArg (gs π.left z _) (H j)).trans ((gs_mul π.left z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res π.left z le_top hz _) (gs_unit π.left z _ hz _))))
  exact key _ hz

theorem isValueAt_of_sv (hL : L.IsLB) {s : LB.Sec (LPow A L k T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} (hτ : τ.IsGen)
    {v : Γ(T.left, ⊤)} (H : ∀ (z : T.left) (J), Good L z J →
      sv A s (lift (𝟙 T) w).left z J = gs (𝟙 T.left) z ⊤ v * (val τ (𝟙 T.left) z J).val) :
    IsValueAt A L k s w τ v := by
  obtain ⟨v₀, h₀⟩ := ThetaPtExist.exists_isValueAt hL s w τ hτ
  obtain rfl : v₀ = v := fn_ext fun z _ => by
    choose J hJ using fun χ : T.left ⟶ A.left => exists_chart hL (χ z)
    have := sv_of_isValueAt h₀ (𝟙 T) hJ
    rw [Category.id_comp, H z J hJ] at this
    exact (Units.mul_left_inj _).1 this.symm
  exact h₀

theorem exists_unit_isValueAt (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {m r n q q' : ℕ}
    (hn : n = r * m) (hq : q ∣ q') (ho : Odd q') {th th' : LB.Sec (LPow A L 1 T)} {ρ : Γ(T.left, ⊤)}
    (hρ : SecM.ofSec A th = ρ • SecM.ofSec A th')
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![b, -1])} (hα : α.IsGen)
    {α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ n).left] ![a, -1])} (hα' : α'.IsGen)
    {s : LB.Sec (LPow A L b T)} {s' : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) b 1 α th s)
    (hs' : IsTwistPull A L (mulT A T n) (snd T A ^ n) (lift_snd _ _) a 1 α' th' s')
    {τ₀ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))} (hτ₀ : τ₀.IsGen)
    {Z h : T ⟶ A} (hh : Z ^ r = h) {UZ : ThetaGrp A L a T} (hZ : SymLift A L a q' Z UZ)
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => h.left) (fun _ => b))} (hτ : τ.IsGen) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (Y : T ⟶ A) (U : ThetaGrp A L b T) (t : LB.Sec (LPow A L b T)) (W : ThetaGrp A L a T)
      (t' : LB.Sec (LPow A L a T)) (w : Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)ˣ), Y ^ q' = 1 →
      SymLift A L b q (Y ^ r) U → IsActOf A L b U s t → SymLift A L a q' (Y * Z) W → IsActOf A L a W s' t' →
      IsValueAt A L a t' 1 τ₀ w → WeilIs A L a Z Y c →
      IsValueAt A L b t h τ (ρ * u * (c ^ ((q' + 1) / 2) : Γ(T.left, ⊤)ˣ) * w) := by
  have := hA.comm
  subst hn hh
  obtain rfl := hZ.pt_eq
  have e₁ : mulT A T r ≫ snd T A = snd T A ^ r := lift_snd _ _
  have e₂ : mulT A T r ≫ snd T A ^ m = snd T A ^ (r * m) := by rw [MonObj.comp_pow, e₁, pow_mul]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ r).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, ← Over.comp_left, e₁, e₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α' (LB.invGen L _ _ (LB.pullGen L _ _ α (mulT A T r).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα' (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _)))
  have vβ' : ∀ (z : T.left) (J), Good L z J → ∀ p : T ⟶ A, bval β (lift (𝟙 T) p).left z J =
      bval (b := 1) α' (lift (𝟙 T) p).left z J * (bval (b := 1) α (lift (𝟙 T) (p ^ r)).left z J)⁻¹ :=
    fun z J hJ p => by
      rw [← lift_mulT]
      exact (vβ _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (_ * ·)
        ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  have e₃ : lift (𝟙 T) (1 : T ⟶ A) ≫ translPt A UZ.pt = UZ.pt := by
    rw [translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp]
    exact _root_.mul_one UZ.pt
  obtain ⟨u, hu⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _)
    (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ← Over.comp_left, e₃, lift_snd, MonObj.comp_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module)
    (DVR.mulGen_isGen L _ _ _ _ τ₀ _ hτ₀ (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen L _ _ _ _ _ τ
      (DVR.mulGen_isGen L _ _ _ _ _ _
        (DVR.pullGen_isGen L ![(snd T A).left, (translPt A UZ.pt).left] ![a, -a] UZ.φ UZ.isGen
          (lift (𝟙 T) (1 : T ⟶ A)).left)
        (DVR.pullGen_isGen L _ _ β hβ (lift (𝟙 T) UZ.pt).left)) hτ)))
  refine ⟨u, fun Y U t W t' w c hY hU ht hW ht' hw hc => isValueAt_of_sv hL hτ fun z J hJ => ?_⟩
  obtain ⟨UY, hUY, vY⟩ := exists_symLift_mulPull hA hL hq hβ hY hU
  have a₁ := hu _ (𝟙 _) z J hJ
  have a₀ : val (LB.pullGen L ![(snd T A).left, (translPt A UZ.pt).left] ![a, -a] UZ.φ
      (lift (𝟙 T) (1 : T ⟶ A)).left) (𝟙 T.left) z J = tval UZ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
  rw [val_mul hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ β, a₀, Category.id_comp, Category.id_comp] at a₁
  have a₂ := tval_mul hG hA hL ho hY hZ hUY hW hc (𝟙 T) hJ 1
  have a₃ := vY _ (𝟙 T) z J hJ UZ.pt
  have a₄ := vβ' z J hJ (Y * UZ.pt)
  have b₁ := sv_act hU.pt_eq ht (𝟙 T) hJ (UZ.pt ^ r)
  have b₂ := sv_mulPull hs (𝟙 T) hJ ((Y * UZ.pt) ^ r)
  have b₃ := sv_act hW.pt_eq ht' (𝟙 T) hJ 1
  have b₄ := sv_mulPull hs' (𝟙 T) hJ (Y * UZ.pt)
  have b₅ := sv_of_isValueAt hw (𝟙 T) hJ
  have b₆ : sv A th (lift (𝟙 T) ((Y * UZ.pt) ^ (r * m))).left z J =
      gs (𝟙 T.left) z ⊤ ρ * sv A th' (lift (𝟙 T) ((Y * UZ.pt) ^ (r * m))).left z J := by
    have := ThetaAct.sv_smul ρ (SecM.ofSec A th') (lift (𝟙 T) ((Y * UZ.pt) ^ (r * m))).left z hJ
    rw [← hρ, lift_fst_left] at this
    exact this
  rw [Category.id_comp, ← mul_pow, b₂, ← pow_mul, b₆] at b₁
  rw [Category.id_comp, _root_.mul_one, b₄] at b₃
  rw [Category.id_comp, b₃] at b₅
  rw [Category.id_comp, _root_.mul_one, a₃, Category.id_comp, a₄] at a₂
  have key : tval U (lift (𝟙 T) (UZ.pt ^ r)).left z J * bval (b := 1) α (lift (𝟙 T) ((Y * UZ.pt) ^ r)).left z J *
      val τ₀ (𝟙 T.left) z J = gm (𝟙 T.left) z ⊤ u * gm (𝟙 T.left) z ⊤ c ^ ((q' + 1) / 2) * val τ (𝟙 T.left) z J *
        (tval W (lift (𝟙 T) (1 : T ⟶ A)).left z J * bval (b := 1) α' (lift (𝟙 T) (Y * UZ.pt)).left z J) := by
    rw [← a₁]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    simp only [ofMul_mul, ofMul_inv, tval, Over.id_left] at a₂ ⊢
    linear_combination (norm := abel) a₂
  replace key := congrArg Units.val key
  simp only [Units.val_mul] at key
  refine (Units.mul_left_inj (val τ₀ (𝟙 T.left) z J)).1 ?_
  rw [b₁, gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial, gs_mul _ _ ⊤ trivial, gs_unit _ _ ⊤ trivial,
    gs_unit _ _ ⊤ trivial, map_pow]
  simp only [Over.id_left] at b₅
  linear_combination (gs (𝟙 T.left) z ⊤ ρ * sv A th' (lift (𝟙 T) ((Y * UZ.pt) ^ (r * m))).left z J) * key +
    (gs (𝟙 T.left) z ⊤ ρ * (gm (𝟙 T.left) z ⊤ u).val * (gm (𝟙 T.left) z ⊤ c ^ ((q' + 1) / 2)).val *
      (val τ (𝟙 T.left) z J).val) * b₅

theorem exists_symLift_one (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (q : ℕ) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k q 1 θ ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ ρ z J = 1 := by
  obtain ⟨o, ho, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      rw [Fin.prod_univ_two, ThetaAct.translPt_one]; simp))
    (LB.oneGen L) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hv' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, o, ho⟩ : ThetaGrp A L k T) ρ z J = 1 := fun Z ρ z J hJ => (hv _ _ z J hJ).trans (val_one _)
  refine ⟨⟨1, o, ho⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => Finset.prod_eq_one fun j _ => hv' _ _ z J hJ)
    (fun T' π z J hJ p => ?_), hv'⟩
  rw [hv' _ _ z J hJ, hv' _ _ z J hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
    mul_inv_cancel]

theorem isActOf_self (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {m q : ℕ} (hq : Odd q)
    {ν : LB.Gen (negLB A L b T)} (hν : ν.IsGen)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])} (hα : α.IsGen)
    {th : LB.Sec (LPow A L b T)} {s : LB.Sec (LPow A L a T)}
    (hs : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a b α th s)
    {y : T ⟶ A} (hm : y ^ m = 1) (hy : y ^ q = 1) {θ : ThetaGrp A L a T} (H : SymLift A L a q y θ) :
    IsActOf A L a θ s s := by
  have := hA.comm
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν q
  obtain ⟨θ', H', v⟩ := exists_symLift_mulPull hA hL dvd_rfl hα hy (hm ▸ ho)
  have hc := SymLiftOdd.symLift_unique hG hA hL hq θ θ' H H'
  refine isTwistPull_of_sv A hL θ.isGen fun z J hJ => ?_
  have e : tval θ (lift (fst T A) (snd T A)).left z J = tval θ' (lift (fst T A) (snd T A)).left z J :=
    val_corr hJ hc _
  rw [v _ _ z J hJ, vo _ _ z J hJ] at e
  rw [SymLiftOdd.id_eq_lift, lift_translT, sv_mulPull hs _ hJ, sv_mulPull hs _ hJ, mul_pow, ← MonObj.comp_pow]
  refine Eq.trans ?_ (congrArg (fun u : ((T ⊗ A).left.presheaf.stalk z)ˣ => u.val * _) e.symm)
  rw [H.pt_eq, hm, MonObj.comp_one, _root_.one_mul, _root_.mul_one, Units.val_mul, _root_.mul_assoc,
    Units.inv_mul_cancel_left]

theorem ofSec_act_act (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {q : ℕ} (hq : Odd q) {x y : T ⟶ A}
    (hy : y ^ q = 1) {θx θy θ : ThetaGrp A L k T} (Hx : SymLift A L k q x θx) (Hy : SymLift A L k q y θy)
    (H : SymLift A L k q (y * x) θ) {c : Γ(T.left, ⊤)ˣ} (hc : WeilIs A L k x y c) {s s₁ s₂ s₃ : LB.Sec (LPow A L k T)}
    (h₁ : IsActOf A L k θy s s₁) (h₂ : IsActOf A L k θx s₁ s₂) (h₃ : IsActOf A L k θ s s₃) :
    SecM.ofSec A s₂ = ((c ^ ((q + 1) / 2) : Γ(T.left, ⊤)ˣ) : Γ(T.left, ⊤)) • SecM.ofSec A s₃ := by
  refine ThetaAct.sv_ext hL fun z J hJ => ?_
  rw [ThetaAct.sv_smul _ _ _ _ hJ, gs_unit _ _ ⊤ trivial, map_pow, Category.id_comp, SymLiftOdd.id_eq_lift]
  change sv A s₂ _ z J = _ * sv A s₃ _ z J
  rw [sv_act Hx.pt_eq h₂ _ hJ, sv_act Hy.pt_eq h₁ _ hJ, sv_act H.pt_eq h₃ _ hJ, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, tval_mul hG hA hL hq hy Hx Hy H hc _ hJ, Units.val_mul, MonObj.comp_mul, _root_.mul_assoc (_ ≫ y),
    _root_.mul_assoc]

theorem exists_symLift_act_pull (hL : L.IsLB) {n : ℕ} (h : T' ⟶ T) {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (H : SymLift A L k n x θ) : ∃ θ' : ThetaGrp A L k T', SymLift A L k n (h ≫ x) θ' ∧
      ∀ s s', IsActOf A L k θ s s' → IsActOf A L k θ' (pullS A k h s) (pullS A k h s') := by
  obtain ⟨θ', e, v⟩ := CommPairing.exists_pull hL h θ
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨ν', hν', w⟩ := exists_neg_pull hL h ν hν
  have e₀ : ∀ (T₀ : Over S) (π : T₀ ⟶ T') (p : T₀ ⟶ A), (lift π p).left ≫ (h ▷ A).left = (lift (π ≫ h) p).left :=
    fun T₀ π p => by rw [← Over.comp_left, lift_whiskerRight]
  refine ⟨θ', symLift_of_tval hL (e.trans (by rw [H.pt_eq])) hν' (fun T₀ π z J hJ p => ?_) (fun T₀ π z J hJ p => ?_),
    fun s s' hs => isTwistPull_of_sv A hL θ'.isGen fun z J hJ => ?_⟩
  · simp only [v _ _ z J hJ, e₀, ← Category.assoc]
    exact prod_tval H _ hJ p
  · have q := val_corr hJ hs (lift (π ≫ h) p).left
    rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at q
    simp only [v _ _ z J hJ, w _ _ z J hJ, e₀, ← Category.assoc]
    exact q
  · have q := v _ (lift (fst T' A) (snd T' A)).left z J hJ
    rw [SymLiftOdd.id_eq_lift, lift_translT, sv_pullS A k h _ _ z hJ, sv_pullS A k h _ _ z hJ, e₀, e₀,
      sv_act rfl hs _ hJ]
    rw [e₀] at q
    exact congrArg₂ (· * ·) (congrArg Units.val q.symm) (by rw [e, Category.assoc])

theorem isGenSec_pullS (hL : L.IsLB) (h : T' ⟶ T) (i : T ⟶ T') (hi : h ≫ i = 𝟙 T') {th : LB.Sec (LPow A L k T)}
    (H : IsGenSec A L k th) : IsGenSec A L k (pullS A k h th) := fun s => by
  obtain ⟨r, hr⟩ := H (pullS A k i s)
  have e : pullM A L k i (SecM.ofSec A s) = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have := congrArg (pullM A L k h) e
  rw [pullM_comp A hL, hi, pullM_id A hL, LinearMap.map_smulₛₗ] at this
  exact ⟨_, fun j => congrArg (fun q => q.1 j) this⟩

theorem isThetaPtOver_pull (P : PolAV S) {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T) (i : T ⟶ T') (hi : h ≫ i = 𝟙 T') :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, isGenSec_pullS hL h i hi hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem isThetaPtOver_of_subsingleton (P : PolAV S) [Subsingleton T.left] [Nonempty T.left] {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) : IsThetaPtOver P n x v := by
  obtain ⟨p⟩ := ‹Nonempty T.left›
  obtain ⟨V, hp, H'⟩ := H.2.2 p
  obtain ⟨h, hh⟩ := exists_section hp
  have hi : h ≫ overResι V = 𝟙 T := hh
  have := isThetaPtOver_pull P H' h (overResι V) hi
  convert this using 2 with a a
  · rw [← Category.assoc, hh, Category.id_comp]
  · have q := congrArg (fun q => q.left.appTop.hom (v a)) hh
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Over.id_left,
      Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at q
    exact q.symm

theorem exists_unit_of_isGenSec [Subsingleton T.left] {th th' : LB.Sec (LPow A L k T)}
    (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') := T.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun p _ => by
    rw [map_sub, map_one, map_mul]
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu ?_
    refine T.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun p' _ => ?_
    obtain rfl : p = p' := Subsingleton.elim (α := T.left) _ _
    exact isUnit_of_mul_isUnit_left h
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩

end GlobalTheory.ThetaCoord
