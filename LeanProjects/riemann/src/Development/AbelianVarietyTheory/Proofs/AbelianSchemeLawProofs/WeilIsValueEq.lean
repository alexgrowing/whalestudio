import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PairingLevels

theorem comm_eq {B U : Type} [CommGroup B] [CommGroup U] (v : B → B → B → U) (φ φ' ψ χ : B → U) (k : ℤ) (l : ℕ)
    (x y : B) (hv : ∀ a, v a x 1 * v a y x = v a y 1 * v a x y)
    (hA : ∀ w, φ (w * x) * φ 1 * v w y x ^ k = φ w * φ x * v w y 1 ^ k)
    (hB : χ y * ψ 1 * (∏ i ∈ Finset.range l, v (x ^ i) x 1) ^ k =
      χ 1 * ψ y * (∏ i ∈ Finset.range l, v (x ^ i) x y) ^ k)
    (hC : φ' x * φ 1 ^ l = φ' 1 * φ x ^ l) :
    χ 1 * φ' x * (φ' 1 * χ y)⁻¹ = ψ 1 * φ (x ^ l) * (φ 1 * ψ y)⁻¹ := by
  have key : ∀ n : ℕ, φ (x ^ n) * φ 1 ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x y) ^ k =
      φ 1 * φ x ^ n * (∏ i ∈ Finset.range n, v (x ^ i) x 1) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have a := congrArg Additive.ofMul (hA (x ^ n))
      have b := congrArg Additive.ofMul (hv (x ^ n))
      have c := congrArg Additive.ofMul ih
      rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow] at a b c ⊢
      linear_combination (norm := module) a + c - k • b
  have a := congrArg Additive.ofMul (key l)
  have b := congrArg Additive.ofMul hB
  have c := congrArg Additive.ofMul hC
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, ofMul_inv] at a b c ⊢
  linear_combination (norm := module) c - a - b

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)

def pt {Y : Over S} (a : Y ⟶ A) : FreeAbelianGroup (Y.left ⟶ A.left) := FreeAbelianGroup.of a.left

abbrev ValFam (Y : Over S) : Type 1 :=
  ∀ (Z : Over S) (_ : Z ⟶ Y) (z : Z.left) (_ : (Z.left ⟶ A.left) → L.ι), (Z.left.presheaf.stalk z)ˣ

def Rep {Y : Over S} (D : FreeAbelianGroup (Y.left ⟶ A.left)) (f : ValFam L Y) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ ∑ k, ε k • FreeAbelianGroup.of (φ k) = D ∧
      ∀ (Z : Over S) (r : Z ⟶ Y) (z : Z.left) (J), Good L z J → val t r.left z J = f Z r z J

variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}

omit [GrpObj A] in
theorem oneGen_isGen : (LB.oneGen L (Y := Y.left)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

omit [GrpObj A] in
theorem Rep.one : Rep L (Y := Y) 0 (fun _ _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L, oneGen_isGen, Fintype.sum_empty _, fun _ _ _ _ _ => val_one _⟩

omit [GrpObj A] in
theorem Rep.mul (h : Rep L D f) (h' : Rep L D' f') : Rep L (D + D') (fun Z r z J => f Z r z J * f' Z r z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hD, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hD', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_,
    fun Z r z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv Z r z J hJ) (hv' Z r z J hJ))⟩
  rw [Fintype.sum_sum_type, ← hD, ← hD']; rfl

omit [GrpObj A] in
theorem Rep.inv (h : Rep L D f) : Rep L (-D) (fun Z r z J => (f Z r z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hD, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L _ _ t, DVR.invGen_isGen _ _ _ _ ht, ?_,
    fun Z r z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (hv Z r z J hJ))⟩
  rw [← hD]; simp

omit [GrpObj A] in
theorem Rep.congr (h : Rep L D f) (hD : D = D') (hf : ∀ Z r z J, f Z r z J = f' Z r z J) : Rep L D' f' := by
  obtain rfl : f = f' := by funext Z r z J; exact hf Z r z J
  exact hD ▸ h

omit [GrpObj A] in
theorem Rep.pow (h : Rep L D f) (n : ℕ) : Rep L (n • D) (fun Z r z J => f Z r z J ^ n) := by
  induction n with
  | zero => exact Rep.one.congr (zero_smul _ _).symm (fun _ _ _ _ => (pow_zero _).symm)
  | succ n ih => exact (ih.mul h).congr (succ_nsmul _ _).symm (fun _ _ _ _ => (pow_succ _ _).symm)

omit [GrpObj A] in
theorem Rep.zpow (h : Rep L D f) (n : ℤ) : Rep L (n • D) (fun Z r z J => f Z r z J ^ n) := by
  cases n with
  | ofNat n => exact (h.pow n).congr (by simp) (fun _ _ _ _ => by simp)
  | negSucc n => exact (h.pow (n + 1)).inv.congr (negSucc_zsmul _ _).symm (fun _ _ _ _ => (zpow_negSucc _ _).symm)

theorem Rep.theta {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (s : Y ⟶ T) (a : Y ⟶ A) :
    Rep L (k • pt a - k • pt ((s ≫ θ.pt) * a)) (fun Z r z J => thetaVal θ (r ≫ s) (r ≫ a) z J) := by
  refine ⟨Fin 2, inferInstance, _, _, LB.pullGen L (K := Fin 2) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ
    (lift s a).left, DVR.pullGen_isGen _ _ _ _ θ.isGen _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_theta (k := k) θ.pt s a (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul] at this
    rw [this, neg_smul, ← sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift]; rfl

def cubeVal (t : LB.Gen (Theta A L)) {Z : Over S} (z : Z.left) (J : (Z.left ⟶ A.left) → L.ι) (a b c : Z ⟶ A) :
    (Z.left.presheaf.stalk z)ˣ := val (L := L) (φ := thφ A (x3 A)) (ε := thε) t (lift a (lift b c)).left z J

theorem Rep.cube [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (a b c : Y ⟶ A) :
    Rep L (pt (a * b * c) - pt (a * b) - pt (a * c) - pt (b * c) + pt a + pt b + pt c - pt (1 : Y ⟶ A))
      (fun Z r z J => cubeVal t z J (r ≫ a) (r ≫ b) (r ≫ c)) := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L (thφ A (x3 A)) thε t (lift a (lift b c)).left,
    DVR.pullGen_isGen _ _ _ _ ht _, ?_, fun Z r z J hJ => ?_⟩
  · have := congrArg Multiplicative.toAdd
      (prod_cub a b c (fun q => Multiplicative.ofAdd (FreeAbelianGroup.of q)))
    simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, toAdd_mul, toAdd_inv] at this
    rw [this]; simp only [sub_eq_add_neg]; rfl
  · refine (val_pull hJ _ _ _).trans ?_
    rw [← Over.comp_left, comp_lift, comp_lift]; rfl

theorem Rep.cubeProd [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (x c : Y ⟶ A) (n : ℕ) :
    Rep L (pt (x ^ n * c) - pt c - pt (x ^ n) + pt (1 : Y ⟶ A) + n • (pt x + pt c - pt (x * c) - pt (1 : Y ⟶ A)))
      (fun Z r z J => ∏ i ∈ Finset.range n, cubeVal t z J ((r ≫ x) ^ i) (r ≫ x) (r ≫ c)) := by
  induction n with
  | zero => exact Rep.one.congr (by simp) (fun _ _ _ _ => by simp)
  | succ n ih =>
    refine (ih.mul (Rep.cube ht (x ^ n) x c)).congr ?_ (fun _ _ _ _ => ?_)
    · rw [pow_succ, succ_nsmul]; abel
    · rw [Finset.prod_range_succ, MonObj.comp_pow]

theorem Rep.rigid (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {Z : Over S}
    {D : FreeAbelianGroup ((Z ⊗ A).left ⟶ A.left)} {f : ValFam L (Z ⊗ A)} (h : Rep L D f) (hD : D = 0)
    (a : Z ⟶ A) {z : Z.left} {J} (hJ : Good L z J) : f Z (lift (𝟙 Z) a) z J = f Z (lift (𝟙 Z) 1) z J := by
  obtain ⟨K, _, φ, ε, t, ht, hD', hv⟩ := h
  obtain ⟨c, hc⟩ := exists_ratio hL (φ := φ) (ε := ε) (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ g => by
      have := congrArg (FreeAbelianGroup.lift (fun q => Additive.ofMul (g q))) (hD'.trans hD)
      simp only [map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of, map_zero] at this
      refine Eq.trans ?_ (Fintype.prod_empty _).symm
      apply Additive.ofMul.injective
      simpa only [ofMul_prod, ofMul_zpow, ofMul_one] using this)
    (fst Z A).left (lift (𝟙 Z) 1).left (by rw [← Over.comp_left, lift_fst]; rfl) (surj_fst hG hA Z) ht oneGen_isGen
  rw [← hv _ _ z J hJ, ← hv _ _ z J hJ, hc _ _ z J hJ, hc _ _ z J hJ, val_one, val_one, ← Over.comp_left,
    ← Over.comp_left, lift_fst, lift_fst]

theorem commVal_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)} (ht : t.IsGen)
    {k : ℤ} {l : ℕ} {T T' Z : Over S} (χ φ' : ThetaGrp A L (k * l) T) (ψ φ : ThetaGrp A L k T') (s : Z ⟶ T)
    (s' : Z ⟶ T') (hx : s' ≫ ψ.pt = (s ≫ χ.pt) ^ l) (hy : s' ≫ φ.pt = s ≫ φ'.pt) {z : Z.left} {J}
    (hJ : Good L z J) : commVal χ φ' s 1 z J = commVal ψ φ s' 1 z J := by
  have := hA.comm
  obtain ⟨x, hx'⟩ : ∃ x, x = s ≫ χ.pt := ⟨_, rfl⟩
  obtain ⟨y, hy'⟩ : ∃ y, y = s ≫ φ'.pt := ⟨_, rfl⟩
  rw [← hx'] at hx
  rw [← hy'] at hy
  have v₁ : ∀ a b : Z ⟶ A, cubeVal t z J a 1 b = cubeVal t z J a 1 1 := fun a b => by
    simpa using (Rep.cube ht (fst Z A ≫ a) 1 (snd Z A)).rigid hG hA hL (by
      simp only [_root_.mul_one, _root_.one_mul]; abel) b hJ
  have v₂ : ∀ a b : Z ⟶ A, cubeVal t z J a b 1 = cubeVal t z J a 1 1 := fun a b => by
    simpa using (Rep.cube ht (fst Z A ≫ a) (snd Z A) 1).rigid hG hA hL (by
      simp only [_root_.mul_one, _root_.one_mul]; abel) b hJ
  have v₃ : ∀ a b c : Z ⟶ A, cubeVal t z J a b c * (cubeVal t z J a c b)⁻¹ =
      cubeVal t z J a b 1 * (cubeVal t z J a 1 b)⁻¹ := fun a b c => by
    simpa using ((Rep.cube ht (fst Z A ≫ a) (fst Z A ≫ b) (snd Z A)).mul
      (Rep.cube ht (fst Z A ≫ a) (snd Z A) (fst Z A ≫ b)).inv).rigid hG hA hL (by
        rw [mul_right_comm (fst Z A ≫ a) (snd Z A), mul_comm (snd Z A)]; abel) c hJ
  rw [commVal, commVal, ← hx', ← hy', hx, hy, _root_.mul_one, _root_.mul_one, _root_.mul_one]
  refine comm_eq (cubeVal t z J) (fun a => thetaVal φ s' a z J) (fun a => thetaVal φ' s a z J)
    (fun a => thetaVal ψ s' a z J) (fun a => thetaVal χ s a z J) k l x y (fun a => ?_) (fun w => ?_) ?_ ?_
  · have e := v₃ a x y
    rw [v₁ a x, v₂ a x, mul_inv_cancel, mul_inv_eq_one] at e
    rw [e, v₂ a x, v₂ a y]
  · have e := (((((Rep.theta φ (fst Z A ≫ s') ((fst Z A ≫ w) * snd Z A)).mul
      (Rep.theta φ (fst Z A ≫ s') 1)).mul ((Rep.cube ht (fst Z A ≫ w) (fst Z A ≫ y) (snd Z A)).zpow k)).mul
      (Rep.theta φ (fst Z A ≫ s') (fst Z A ≫ w)).inv).mul (Rep.theta φ (fst Z A ≫ s') (snd Z A)).inv).rigid
      hG hA hL (by
        rw [Category.assoc, hy, mul_left_comm (fst Z A ≫ y), _root_.mul_assoc, mul_comm (fst Z A ≫ y) (fst Z A ≫ w),
          _root_.mul_one]
        module) x hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'
  · have e := (((((Rep.theta χ (fst Z A ≫ s) (snd Z A)).mul
      (Rep.theta ψ (fst Z A ≫ s') 1)).mul ((Rep.cubeProd ht (fst Z A ≫ x) (snd Z A) l).zpow k).inv).mul
      (Rep.theta χ (fst Z A ≫ s) 1).inv).mul (Rep.theta ψ (fst Z A ≫ s') (snd Z A)).inv).rigid
      hG hA hL (by
        rw [Category.assoc, Category.assoc, hx, ← hx', MonObj.comp_pow, _root_.mul_one, _root_.mul_one]
        module) y hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'
  · have e := ((((Rep.theta φ' (fst Z A ≫ s) (snd Z A)).mul
      ((Rep.theta φ (fst Z A ≫ s') 1).pow l)).mul
      (Rep.theta φ' (fst Z A ≫ s) 1).inv).mul ((Rep.theta φ (fst Z A ≫ s') (snd Z A)).pow l).inv).rigid
      hG hA hL (by
        rw [Category.assoc, Category.assoc, hy, ← hy']
        module) x hJ
    simp only [MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp, _root_.mul_one] at e
    have e' := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv] at e' ⊢
    linear_combination (norm := module) e'

theorem weilIs_value_eq (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {t : LB.Gen (Theta A L)}
    (ht : t.IsGen) {k : ℤ} {l : ℕ} {T : Over S} {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : WeilIs A L (k * l) x y c) (h' : WeilIs A L k (x ^ l) y c') : c = c' := by
  refine unit_ext fun p _ => ?_
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', ⟨θx', θy', hx', hy'⟩, H'⟩ := h' p
  let z : (V ⊓ V').toScheme := ⟨p, hV, hV'⟩
  let s := overLE (inf_le_left : V ⊓ V' ≤ V)
  let s' := overLE (inf_le_right : V ⊓ V' ≤ V')
  choose J hJ using fun χ : (overRes (V ⊓ V')).left ⟶ A.left => exists_chart hL (χ z)
  have e₁ := (commIsOf_iff hL _ _ _).1 (H θx θy hx hy) _ s 1 z J hJ
  have e₂ := (commIsOf_iff hL _ _ _).1 (H' θx' θy' hx' hy') _ s' 1 z J hJ
  have e₃ := commVal_eq hG hA hL ht θx θy θx' θy' s s'
    (by rw [hx, hx', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι, MonObj.comp_pow])
    (by rw [hy, hy', ← Category.assoc, ← Category.assoc, overLE_ι, overLE_ι]) (z := z) hJ
  have f₁ := gm_unitRes V c (T.left.homOfLE (inf_le_left : V ⊓ V' ≤ V)) z
  have f₂ := gm_unitRes V' c' (T.left.homOfLE (inf_le_right : V ⊓ V' ≤ V')) z
  rw [Scheme.homOfLE_ι] at f₁ f₂
  exact gm_inj (V ⊓ V').ι z (U := ⊤) (U' := ⊤) trivial trivial (f₁.symm.trans (e₁.symm.trans (e₃.trans (e₂.trans f₂))))

theorem weilIs_mul_iff : GlobalFnsSt → (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (x y : T ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L k x y c) → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S) (l : ℕ) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) → x ^ (k * l) = 1 → y ^ k = 1 → (WeilIs P.A P.L (k * l) x y c ↔ WeilIs P.A P.L k (x ^ l) y c) := by
  intro hG hT _ hW S P k T l x y c _ hx hy
  obtain ⟨t, ht⟩ := hT S P P.L P.isLB
  obtain ⟨c₁, h₁, -⟩ := hW S P (k * l) T x y hx (by rw [pow_mul, hy, one_pow])
  obtain ⟨c₂, h₂, -⟩ := hW S P k T (x ^ l) y (by rw [← pow_mul, mul_comm, hx]) hy
  rw [Nat.cast_mul] at h₁
  constructor
  · intro h
    rw [weilIs_value_eq hG P.isAb P.isLB ht h h₂]; exact h₂
  · intro h
    rw [← weilIs_value_eq hG P.isAb P.isLB ht h₁ h]; exact h₁

end GlobalTheory.PairingLevels
