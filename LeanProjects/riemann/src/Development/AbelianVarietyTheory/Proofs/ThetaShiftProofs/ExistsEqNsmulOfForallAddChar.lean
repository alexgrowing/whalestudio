import Mathlib

set_option autoImplicit false

namespace GlobalTheory

namespace ConjIdeal

theorem exists_eq_nsmul_of_forall_zmod {X : Type*} [AddCommGroup X] [Module.Free ℤ X] (M : ℕ) (v : X)
    (h : ∀ t : X →+ ZMod M, t v = 0) : ∃ z : X, v = M • z := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hd : ∀ i, (M : ℤ) ∣ b.repr v i := fun i => by
    have := h ((Int.castAddHom (ZMod M)).comp (b.coord i).toAddMonoidHom)
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  refine ⟨b.repr.symm ((b.repr v).mapRange (fun n => n / (M : ℤ)) (by simp)), ?_⟩
  apply b.repr.injective
  ext i
  simp [Int.mul_ediv_cancel' (hd i)]

theorem exists_eq_nsmul_of_forall_addChar {X : Type*} [AddCommGroup X] [Module.Free ℤ X] {M : ℕ}
    (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C} (hζ : IsPrimitiveRoot ζ M) (v : X)
    (h : ∀ t : AddChar X C, (∀ x, t x ^ M = 1) → t v = 1) : ∃ z : X, v = M • z := by
  haveI : NeZero M := ⟨hM⟩
  refine exists_eq_nsmul_of_forall_zmod M v fun t => ?_
  have h1 := h ((AddChar.zmodChar M hζ.pow_eq_one).compAddMonoidHom t) fun x => by
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  rw [AddChar.compAddMonoidHom_apply, AddChar.zmodChar_apply, hζ.pow_eq_one_iff_dvd] at h1
  rw [← ZMod.val_eq_zero]
  exact Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)

variable {O : Type*} [CommRing O]

theorem dvd_of_dvd_conj (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, bar x • d y = M • z) (y : X) : ∃ z : Y, d y = M • z := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  obtain ⟨z₁, hz₁⟩ := h₁ j hj y
  obtain ⟨z₂, hz₂⟩ := h₂ (bar i) (Ideal.mem_map_of_mem bar hi) y
  rw [hbar] at hz₂
  refine ⟨z₂ + z₁, ?_⟩
  rw [smul_add, ← hz₁, ← hz₂, map_smul, ← add_smul, hij, one_smul]

theorem dvd_of_zmod (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : Y →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_zmod M _ fun t => h₂ t x hx y) y

theorem dvd_of_addChar (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ Y] (d : X →ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, d (x • y) = M • z)
    (h₂ : ∀ t : AddChar Y C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 1) (y : X) :
    ∃ z : Y, d y = M • z :=
  dvd_of_dvd_conj bar hbar I hsup M d h₁
    (fun x hx y => exists_eq_nsmul_of_forall_addChar hM hζ _ fun t ht => h₂ t ht x hx y) y

theorem trans_symm_congr_one (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) {M : ℕ} (hM : M ≠ 0) {C : Type*} [CommMonoid C] {ζ : C}
    (hζ : IsPrimitiveRoot ζ M) {X Y : Type*} [AddCommGroup X] [Module O X] [AddCommGroup Y]
    [Module O Y] [Module.Free ℤ X] (e₁ e₂ : X ≃ₗ[O] Y)
    (h₁ : ∀ x ∈ I.map bar, ∀ y, ∃ z : Y, e₂ (x • y) = e₁ (x • y) + M • z)
    (h₂ : ∀ t : AddChar X C, (∀ v, t v ^ M = 1) → ∀ x ∈ I.map bar, ∀ χ : Y,
      t (bar x • e₁.symm χ) = t (bar x • e₂.symm χ)) (y : X) :
    ∃ z : X, e₁.trans e₂.symm y = y + M • z := by
  obtain ⟨z, hz⟩ := dvd_of_addChar bar hbar I hsup hM hζ
    ((e₁.trans e₂.symm).toLinearMap - LinearMap.id) (fun x hx y => by
      obtain ⟨z, hz⟩ := h₁ x hx y
      refine ⟨-e₂.symm z, ?_⟩
      have h : e₁ (x • y) = e₂ (x • y) - M • z := by rw [hz]; abel
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [h, map_sub, map_nsmul, e₂.symm_apply_apply, smul_neg]
      abel) (fun t ht x hx y => by
      have h := h₂ t ht x hx (e₁ y)
      rw [e₁.symm_apply_apply] at h
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearMap.id_apply]
      rw [smul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, ← h, ← AddChar.map_add_eq_mul,
        add_neg_cancel, AddChar.map_zero_eq_one]) y
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

theorem fix_torsion_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : G → G → A)
    (e_mul : ∀ x x' y, x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → e x y = 1) → x = 1)
    (e_adj : ∀ a x y, x ^ M = 1 → y ^ M = 1 → e (act a x) y = e x (act (bar a) y))
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, x ^ M = 1 → y ^ M = 1 → e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hsup)
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  have act_zero : ∀ y, act 0 y = 1 := fun y => by
    have := act_add 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.mp this
  have act_nat : ∀ (n : ℕ) y, act (n : O) y = y ^ n := fun n y => by
    induction n with
    | zero => simpa using act_zero y
    | succ n ih => rw [Nat.cast_succ, act_add, ih, act_one, pow_succ]
  have e_one : ∀ y, y ^ M = 1 → e 1 y = 1 := fun y hy => by
    have := e_mul 1 1 y (one_pow _) (one_pow _) hy
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have e_one' : ∀ y, y ^ M = 1 → e y 1 = 1 := fun y hy => by
    have := e_adj 0 y 1 hy (one_pow _)
    rw [act_zero, map_one, e_one 1 (one_pow _)] at this
    exact this.symm
  have split : ∀ w y, w ^ M = 1 → y ^ M = 1 → e w y = e w (act i y) * e w (act j y) := fun w y hw hy => by
    have h1 : w = act (bar.symm i) w * act (bar.symm j) w := by
      rw [← act_add, ← map_add, hij, map_one, act_one]
    conv_lhs => rw [h1]
    rw [e_mul _ _ _ (tors _ _ hw) (tors _ _ hw) hy, e_adj _ _ _ hw hy, e_adj _ _ _ hw hy,
      bar.apply_symm_apply, bar.apply_symm_apply]
  have hm : (θ x * x⁻¹) ^ M = 1 := by rw [mul_pow, tors θ x hx, inv_pow, hx, inv_one, mul_one]
  have hu : act i x ^ M = 1 := tors _ _ hx
  have hw : θ (act i x) = act i (θ x * x⁻¹) * act i x := by
    rw [← map_mul, θ_act _ _ hx, inv_mul_cancel_right]
  have key : act i (θ x * x⁻¹) = 1 := by
    refine e_nondeg _ (tors _ _ hm) fun y hy => ?_
    rw [split _ _ (tors _ _ hm) hy]
    have hA : e (act i (θ x * x⁻¹)) (act i y) = 1 := by
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (hIJ (Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem bar hi)))
      rw [e_adj _ _ _ hm (tors _ _ hy), ← act_mul, mul_comm (bar i), ← hc, act_mul, act_nat, hy,
        map_one, e_one' _ hm]
    have hB : e (act i (θ x * x⁻¹)) (act j y) = 1 := by
      have hv : act j y ^ M = 1 := tors _ _ hy
      have h := θ_iso _ _ hu hv
      rw [θ_fix j hj y hy, hw, e_mul _ _ _ (tors _ _ hm) hu hv] at h
      exact mul_eq_right.mp h
    rw [hA, hB, mul_one]
  have hx' : x = act i x * act j x := by rw [← act_add, hij, act_one]
  conv_lhs => rw [hx']
  rw [map_mul, hw, key, one_mul, θ_fix j hj x hx, ← hx']

theorem fix_torsion_of_fix_conj_rel (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {G A : Type*} [CommGroup G] [CommGroup A]
    (act : O → G →* G) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (R : G → G → A → Prop)
    (R_ex : ∀ x y, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (R_mul : ∀ x x' y c c', x ^ M = 1 → x' ^ M = 1 → y ^ M = 1 → R x y c → R x' y c' →
      R (x * x') y (c * c'))
    (R_nondeg : ∀ x, x ^ M = 1 → (∀ y, y ^ M = 1 → R x y 1) → x = 1)
    (R_adj : ∀ a x y c, x ^ M = 1 → y ^ M = 1 → R x (act (bar a) y) c → R (act a x) y c)
    (θ : G →* G) (θ_act : ∀ a x, x ^ M = 1 → θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → R (θ x) (θ y) c)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, y ^ M = 1 → θ (act a y) = act a y)
    (x : G) (hx : x ^ M = 1) : θ x = x := by
  classical
  have tors : ∀ (f : G →* G) y, y ^ M = 1 → f y ^ M = 1 := fun f y hy => by
    rw [← map_pow, hy, map_one]
  let e : G → G → A := fun x y => if h : ∃ c, R x y c then h.choose else 1
  have he : ∀ x y, x ^ M = 1 → y ^ M = 1 → R x y (e x y) := fun x y hx hy => by
    have h : ∃ c, R x y c := (R_ex x y hx hy).exists
    simp only [e, dif_pos h]
    exact h.choose_spec
  have hu : ∀ x y c, x ^ M = 1 → y ^ M = 1 → R x y c → e x y = c := fun x y c hx hy h =>
    (R_ex x y hx hy).unique (he x y hx hy) h
  refine fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e ?_ ?_ ?_ θ θ_act ?_
    θ_fix x hx
  · intro x x' y hx hx' hy
    exact hu _ _ _ (by rw [mul_pow, hx, hx', mul_one]) hy
      (R_mul _ _ _ _ _ hx hx' hy (he _ _ hx hy) (he _ _ hx' hy))
  · intro x hx h
    exact R_nondeg x hx fun y hy => h y hy ▸ he x y hx hy
  · intro a x y hx hy
    exact hu _ _ _ (tors _ _ hx) hy (R_adj _ _ _ _ hx hy (he _ _ hx (tors _ _ hy)))
  · intro x y hx hy
    exact hu _ _ _ (tors _ _ hx) (tors _ _ hy) (θ_iso _ _ _ hx hy (he _ _ hx hy))

theorem eq_id_of_fix_conj_mul (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [CommGroup N] [CommGroup A]
    (hN : ∀ x : N, x ^ M = 1) (act : O → N →* N) (act_one : ∀ x, act 1 x = x)
    (act_add : ∀ a b x, act (a + b) x = act a x * act b x)
    (act_mul : ∀ a b x, act (a * b) x = act a (act b x))
    (e : N → N → A) (e_mul : ∀ x x' y, e (x * x') y = e x y * e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 1) → x = 1)
    (e_adj : ∀ a x y, e (act a x) y = e x (act (bar a) y))
    (θ : N →* N) (θ_act : ∀ a x, θ (act a x) = act a (θ x))
    (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (act a y) = act a y) : θ = MonoidHom.id N :=
  MonoidHom.ext fun x => fix_torsion_of_fix_conj bar I hsup M hIJ act act_one act_add act_mul e
    (fun x x' y _ _ _ => e_mul x x' y) (fun x _ h => e_nondeg x fun y => h y (hN y))
    (fun a x y _ _ => e_adj a x y) θ (fun a x _ => θ_act a x) (fun x y _ _ => θ_iso x y)
    (fun a ha y _ => θ_fix a ha y) x (hN x)

theorem eq_id_of_fix_conj (bar : O ≃+* O) (I : Ideal O) (hsup : I ⊔ I.map bar = ⊤) (M : ℕ)
    (hIJ : I * I.map bar ≤ Ideal.span {(M : O)}) {N A : Type*} [AddCommGroup N] [Module O N]
    [AddCommGroup A] (hN : ∀ x : N, M • x = 0)
    (e : N → N → A) (e_add : ∀ x x' y, e (x + x') y = e x y + e x' y)
    (e_nondeg : ∀ x, (∀ y, e x y = 0) → x = 0)
    (e_adj : ∀ (a : O) x y, e (a • x) y = e x (bar a • y))
    (θ : N →ₗ[O] N) (θ_iso : ∀ x y, e (θ x) (θ y) = e x y)
    (θ_fix : ∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) : θ = LinearMap.id := by
  have h := eq_id_of_fix_conj_mul bar I hsup M hIJ (N := Multiplicative N) (A := Multiplicative A)
    (fun x => hN x.toAdd)
    (fun a => AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom N a))
    (fun x => one_smul O x.toAdd) (fun a b x => add_smul a b x.toAdd)
    (fun a b x => mul_smul a b x.toAdd)
    (fun x y => Multiplicative.ofAdd (e x.toAdd y.toAdd)) (fun x x' y => e_add _ _ _)
    (fun x h => e_nondeg x.toAdd fun y => h (Multiplicative.ofAdd y)) (fun a x y => e_adj a _ _)
    (AddMonoidHom.toMultiplicative θ.toAddMonoidHom) (fun a x => θ.map_smul a x.toAdd)
    (fun x y => θ_iso _ _) (fun a ha y => θ_fix a ha _)
  ext x
  exact DFunLike.congr_fun h (Multiplicative.ofAdd x)

theorem level_rigidity (bar : O ≃+* O) (hbar : ∀ a, bar (bar a) = a) (I : Ideal O)
    (hsup : I ⊔ I.map bar = ⊤) (M : ℕ) (hIJ : I * I.map bar = Ideal.span {(M : O)}) :
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] (d : X →ₗ[O] X),
      (∀ x ∈ I.map bar, ∀ y, ∃ z : X, d (x • y) = M • z) →
      (∀ t : X →+ ZMod M, ∀ x ∈ I.map bar, ∀ y, t (bar x • d y) = 0) →
      ∀ y, ∃ z : X, d y = M • z) ∧
    (∀ (N A : Type) [AddCommGroup N] [Module O N] [AddCommGroup A], (∀ x : N, M • x = 0) →
      ∀ e : N →+ N →+ A, (∀ x, e x = 0 → x = 0) → (∀ (a : O) x y, e (a • x) y = e x (bar a • y)) →
      ∀ θ : N ≃ₗ[O] N, (∀ x y, e (θ x) (θ y) = e x y) → (∀ a ∈ I.map bar, ∀ y, θ (a • y) = a • y) →
      θ = LinearEquiv.refl O N) := by
  refine ⟨fun X _ _ _ d h₁ h₂ y => dvd_of_zmod bar hbar I hsup M d h₁ h₂ y,
    fun N A _ _ _ hN e hnd hadj θ hiso hfix => ?_⟩
  have h := eq_id_of_fix_conj bar I hsup M hIJ.le hN (fun x y => e x y)
    (fun x x' y => by simp) (fun x h => hnd x (AddMonoidHom.ext h)) hadj θ.toLinearMap hiso hfix
  exact LinearEquiv.toLinearMap_injective h

end ConjIdeal

end GlobalTheory
