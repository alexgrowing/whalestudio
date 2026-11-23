import Mathlib

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem normOrd_mul_mem_iff {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) (b : B) :
    b * a ∈ P ^ (n + 1) ↔ b ∈ P := by
  constructor
  · intro h
    by_contra hb
    have hcop : IsCoprime (Ideal.span {b}) (P ^ (n + 1)) := by
      refine IsCoprime.pow_right ?_
      rw [Ideal.isCoprime_iff_sup_eq]
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hb
      rw [Ideal.eq_top_iff_one, ← hyi]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self b)))
        (Ideal.mem_sup_right hi)
    rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hcop
    obtain ⟨y, hy, z, hz, hyz⟩ := hcop
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    apply ha'
    have : a = r * (b * a) + z * a := by
      calc a = (r * b + z) * a := by rw [hyz, one_mul]
        _ = r * (b * a) + z * a := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hz)
  · intro hb
    rw [pow_succ']
    exact Ideal.mul_mem_mul hb ha

theorem normOrd_le_span_sup {B : Type} [CommRing B] [IsDedekindDomain B] {P : Ideal B}
    [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {n : ℕ} {a : B} (ha : a ∈ P ^ n) (ha' : a ∉ P ^ (n + 1)) :
    P ^ n ≤ Ideal.span {a} ⊔ P ^ (n + 1) := by
  classical
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP.isPrime
  set I := Ideal.span {a} ⊔ P ^ (n + 1) with hI
  have hIdvd : I ∣ P ^ (n + 1) := Ideal.dvd_iff_le.mpr le_sup_right
  obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow hPprime (n + 1)).mp hIdvd
  have hIk : I = P ^ k := associated_iff_eq.mp hassoc
  have hIle : I ≤ P ^ n := sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ha) (Ideal.pow_le_pow_right (Nat.le_succ n))
  have hPnu : ¬ IsUnit P := by rw [Ideal.isUnit_iff]; exact hP.ne_top
  have hnk : n ≤ k := by
    have : P ^ n ∣ P ^ k := Ideal.dvd_iff_le.mpr (hIk ▸ hIle)
    exact (pow_dvd_pow_iff hPprime.ne_zero hPnu).mp this
  rcases Nat.lt_or_ge n k with h | h
  · exfalso
    have hk' : k = n + 1 := by omega
    apply ha'
    have : a ∈ I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
    rwa [hIk, hk'] at this
  · have : k = n := by omega
    rw [hIk, this]

theorem normOrd_length_succ (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [hP : P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ (n + 1)) = length O (B ⧸ P) + length O (B ⧸ P ^ n) := by
  classical
  obtain ⟨a, ha, ha'⟩ : ∃ a ∈ P ^ n, a ∉ P ^ (n + 1) := by
    by_contra hcon
    push_neg at hcon
    have hle : P ^ n ≤ P ^ (n + 1) := hcon
    have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP.isPrime
    have hPnu : ¬ IsUnit P := by rw [Ideal.isUnit_iff]; exact hP.ne_top
    have := (pow_dvd_pow_iff hPprime.ne_zero hPnu).mp (Ideal.dvd_iff_le.mpr hle)
    omega
  let φ : B →ₗ[B] B ⧸ P ^ (n + 1) := (P ^ (n + 1)).mkQ ∘ₗ LinearMap.mulRight B a
  have hφ : P ≤ LinearMap.ker φ := by
    intro x hx
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact (normOrd_mul_mem_iff ha ha' x).mpr hx
  let f : B ⧸ P →ₗ[O] B ⧸ P ^ (n + 1) := (P.liftQ φ hφ).restrictScalars O
  let g : B ⧸ P ^ (n + 1) →ₗ[O] B ⧸ P ^ n :=
    (Submodule.factor (Ideal.pow_le_pow_right (Nat.le_succ n) : P ^ (n + 1) ≤ P ^ n)).restrictScalars O
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      have hx' : x * a ∈ P ^ (n + 1) := by
        have := hx
        simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
          LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        exact this
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((normOrd_mul_mem_iff ha ha' x).mp hx')
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      change (Submodule.Quotient.mk x : B ⧸ P ^ n) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, Set.mem_range]
      constructor
      · intro hx
        have hx2 := normOrd_le_span_sup hP0 ha ha' hx
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
        obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
        refine ⟨Submodule.Quotient.mk r, ?_⟩
        simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
          LinearMap.mulRight_apply, Submodule.mkQ_apply]
        rw [Submodule.Quotient.eq]
        have : r * a - x = -z := by rw [← hyz]; ring
        rw [this]
        exact neg_mem hz
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H r =>
          simp only [f, φ, LinearMap.restrictScalars_apply, Submodule.liftQ_apply, LinearMap.comp_apply,
            LinearMap.mulRight_apply, Submodule.mkQ_apply] at hw
          rw [Submodule.Quotient.eq] at hw
          have hra : r * a ∈ P ^ n := Ideal.mul_mem_left _ _ ha
          have hd : r * a - x ∈ P ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hw
          have : x = r * a - (r * a - x) := by ring
          rw [this]
          exact Ideal.sub_mem _ hra hd
  exact Module.length_eq_add_of_exact f g hf hg hex

theorem normOrd_length_pow (O B : Type) [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (P : Ideal B) [P.IsMaximal] (hP0 : P ≠ ⊥) (n : ℕ) :
    length O (B ⧸ P ^ n) = n * length O (B ⧸ P) := by
  induction n with
  | zero =>
    have : Subsingleton (B ⧸ P ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    rw [Module.length_eq_zero_iff.mpr this]
    simp
  | succ n ih =>
    rw [normOrd_length_succ O B P hP0 n, ih]
    push_cast
    ring

theorem normOrd_length_residue (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
    [Module.Finite O B] (Q : Ideal B) [Q.IsMaximal] :
    length O (B ⧸ Q) = Q.inertiaDeg O := by
  classical
  set p := Q.under O with hp
  haveI : p.IsMaximal := Ideal.IsMaximal.under O Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  rw [← Ideal.inertiaDeg_eq_inertiaDeg' p Q, Ideal.inertiaDeg_algebraMap]
  letI : Field (O ⧸ p) := Ideal.Quotient.field p
  haveI : Module.Finite (O ⧸ p) (B ⧸ Q) := Module.Finite.of_restrictScalars_finite O _ _
  rw [← Module.length_eq_finrank]
  have hsurj : Function.Surjective (algebraMap O (O ⧸ p)) := Ideal.Quotient.mk_surjective
  let e : Submodule (O ⧸ p) (B ⧸ Q) ≃o Submodule O (B ⧸ Q) :=
    { toFun := fun N => N.restrictScalars O
      invFun := fun N =>
        { carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun c x hx => by
            obtain ⟨a, rfl⟩ := hsurj c
            rw [algebraMap_smul]
            exact N.smul_mem a hx }
      left_inv := fun N => Submodule.ext fun _ => Iff.rfl
      right_inv := fun N => Submodule.ext fun _ => Iff.rfl
      map_rel_iff' := Iff.rfl }
  have key : ∀ (x y : WithBot ℕ∞) (hx : x ≠ ⊥) (hy : y ≠ ⊥), x = y → x.unbot hx = y.unbot hy := by
    rintro x y hx hy rfl
    rfl
  unfold Module.length
  exact key _ _ _ _ (Order.krullDim_eq_of_orderIso e).symm

end ReciprocityTheory.MultiplicativeHeights
