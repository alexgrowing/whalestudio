import Mathlib
open Matrix

namespace GlobalTheory.SympTower

theorem rank_le_of_smul_sub_eq_zero {R : Type} [CommRing R] [Finite R] {r : ℕ} {ι : Type}
    [Fintype ι] (φ : (ι → R) →ₗ[R] (Fin r → R)) (ψ : (Fin r → R) →ₗ[R] (ι → R)) (c : R)
    (hc : c ≠ 0) (h : ∀ x, c • (x - φ (ψ x)) = 0) : r ≤ Fintype.card ι := by
  classical
  let S := {y : R // ∃ z, y = c * z}
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Nontrivial S := ⟨⟨⟨c, 1, by simp⟩, ⟨0, 0, by simp⟩, fun h => hc (congrArg Subtype.val h)⟩⟩
  have key : ∀ s : Fin r → S, ∃ x : Fin r → R, (fun i => (s i).1) = c • x := by
    intro s
    choose z hz using fun i => (s i).2
    exact ⟨z, funext fun i => by simpa using hz i⟩
  let f : (Fin r → S) → (ι → S) := fun s j => ⟨ψ (fun i => (s i).1) j, by
    obtain ⟨x, hx⟩ := key s
    exact ⟨ψ x j, by rw [hx]; simp⟩⟩
  have hφ : ∀ s : Fin r → S, φ (ψ (fun i => (s i).1)) = fun i => (s i).1 := by
    intro s
    obtain ⟨x, hx⟩ := key s
    have := h x
    rw [smul_sub, sub_eq_zero] at this
    rw [hx, map_smul, map_smul, ← this]
  have hf : Function.Injective f := by
    intro s t hst
    have h1 : ψ (fun i => (s i).1) = ψ (fun i => (t i).1) :=
      funext fun j => congrArg Subtype.val (congrFun hst j)
    have h2 := hφ s
    rw [h1, hφ t] at h2
    exact funext fun i => Subtype.ext (congrFun h2 i).symm
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fun, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).1 hcard

theorem exists_eq_one {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    (f : V →ₗ[ZMod n] ZMod n) (h : ∀ c : ZMod n, (∀ y, c * f y = 0) → c = 0) : ∃ y, f y = 1 := by
  haveI : IsPrincipalIdealRing (ZMod n) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal (LinearMap.range f)).principal
  have hreg : d ∈ nonZeroDivisors (ZMod n) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    apply h
    intro y
    have : f y ∈ Submodule.span (ZMod n) {d} := hd ▸ LinearMap.mem_range_self f y
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← ha, smul_eq_mul, mul_left_comm, hc, mul_zero]
  have hu : IsUnit d := IsArtinianRing.isUnit_of_mem_nonZeroDivisors hreg
  have : (1 : ZMod n) ∈ LinearMap.range f := by
    rw [hd]
    obtain ⟨u, rfl⟩ := hu
    exact Submodule.mem_span_singleton.2 ⟨↑u⁻¹, by simp⟩
  exact this

theorem exists_faithful {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module (ZMod n) V]
    [Finite V] (h : ∀ c : ZMod n, (∀ y : V, c • y = 0) → c = 0) :
    ∃ x : V, ∀ c : ZMod n, c • x = 0 → c = 0 := by
  obtain ⟨x, hx⟩ := AddMonoid.exists_addOrderOf_eq_exponent (G := V) AddMonoid.ExponentExists.of_finite
  refine ⟨x, fun c hc => h c fun y => ?_⟩
  rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hc ⊢
  obtain ⟨m, hm⟩ := addOrderOf_dvd_of_nsmul_eq_zero hc
  rw [hm, hx, mul_nsmul, AddMonoid.exponent_nsmul_eq_zero, nsmul_zero]

theorem exists_pairs {n : ℕ} [NeZero n] {g : ℕ}
    (ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n)
    (halt : ∀ x, ω x x = 0) (hnd : ∀ x, (∀ y, ω x y = 0) → x = 0) (k : ℕ) (hk : k ≤ g) :
    ∃ v w : Fin k → (Fin (2 * g) → ZMod n), (∀ i j, ω (v i) (v j) = 0) ∧
      (∀ i j, ω (w i) (w j) = 0) ∧ ∀ i j, ω (v i) (w j) = if i = j then 1 else 0 := by
  classical
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at this
    linear_combination this
  induction k with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨v, w, hv, hw, hvw⟩ := ih (by omega)
    let φ : (Fin k ⊕ Fin k → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) :=
      Fintype.linearCombination (ZMod n) (Sum.elim v w)
    let ψ : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin k ⊕ Fin k → ZMod n) :=
      LinearMap.pi (Sum.elim (fun i => ω.flip (w i)) (fun i => ω (v i)))
    have hφψ : ∀ x, φ (ψ x) = ∑ i, ω x (w i) • v i + ∑ i, ω (v i) x • w i := by
      intro x
      simp [φ, ψ, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    let K : Submodule (ZMod n) (Fin (2 * g) → ZMod n) :=
      { carrier := {x | ∀ j, ω (v j) x = 0 ∧ ω x (w j) = 0}
        add_mem' := fun ha hb j => by simp [(ha j).1, (ha j).2, (hb j).1, (hb j).2]
        zero_mem' := fun j => by simp
        smul_mem' := fun c x hx j => by simp [(hx j).1, (hx j).2] }
    have hp : ∀ x, x - φ (ψ x) ∈ K := by
      intro x j
      rw [hφψ]
      constructor
      · simp [map_sum, hv, hvw]
      · simp [map_sum, LinearMap.sum_apply, hw, hvw]
    have hKp : ∀ x ∈ K, ∀ y, ω x (y - φ (ψ y)) = ω x y := by
      intro x hx y
      have h1 : ∀ j, ω x (v j) = 0 := fun j => by rw [hsk, (hx j).1, neg_zero]
      rw [hφψ]
      simp [map_sum, h1, fun j => (hx j).2]
    obtain ⟨x, hx⟩ := exists_faithful (n := n) (V := K) (by
      intro c hc
      by_contra hc0
      have := rank_le_of_smul_sub_eq_zero φ ψ c hc0
        (fun x => congrArg Subtype.val (hc ⟨_, hp x⟩))
      simp at this
      omega)
    obtain ⟨y, hy⟩ := exists_eq_one ((ω x.1).comp K.subtype) (by
      intro c hc
      apply hx
      apply Subtype.ext
      apply hnd
      intro y
      have := hc ⟨_, hp y⟩
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, hKp x.1 x.2] at this
      simpa using this)
    have hxv : ∀ j, ω x.1 (v j) = 0 := fun j => by rw [hsk, (x.2 j).1, neg_zero]
    have hwy : ∀ j, ω (w j) y.1 = 0 := fun j => by rw [hsk, (y.2 j).2, neg_zero]
    refine ⟨Fin.cons x.1 v, Fin.cons y.1 w, ?_, ?_, ?_⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hxv, hv, (x.2 _).1]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [halt, hwy, hw, (y.2 _).2]
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hy
      · simp [(x.2 _).2, (Fin.succ_ne_zero j).symm]
      · simp [(y.2 _).1]
      · simp [hvw]

theorem exists_level {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (h2 : ∀ x y z, e x (y + z) = e x y * e x z) (h3 : ∀ x, e x x = 1)
    (h4 : ∀ x, (∀ y, e x y = 1) → x = 0) :
    ∃ ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G,
      ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  let χ : ZMod n → Fˣ := fun a => ((Additive.toMul (hζ.zmodEquivZPowers a) : Subgroup.zpowers ζ) : Fˣ)
  have χadd : ∀ a b, χ (a + b) = χ a * χ b := by intro a b; simp [χ]
  have χinj : Function.Injective χ := by
    intro a b h
    exact hζ.zmodEquivZPowers.injective (Additive.toMul.injective (Subtype.ext h))
  have χint : ∀ i : ℤ, χ i = ζ ^ i := by
    intro i; simp only [χ, hζ.zmodEquivZPowers_apply_coe_int]; rfl
  have χ0 : χ 0 = 1 := by simpa using χint 0
  have hpow : ∀ x y, e x y ^ n = 1 := by
    intro x y
    let f : G →+ Additive Fˣ := AddMonoidHom.mk' (fun x => Additive.ofMul (e x y))
      (fun a b => by rw [h1]; rfl)
    have hx : n • x = 0 := Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
    have := map_nsmul f n x
    rw [hx, map_zero] at this
    exact (congrArg Additive.toMul this).symm
  have hex : ∀ x y, ∃ a, χ a = e (Φ.symm x) (Φ.symm y) := by
    intro x y
    have hm : e (Φ.symm x) (Φ.symm y) ∈ Subgroup.zpowers ζ := by
      rw [hζ.zpowers_eq, mem_rootsOfUnity]; exact hpow _ _
    obtain ⟨i, hi⟩ := hm
    exact ⟨i, by rw [χint]; exact hi⟩
  choose b hb using hex
  have b1 : ∀ x y z, b (x + y) z = b x z + b y z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add, h1])
  have b2 : ∀ x y z, b x (y + z) = b x y + b x z := fun x y z =>
    χinj (by rw [χadd, hb, hb, hb, map_add, h2])
  let ω : (Fin (2 * g) → ZMod n) →ₗ[ZMod n] (Fin (2 * g) → ZMod n) →ₗ[ZMod n] ZMod n :=
    LinearMap.mk₂ (ZMod n) b b1
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun x => b x y) (fun x z => b1 x z y)) c x)
      b2
      (fun c x y => ZMod.map_smul (AddMonoidHom.mk' (fun y => b x y) (fun y z => b2 x y z)) c y)
  have hω : ∀ x y, χ (ω x y) = e (Φ.symm x) (Φ.symm y) := hb
  have halt : ∀ x, ω x x = 0 := fun x => χinj (by rw [hω, h3, χ0])
  have hsk : ∀ x y, ω x y = - ω y x := by
    intro x y
    have := halt (x + y)
    simp only [map_add, LinearMap.add_apply, halt] at this
    linear_combination this
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_pairs ω halt (by
    intro x hx
    have := h4 (Φ.symm x) (fun y => by
      have := hω x (Φ y)
      rw [hx, χ0, Φ.symm_apply_apply] at this
      exact this.symm)
    exact Φ.symm.injective (by rw [this, map_zero])) g le_rfl
  have hwv : ∀ i j, ω (w i) (v j) = if j = i then -1 else 0 := by
    intro i j; rw [hsk, hvw]; split_ifs <;> simp
  let E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ (Fin (2 * g) → ZMod n) :=
    AddMonoidHom.mk' (fun a => ∑ i, (a.1 i : ZMod n) • v i + ∑ i, (a.2 i : ZMod n) • w i)
      (fun a b => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add, add_smul,
          Finset.sum_add_distrib]
        abel)
  refine ⟨Φ.symm.toAddMonoidHom.comp E, fun a c => ?_⟩
  change e (Φ.symm (E a)) (Φ.symm (E c)) = _
  rw [← hω, ← χint]
  congr 1
  simp [E, map_sum, LinearMap.sum_apply, hv, hw, hvw, hwv, dotProduct, mul_comm]
  ring

theorem ker_and_surj {F : Type} [Field F] {ζ : Fˣ} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) {g : ℕ} {G : Type} [AddCommGroup G] (e : G → G → Fˣ)
    (Φ : G ≃+ (Fin (2 * g) → ZMod n)) (h1 : ∀ x y z, e (x + y) z = e x z * e y z)
    (ev : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G)
    (hev : ∀ a b, e (ev a) (ev b) = ζ ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) :
    (∀ a b, ev a = ev b ↔ ∃ e', a = b + n • e') ∧ Function.Surjective ev := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnx : ∀ x : G, n • x = 0 := fun x => Φ.injective (by
      rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul])
  have h0 : ∀ y, e 0 y = 1 := by
    intro y
    have := h1 0 0 y
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hker : ∀ a, ev a = 0 → (∀ i, (n : ℤ) ∣ a.1 i) ∧ ∀ i, (n : ℤ) ∣ a.2 i := by
    intro a ha
    constructor
    · intro i
      have := hev a (0, Pi.single i 1)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
    · intro i
      have := hev a (Pi.single i 1, 0)
      rw [ha, h0, eq_comm, hζ.zpow_eq_one_iff_dvd] at this
      simpa using this
  refine ⟨fun a b => ⟨fun h => ?_, ?_⟩, ?_⟩
  · obtain ⟨ha, hb⟩ := hker (a - b) (by rw [map_sub, h, sub_self])
    choose c hc using ha
    choose d hd using hb
    refine ⟨(c, d), ?_⟩
    ext i
    · have := hc i
      simp at this ⊢
      linarith
    · have := hd i
      simp at this ⊢
      linarith
  · rintro ⟨c, rfl⟩
    rw [map_add, map_nsmul, hnx, add_zero]
  · let f : (Fin g → ZMod n) × (Fin g → ZMod n) → G :=
      fun a => ev (fun i => ((a.1 i).val : ℤ), fun i => ((a.2 i).val : ℤ))
    have hf : Function.Injective f := by
      intro a b h
      obtain ⟨ha, hb⟩ := hker (_ - _) (by rw [map_sub]; exact sub_eq_zero.2 h)
      ext i
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (ha i)
        simpa [sub_eq_zero] using this
      · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).2 (hb i)
        simpa [sub_eq_zero] using this
    haveI : Fintype G := Fintype.ofEquiv _ Φ.symm.toEquiv
    have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by
      rw [Fintype.card_congr Φ.toEquiv]
      simp [two_mul, pow_add]⟩
    intro x
    obtain ⟨a, ha⟩ := hb.2 x
    exact ⟨_, ha⟩

theorem exists_compatible_symplectic : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  intro F _ ζ hζ hζc g G _ e π hG h1 h2 h3 h4 hπ hcomp
  classical
  have hlev : ∀ M : ℕ, ∃ E : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G M.factorial,
      ∀ a b, e _ (E a) (E b) = ζ M.factorial ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := fun M =>
    exists_level M.factorial_pos (hζ _ M.factorial_pos) (e _) (hG _ M.factorial_pos).some
      (h1 _) (h2 _) (h3 _) (h4 _ M.factorial_pos)
  choose E hE using hlev
  have hpush : ∀ n M, 0 < M → n ∣ M → ∀ (x y : G M) (i : ℤ), e M x y = ζ M ^ i →
      e n (π M n x) (π M n y) = ζ n ^ i := by
    rintro n _ hM ⟨m, rfl⟩ x y i h
    have hn : 0 < n := Nat.pos_of_mul_pos_right hM
    have hm : 0 < m := Nat.pos_of_mul_pos_left hM
    rw [hπ n m hn hm, h, ← hζc n m hn hm, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul,
      mul_comm i]
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n, 0 < n → ∀ᶠ k in (U : Filter ℕ), n ∣ k.factorial := by
    intro n hn
    apply Filter.Eventually.filter_mono Filter.hyperfilter_le_cofinite
    rw [Nat.cofinite_eq_atTop]
    exact (Filter.eventually_ge_atTop n).mono fun k hk => Nat.dvd_factorial hn hk
  have hlim : ∀ n, ∃ f : ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, 0 < n →
      ∀ a, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = f a := by
    intro n
    by_cases hn : 0 < n
    · haveI : NeZero n := ⟨hn.ne'⟩
      haveI : Finite (G n) := Finite.of_equiv _ (hG n hn).some.symm.toEquiv
      have : ∀ a, ∃ x, ∀ᶠ k in (U : Filter ℕ), π k.factorial n (E k a) = x := by
        intro a
        obtain ⟨x, hx⟩ := (U.map fun k => π k.factorial n (E k a)).eq_pure_of_finite
        refine ⟨x, ?_⟩
        have : {x} ∈ (U.map fun k => π k.factorial n (E k a)) := by rw [hx]; simp
        exact this
      choose f hf using this
      refine ⟨AddMonoidHom.mk' f fun a b => ?_, fun _ => hf⟩
      obtain ⟨k, hk1, hk2, hk3⟩ := ((hf a).and ((hf b).and (hf (a + b)))).exists
      rw [← hk1, ← hk2, ← hk3, map_add, map_add]
    · exact ⟨0, fun h => absurd h hn⟩
  choose ev hev using hlim
  have hpair : ∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) := by
    intro n hn a b
    obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev n hn b).and (hU n hn))).exists
    rw [← hk1, ← hk2]
    exact hpush n _ k.factorial_pos hk3 _ _ _ (hE k a b)
  have hks := fun n (hn : 0 < n) =>
    ker_and_surj hn (hζ n hn) (e n) (hG n hn).some (h1 n) (ev n) (hpair n hn)
  refine ⟨ev, fun n hn => (hks n hn).1, fun n hn => (hks n hn).2, ?_, hpair⟩
  intro n m hn hm a
  have hnm := Nat.mul_pos hn hm
  obtain ⟨k, hk1, hk2, hk3⟩ := ((hev n hn a).and ((hev _ hnm a).and (hU _ hnm))).exists
  rw [← hk1, ← hk2]
  exact hcomp _ _ _ hn k.factorial_pos (Dvd.intro _ rfl) hk3 _

end GlobalTheory.SympTower
