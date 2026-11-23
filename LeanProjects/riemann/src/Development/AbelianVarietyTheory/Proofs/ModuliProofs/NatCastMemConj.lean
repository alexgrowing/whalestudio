import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnimodDiv

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeCompare

theorem card_orth_mul {G k : Type} [CommGroup G] [Finite G] [Field k] [IsAlgClosed k] [CharZero k]
    (B : G →* G →* kˣ) (hB : Function.Injective B) (S : Subgroup G) :
    Nat.card {x : G // ∀ c ∈ S, B x c = 1} * Nat.card S = Nat.card G := by
  have : NeZero ((Monoid.exponent G : ℕ) : k) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero ((Monoid.exponent S : ℕ) : k) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have hc := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G k
  have : Finite (G →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hc]; exact Nat.card_pos.ne')
  have hb := hB.bijective_of_nat_card_le hc.le
  have hs : Function.Surjective ((MonoidHom.domRestrictHom S kˣ).comp B) :=
    (MonoidHom.domRestrict_surjective k S).comp hb.2
  rw [← ((MonoidHom.domRestrictHom S kˣ).comp B).ker.card_mul_index, Subgroup.index_ker,
    MonoidHom.range_eq_top.2 hs, Subgroup.card_top, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [MonoidHom.mem_ker, MonoidHom.ext_iff]
  exact ⟨fun h c => h c.1 c.2, fun h c hc => h ⟨c, hc⟩⟩

theorem card_eq_tors_mul {Q : Type} [CommGroup Q] (C : Subgroup Q) (p : ℕ) :
    Nat.card C = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card (C.map (powMonoidHom p)) := by
  rw [← ((powMonoidHom p).comp C.subtype).ker.card_mul_index, Subgroup.index_ker, MonoidHom.range_comp,
    Subgroup.range_subtype]
  congr 1
  exact Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem exists_split_one {O : Type} [CommRing O] [IsDedekindDomain O] {p : O} (hp : p ≠ 0) (P : Ideal O)
    [P.IsMaximal] : ∃ (n : ℕ) (π j : O), π ∈ P ∧ π + j = 1 ∧ ∀ a ∈ P ^ (n + 1), j * a ∈ Ideal.span {p} * P := by
  obtain ⟨J, hJ, e⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {p}) (by simpa using hp) P
  obtain ⟨π, hπ, j, hj, h⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hJ)
  generalize Multiset.count P _ = n at e
  refine ⟨n, π, j, hπ, h, fun a ha => ?_⟩
  rw [e, mul_right_comm, ← pow_succ, mul_comm j]
  exact Ideal.mul_mem_mul ha hj

theorem exists_split_two {O : Type} [CommRing O] [IsDedekindDomain O] {p : O} (hp : p ≠ 0) (P P' : Ideal O)
    [hP : P.IsMaximal] [hP' : P'.IsMaximal] (hco : P ⊔ P' = ⊤) : ∃ (m n : ℕ) (w u v a : O), w + v + u = 1 ∧
      a ∉ P ∧ a ∉ P' ∧ p ∣ w * a ∧ (∀ b ∈ P ^ m, p ∣ u * b) ∧ ∀ b ∈ P' ^ n, p ∣ v * b := by
  obtain ⟨J, hJ, e⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {p}) (by simpa using hp) P
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    simp [hp] at e
  obtain ⟨R, hR, e'⟩ := Ideal.eq_prime_pow_mul_coprime hJ0 P'
  obtain ⟨m, e⟩ : ∃ m, Ideal.span {p} = P ^ m * J := ⟨_, e⟩
  obtain ⟨n, e'⟩ : ∃ n, J = P' ^ n * R := ⟨_, e'⟩
  have h₁ : IsCoprime P R := (Ideal.isCoprime_iff_sup_eq.2 hJ).of_isCoprime_of_dvd_right ⟨P' ^ n, by rw [e', mul_comm]⟩
  have h₂ : IsCoprime P' R := Ideal.isCoprime_iff_sup_eq.2 hR
  have h₃ : IsCoprime (P ^ (m + 1) * P' ^ (n + 1)) R :=
    IsCoprime.mul_left (IsCoprime.pow_left h₁) (IsCoprime.pow_left h₂)
  have h₄ : IsCoprime (P ^ m) (P' ^ n) := (Ideal.isCoprime_iff_sup_eq.2 hco).pow
  obtain ⟨w, hw, a, ha, hwa⟩ := Ideal.isCoprime_iff_exists.1 h₃
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 h₄
  have key : ∀ x ∈ P ^ m, ∀ y ∈ P' ^ n, p ∣ x * (y * a) := fun x hx y hy => by
    rw [← Ideal.mem_span_singleton, e, e']
    exact Ideal.mul_mem_mul hx (Ideal.mul_mem_mul hy ha)
  have hn : ∀ I : Ideal O, I.IsMaximal → w ∈ I → a ∉ I := fun I hI h h' =>
    hI.ne_top ((Ideal.eq_top_iff_one _).2 (hwa ▸ I.add_mem h h'))
  refine ⟨m, n, w, a * t, a * s, a, by linear_combination hwa + a * hst,
    hn _ hP (Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.mul_le_inf hw).1),
    hn _ hP' (Ideal.pow_le_self (Nat.succ_ne_zero n) (Ideal.mul_le_inf hw).2), ?_, fun b hb => ?_, fun b hb => ?_⟩
  · rw [← Ideal.mem_span_singleton, e, e', ← mul_assoc]
    exact Ideal.mul_mem_mul (Ideal.mul_mono (Ideal.pow_le_pow_right (Nat.le_succ m))
      (Ideal.pow_le_pow_right (Nat.le_succ n)) hw) ha
  · rw [show a * t * b = b * (t * a) by ring]; exact key b hb t ht
  · rw [show a * s * b = s * (b * a) by ring]; exact key s hs b hb

def IsAct {O Q : Type} [CommRing O] [CommGroup Q] (ρ : O → Q →* Q) : Prop :=
  (∀ x, ρ 1 x = x) ∧ (∀ a b x, ρ (a * b) x = ρ b (ρ a x)) ∧ ∀ a b x, ρ (a + b) x = ρ a x * ρ b x

section Act

variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}

theorem IsAct.nat (h : IsAct ρ) (n : ℕ) (x : Q) : ρ n x = x ^ n := by
  induction n with
  | zero =>
    have := h.2.2 0 0 x
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, left_eq_mul.1 this]
  | succ n ih => rw [Nat.cast_succ, h.2.2, ih, h.1, pow_succ]

theorem IsAct.of_dvd (h : IsAct ρ) {n : ℕ} {x : Q} (hx : x ^ n = 1) {a : O} (ha : (n : O) ∣ a) : ρ a x = 1 := by
  obtain ⟨b, rfl⟩ := ha
  rw [h.2.1, h.nat, hx, map_one]

theorem IsAct.comm (h : IsAct ρ) (a b : O) (x : Q) : ρ a (ρ b x) = ρ b (ρ a x) := by
  rw [← h.2.1, ← h.2.1, mul_comm]

theorem IsAct.split (h : IsAct ρ) {a b : O} (hab : a + b = 1) (x : Q) : ρ a x * ρ b x = x := by
  rw [← h.2.2, hab, h.1]

theorem IsAct.pow_tors (h : IsAct ρ) {n : ℕ} {x : Q} (hx : x ^ n = 1) (a : O) : ρ a x ^ n = 1 := by
  rw [← map_pow, hx, map_one]

theorem IsAct.kill_mul_iff (h : IsAct ρ) (p : ℕ) (I : Ideal O) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)} * I, ρ a x = 1) ↔ ∀ a ∈ I, ρ a (x ^ p) = 1 := by
  constructor
  · intro H a ha
    rw [← h.nat, ← h.2.1]
    exact H _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ha)
  · intro H a ha
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 ha
    rw [h.2.1, h.nat, H b hb]

theorem IsAct.kill_span_iff (h : IsAct ρ) (p : ℕ) (x : Q) :
    (∀ a ∈ Ideal.span {(p : O)}, ρ a x = 1) ↔ x ^ p = 1 :=
  ⟨fun H => (h.nat p x).symm.trans (H _ (Ideal.mem_span_singleton_self _)),
    fun H _ ha => h.of_dvd H (Ideal.mem_span_singleton.1 ha)⟩

end Act

section Tate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)

def evH (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl

theorem ev_zero (n : ℕ) : I.ev n 0 = 1 := (evH I n).map_zero

theorem ev_nsmul (n m : ℕ) (a : D.La) : I.ev n (m • a) = I.ev n a ^ m := (evH I n).map_nsmul m a

theorem ev_sub (n : ℕ) (a b : D.La) : I.ev n (a - b) = I.ev n a / I.ev n b := (evH I n).map_sub a b

theorem ev_pow {n : ℕ} (hn : 0 < n) (a : D.La) : I.ev n a ^ n = 1 := (I.onto n hn _).2 ⟨a, rfl⟩

def Uniq (e : ℕ → Q → Q → kˣ → Prop) : Prop :=
  ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c'

variable (hu : Uniq e)
include hu

theorem triv_iff {n : ℕ} (hn : 0 < n) (a b : D.La) : e n (I.ev n a) (I.ev n b) 1 ↔ (n : ℤ) ∣ D.EF a b := by
  rw [← (I.ζ_prim n hn).zpow_eq_one_iff_dvd]
  exact ⟨fun h => hu n _ _ _ _ hn (ev_pow I hn a) (ev_pow I hn b) (I.isom n hn a b) h,
    fun h => h ▸ I.isom n hn a b⟩

include I

theorem triv_mul {n : ℕ} (hn : 0 < n) {x x' y : Q} (hx : x ^ n = 1) (hx' : x' ^ n = 1) (hy : y ^ n = 1)
    (h : e n x y 1) (h' : e n x' y 1) : e n (x * x') y 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  obtain ⟨a', rfl⟩ := (I.onto n hn _).1 hx'
  obtain ⟨b, rfl⟩ := (I.onto n hn _).1 hy
  rw [triv_iff I hu hn] at h h'
  rw [← I.add, triv_iff I hu hn, map_add, LinearMap.add_apply]
  exact dvd_add h h'

theorem triv_symm {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1)
    (h : e n x y 1) : e n y x 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  obtain ⟨b, rfl⟩ := (I.onto n hn _).1 hy
  rw [triv_iff I hu hn] at h ⊢
  rw [← LinearMap.IsAlt.neg (B := D.EF) D.alt]
  exact h.neg_right

theorem triv_adj {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) (c : 𝓞 E) :
    e n (ρ c x) y 1 ↔ e n x (ρ (H.bar c) y) 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  obtain ⟨b, rfl⟩ := (I.onto n hn _).1 hy
  rw [← I.lin n c a, ← I.lin n (H.bar c) b, triv_iff I hu hn, triv_iff I hu hn, D.adj]

theorem triv_one {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) : e n x 1 1 := by
  obtain ⟨a, rfl⟩ := (I.onto n hn _).1 hx
  have := (triv_iff I hu hn a 0).2 (by simp)
  rwa [ev_zero] at this

theorem triv_of_kill {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) {c : 𝓞 E}
    (h : ρ (H.bar c) y = 1) : e n (ρ c x) y 1 := by
  rw [triv_adj I hu hn hx hy, h]
  exact triv_one I hu hn hx

theorem triv_down {p : ℕ} (hp : 0 < p) {x y : Q} (hx : x ^ (p * p) = 1) (hy : y ^ p = 1) :
    e (p * p) x y 1 ↔ e p (x ^ p) y 1 := by
  have hq := Nat.mul_pos hp hp
  obtain ⟨a, rfl⟩ := (I.onto _ hq _).1 hx
  obtain ⟨b, rfl⟩ := (I.onto _ hp _).1 hy
  rw [I.tower p p hp hp, triv_iff I hu hp, ← I.tower p p hp hp b, ← ev_nsmul, triv_iff I hu hq, map_nsmul,
    nsmul_eq_mul, Nat.cast_mul, mul_dvd_mul_iff_left (Nat.cast_ne_zero.2 hp.ne')]

omit hu in
theorem exists_root {p : ℕ} (hp : 0 < p) {c : Q} (hc : c ^ p = 1) : ∃ y, y ^ p = c := by
  obtain ⟨b, rfl⟩ := (I.onto _ hp _).1 hc
  exact ⟨_, I.tower p p hp hp b⟩

theorem card_orth [IsAlgClosed k] [CharZero k] {p : ℕ} (hp : 0 < p) (hf : Finite {x : Q // x ^ p = 1})
    (S : Subgroup Q) (hS : ∀ c ∈ S, c ^ p = 1) :
    Nat.card {x : Q // x ^ p = 1 ∧ ∀ c ∈ S, e p x c 1} * Nat.card S = Nat.card {x : Q // x ^ p = 1} := by
  let G : Subgroup Q := (powMonoidHom p).ker
  have : Finite G := hf
  have hs : ∀ x : G, ∃ a, I.ev p a = x := fun x => (I.onto p hp _).1 x.2
  choose s hs using hs
  have hv : ∀ (x y : G) a b, I.ev p a = x → I.ev p b = y → I.ζ p ^ D.EF (s x) (s y) = I.ζ p ^ D.EF a b :=
    fun x y a b ha hb => hu p x y _ _ hp x.2 y.2 (by simpa only [hs] using I.isom p hp (s x) (s y))
      (by simpa only [ha, hb] using I.isom p hp a b)
  let B : G →* G →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (fun y => I.ζ p ^ D.EF (s x) (s y)) fun y y' => by
      rw [hv x (y * y') (s x) (s y + s y') (hs x) (by rw [I.add, hs, hs]; rfl), map_add, zpow_add])
    fun x x' => MonoidHom.ext fun y => by
      show I.ζ p ^ D.EF (s (x * x')) (s y) = I.ζ p ^ D.EF (s x) (s y) * I.ζ p ^ D.EF (s x') (s y)
      rw [hv (x * x') y (s x + s x') (s y) (by rw [I.add, hs, hs]; rfl) (hs y), map_add, LinearMap.add_apply, zpow_add]
  have hB1 : ∀ x y : G, B x y = 1 ↔ e p x y 1 := fun x y => by
    rw [← hs x, ← hs y, triv_iff I hu hp, ← (I.ζ_prim p hp).zpow_eq_one_iff_dvd]
    rfl
  have hB : Function.Injective B := (injective_iff_map_eq_one B).2 fun x hx => by
    have h₁ : ∀ b, (p : ℤ) ∣ D.EF (s x) b := fun b => by
      rw [← triv_iff I hu hp, hs]
      exact (hB1 x ⟨_, ev_pow I hp b⟩).1 (by rw [hx]; rfl)
    choose f hf using h₁
    have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    obtain ⟨a, ha⟩ := D.unimod.2 (AddMonoidHom.mk' f fun b b' => mul_left_cancel₀ hp' (by
      rw [mul_add, ← hf, ← hf, ← hf, map_add])).toIntLinearMap
    refine Subtype.ext ((hs x).symm.trans ((I.ker p hp _).2 ⟨a, D.unimod.1 (LinearMap.ext fun b => ?_)⟩))
    rw [map_nsmul, LinearMap.smul_apply, ha, hf, nsmul_eq_mul]
    rfl
  have h := card_orth_mul B hB (S.subgroupOf G)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show S ≤ G from hS)).toEquiv] at h
  refine Eq.trans (congrArg (· * _) (Nat.card_congr ?_)) h
  exact ⟨fun x => ⟨⟨x.1, x.2.1⟩, fun c hc => (hB1 _ _).2 (x.2.2 c.1 hc)⟩,
    fun x => ⟨x.1.1, x.1.2, fun c hc => (hB1 x.1 ⟨c, hS c hc⟩).1 (x.2 _ hc)⟩, fun _ => rfl, fun _ => rfl⟩

end Tate

section Kernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}

def kerSet (ρ : 𝓞 E → Q →* Q) (e : ℕ → Q → Q → kˣ → Prop) (p : ℕ) (P P' : Ideal (𝓞 E)) (C₀ : Subgroup Q) : Set Q :=
  {x | ∃ x₁ x₂ x₃ : Q, x = x₁ * x₂ * x₃ ∧ (x₁ ^ p = 1 ∧ ∃ a : 𝓞 E, a ∉ P ∧ a ∉ P' ∧ ρ a x₁ = 1) ∧
    ((∃ n : ℕ, ∀ a ∈ P' ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀) ∧
    (x₃ ^ p = 1 ∧ (∃ n : ℕ, ∀ a ∈ P ^ n, ρ a x₃ = 1) ∧ ∀ c ∈ C₀, e p x₃ c 1)}

theorem natCast_mem_conj {P : Ideal (𝓞 E)} {p : ℕ} (h : (p : 𝓞 E) ∈ P) :
    (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) h
  rwa [map_natCast] at this

theorem conj_isMaximal (H : Host E) (P : Ideal (𝓞 E)) [P.IsMaximal] : (P.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal :=
  Ideal.IsMaximal.map_bijective _ H.bar.bijective inferInstance

variable (I : TateIso D k Q (fun a x => ρ a x) e) (hu : Uniq e) (hρ : IsAct ρ) {P : Ideal (𝓞 E)} [hP : P.IsMaximal]
  (hco : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {p : ℕ} (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
include I hu hρ hco

omit hP in

theorem triv_of_primary {n : ℕ} (hn : 0 < n) {x y : Q} (hx : x ^ n = 1) (hy : y ^ n = 1) {r s : ℕ}
    (h : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ r, ρ a x = 1)
    (h' : ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ s, ρ a y = 1) : e n x y 1 := by
  have h₄ : IsCoprime (P ^ s) (P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ r) := (Ideal.isCoprime_iff_sup_eq.2 hco).pow
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h₄
  have := hρ.split hab x
  rw [h b hb, mul_one] at this
  rw [← this]
  refine triv_of_kill I hu hn hx hy (h' _ ?_)
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) ha

include hp hpP

variable {C₀ : Subgroup Q} (h₁ : ∀ a, ∀ x ∈ C₀, ρ a x ∈ C₀)
  (h₂ : ∀ x ∈ C₀, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
include h₂

omit I hu hco hP hp in
theorem datum_tors {c : Q} (hc : c ∈ C₀) : c ^ p = 1 := (hρ.nat p c).symm.trans (h₂ c hc _ (natCast_mem_conj hpP))

include h₁

theorem mem_kerSet_iff (x : Q) : x ∈ kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ↔
    ∃ x' x₂ : Q, x = x' * x₂ ∧ (x' ^ p = 1 ∧ ∀ c ∈ C₀, e p x' c 1) ∧
      (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀ := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  constructor
  · rintro ⟨x₁, x₂, x₃, rfl, ⟨t₁, a, ha, -, k₁⟩, k₂, t₃, -, k₃⟩
    refine ⟨x₁ * x₃, x₂, mul_right_comm _ _ _, ⟨by rw [mul_pow, t₁, t₃, mul_one], fun c hc => ?_⟩, k₂⟩
    refine triv_mul I hu hp t₁ t₃ (ht c hc) ?_ (k₃ c hc)
    obtain ⟨b, π, hπ, h⟩ := hP.exists_inv ha
    have := hρ.split h x₁
    rw [mul_comm b, hρ.2.1, k₁, map_one, one_mul] at this
    rw [← this]
    exact triv_of_kill I hu hp t₁ (ht c hc) (h₂ c hc _ (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hπ))
  · rintro ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩
    have := conj_isMaximal H P
    obtain ⟨m, n, w, u, v, a, h, ha, ha', hw, hu', hv⟩ :=
      exists_split_two (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0) P _ hco
    refine ⟨ρ w x', ρ v x' * x₂, ρ u x', ?_, ⟨hρ.pow_tors t w, a, ha, ha', ?_⟩, ⟨⟨n + r, fun b hb => ?_⟩, ?_⟩,
      hρ.pow_tors t u, ⟨m, fun b hb => ?_⟩, fun c hc => ?_⟩
    · rw [← mul_assoc, mul_right_comm, ← hρ.2.2, ← hρ.2.2, h, hρ.1]
    · rw [← hρ.2.1]; exact hρ.of_dvd t hw
    · rw [map_mul, ← hρ.2.1, hρ.of_dvd t (hv b (Ideal.pow_le_pow_right (Nat.le_add_right _ _) hb)),
        k₂ b (Ideal.pow_le_pow_right (Nat.le_add_left _ _) hb), mul_one]
    · rwa [mul_pow, hρ.pow_tors t v, one_mul]
    · rw [← hρ.2.1]; exact hρ.of_dvd t (hu' b hb)
    · rw [triv_adj I hu hp t (ht c hc)]
      exact o _ (h₁ _ c hc)

omit hco h₁ hP in
theorem ev_orth {a : D.La} (ha : a ∈ P • (⊤ : Submodule (𝓞 E) D.La)) : ∀ c ∈ C₀, e p (I.ev p a) c 1 := by
  intro c hc
  have ht := datum_tors hρ hpP h₂ hc
  refine Submodule.smul_induction_on ha (fun π hπ b _ => ?_) fun a b ha hb => ?_
  · rw [I.lin]
    exact triv_of_kill I hu hp (ev_pow I hp b) ht (h₂ c hc _ (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hπ))
  · rw [I.add]
    exact triv_mul I hu hp (ev_pow I hp a) (ev_pow I hp b) ht ha hb

theorem exists_subgroup [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) :
    ∃ C : Subgroup Q, (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ ∧
      (∀ x ∈ C, ∀ a, ρ a x ∈ C) ∧
      (∀ J : Ideal (𝓞 E), J * P = Ideal.span {(p : 𝓞 E)} → ∀ x, (∀ a ∈ J, ρ a x = 1) → x ∈ C) ∧
      (∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) ∧ Nat.card C = Nat.card {x : Q // x ^ p = 1} ∧
      Nat.card {x : Q // x ^ p = 1} = Nat.card {x : Q // x ∈ C ∧ x ^ p = 1} * Nat.card C₀ := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  have hq := Nat.mul_pos hp hp
  have h1 : ∀ y : Q, y ^ p = 1 → e p 1 y 1 := fun y hy =>
    triv_symm I hu hp hy (one_pow _) (triv_one I hu hp hy)
  let U : Subgroup Q := Subgroup.ofDiv {x | x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} ⟨1, one_pow _, fun c hc => h1 c (ht c hc)⟩
    fun x hx y hy => by
      have ti : y⁻¹ ^ p = 1 := by rw [inv_pow, hy.1, inv_one]
      refine ⟨by rw [mul_pow, hx.1, ti, mul_one], fun c hc => triv_mul I hu hp hx.1 ti (ht c hc) (hx.2 c hc) ?_⟩
      have e₁ : y⁻¹ = ρ (-1) y := by
        have := hρ.2.2 (-1) 1 y
        have h0 := hρ.nat 0 y
        rw [Nat.cast_zero, pow_zero] at h0
        rw [neg_add_cancel, h0, hρ.1] at this
        exact inv_eq_of_mul_eq_one_left this.symm
      rw [e₁, triv_adj I hu hp hy.1 (ht c hc)]
      exact hy.2 _ (h₁ _ c hc)
  let W : Subgroup Q := Subgroup.ofDiv
    {x | (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x = 1) ∧ x ^ p ∈ C₀}
    ⟨1, ⟨0, fun a _ => map_one _⟩, by rw [one_pow]; exact C₀.one_mem⟩ (by
      rintro x ⟨⟨n, hn⟩, hx⟩ y ⟨⟨m, hm⟩, hy⟩
      refine ⟨⟨n + m, fun a ha => ?_⟩, by rw [mul_pow, inv_pow]; exact C₀.mul_mem hx (C₀.inv_mem hy)⟩
      rw [map_mul, map_inv, hn a (Ideal.pow_le_pow_right (Nat.le_add_right _ _) ha),
        hm a (Ideal.pow_le_pow_right (Nat.le_add_left _ _) ha), inv_one, mul_one])
  have mem : ∀ x, x ∈ U ⊔ W ↔ ∃ x' x₂ : Q, x = x' * x₂ ∧ (x' ^ p = 1 ∧ ∀ c ∈ C₀, e p x' c 1) ∧
      (∃ n : ℕ, ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) ^ n, ρ a x₂ = 1) ∧ x₂ ^ p ∈ C₀ := fun x => by
    rw [Subgroup.mem_sup]
    exact ⟨fun ⟨a, ha, b, hb, h⟩ => ⟨a, b, h.symm, ha, hb⟩, fun ⟨a, b, h, ha, hb⟩ => ⟨a, ha, b, hb, h.symm⟩⟩
  have tors : ∀ x, (x ∈ U ⊔ W ∧ x ^ p = 1) ↔ (x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1) := fun x => by
    refine ⟨fun ⟨hx, t⟩ => ⟨t, fun c hc => ?_⟩, fun h => ⟨Subgroup.mem_sup_left h, h.1⟩⟩
    obtain ⟨x', x₂, rfl, ⟨t', o⟩, ⟨r, k₂⟩, -⟩ := (mem x).1 hx
    rw [mul_pow, t', one_mul] at t
    exact triv_mul I hu hp t' t (ht c hc) (o c hc)
      (triv_of_primary I hu hρ hco hp t (ht c hc) k₂ (s := 1) (by rw [pow_one]; exact h₂ c hc))
  have img : (U ⊔ W).map (powMonoidHom p) = C₀ := by
    refine le_antisymm ?_ fun c hc => ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', x₂, rfl, ⟨t', -⟩, -, k₂⟩ := (mem x).1 hx
      rwa [powMonoidHom_apply, mul_pow, t', one_mul]
    · have := conj_isMaximal H P
      obtain ⟨n, π, j, hπ, h, hj⟩ := exists_split_one (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0)
        (P.map (H.bar : 𝓞 E →+* 𝓞 E))
      obtain ⟨y, rfl⟩ := exists_root I hp (ht c hc)
      have e₁ : ρ j y ^ p = y ^ p := by
        have := hρ.split h (y ^ p)
        rwa [h₂ _ hc π hπ, one_mul, map_pow] at this
      refine ⟨ρ j y, Subgroup.mem_sup_right ⟨⟨n + 1, fun a ha => ?_⟩, e₁ ▸ hc⟩, e₁⟩
      rw [← hρ.2.1]
      exact (hρ.kill_mul_iff p _ y).2 (h₂ _ hc) _ (hj a ha)
  have hc := card_orth I hu hp hf C₀ ht
  rw [← Nat.card_congr (Equiv.subtypeEquivRight tors)] at hc
  refine ⟨U ⊔ W, Set.ext fun x => (mem x).trans (mem_kerSet_iff I hu hρ hco hp hpP h₁ h₂ x).symm, fun x hx a => ?_,
    fun J hJ x hx => ?_, fun x hx => (hρ.kill_mul_iff p _ x).2 (h₂ _ (img ▸ ⟨x, hx, rfl⟩)), fun x hx y hy => ?_,
    by rw [card_eq_tors_mul _ p, img, hc], hc.symm⟩
  · obtain ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩ := (mem x).1 hx
    refine (mem _).2 ⟨ρ a x', ρ a x₂, map_mul _ _ _, ⟨hρ.pow_tors t a, fun c hc => ?_⟩,
      ⟨r, fun b hb => by rw [hρ.comm, k₂ b hb, map_one]⟩, by rw [← map_pow]; exact h₁ _ _ k₂'⟩
    rw [triv_adj I hu hp t (ht c hc)]
    exact o _ (h₁ _ c hc)
  · have hpJ : (p : 𝓞 E) ∈ J * P := hJ ▸ Ideal.mem_span_singleton_self _
    have t : x ^ p = 1 := (hρ.nat p x).symm.trans (hx _ (Ideal.mul_le_inf hpJ).1)
    obtain ⟨a, rfl⟩ := (I.onto p hp _).1 t
    refine Subgroup.mem_sup_left ⟨t, ev_orth I hu hρ hp hpP h₂ ?_⟩
    have key : ∀ z ∈ J * P, ∃ b ∈ P • (⊤ : Submodule (𝓞 E) D.La), z • a = p • b := fun z hz => by
      refine Submodule.mul_induction_on hz (fun j hj π hπ => ?_) ?_
      · obtain ⟨b, hb⟩ := (I.ker p hp (j • a)).1 ((I.lin p j a).trans (hx j hj))
        exact ⟨π • b, Submodule.smul_mem_smul hπ trivial, by rw [mul_comm, mul_smul, hb, smul_comm]⟩
      · rintro z z' ⟨b, hb, e₁⟩ ⟨b', hb', e₂⟩
        exact ⟨b + b', add_mem hb hb', by rw [add_smul, e₁, e₂, smul_add]⟩
    obtain ⟨b, hb, e₁⟩ := key _ hpJ
    rw [Nat.cast_smul_eq_nsmul] at e₁
    have : a = b := D.unimod.1 (LinearMap.ext fun y => mul_left_cancel₀ (Nat.cast_ne_zero.2 hp.ne' : (p : ℤ) ≠ 0) (by
      have := congrArg (fun z => D.EF z y) e₁
      simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using this))
    exact this ▸ hb
  · obtain ⟨x', x₂, rfl, ⟨t, o⟩, ⟨r, k₂⟩, k₂'⟩ := (mem x).1 hx
    obtain ⟨y', y₂, rfl, ⟨t', o'⟩, ⟨r', l₂⟩, l₂'⟩ := (mem y).1 hy
    have a₁ : x' ^ (p * p) = 1 := by rw [pow_mul, t, one_pow]
    have a₂ : x₂ ^ (p * p) = 1 := by rw [pow_mul, ht _ k₂']
    have b₁ : y' ^ (p * p) = 1 := by rw [pow_mul, t', one_pow]
    have b₂ : y₂ ^ (p * p) = 1 := by rw [pow_mul, ht _ l₂']
    have b₃ : (y' * y₂) ^ (p * p) = 1 := by rw [mul_pow, b₁, b₂, mul_one]
    refine triv_mul I hu hq a₁ a₂ b₃ (triv_symm I hu hq b₃ a₁ ((triv_down I hu hp b₃ t).2 ?_))
      (triv_symm I hu hq b₃ a₂ (triv_mul I hu hq b₁ b₂ a₂ (triv_symm I hu hq a₂ b₁ ((triv_down I hu hp a₂ t').2 ?_))
        (triv_of_primary I hu hρ hco hq b₂ a₂ l₂ k₂)))
    · rw [mul_pow, t', one_mul]
      exact triv_symm I hu hp t (ht _ l₂') (o _ l₂')
    · exact triv_symm I hu hp t' (ht _ k₂') (o' _ k₂')

omit h₁ hco in

theorem card_datum_le [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) :
    Nat.card C₀ ≤ Ideal.absNorm P ^ (D.p + D.q) := by
  have ht : ∀ c ∈ C₀, c ^ p = 1 := fun c hc => datum_tors hρ hpP h₂ hc
  have hc := card_orth I hu hp hf C₀ ht
  have := D.fin
  have := D.proj
  have := hP.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact Nat.cast_ne_zero.2 hp.ne' (Ideal.mem_bot.1 hpP)
  have : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  obtain ⟨φ, φ', s, hs, hφ, -⟩ := HeckeTate.exists_local_iso (R := 𝓞 E) (M := D.La) (M' := Fin (D.p + D.q) → 𝓞 E)
    (by rw [D.rank, Module.finrank_fin_fun]) P
  have fU : Finite {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} :=
    Finite.of_injective (β := {x : Q // x ^ p = 1}) (fun x => ⟨x.1, x.2.1⟩) fun a b h =>
      Subtype.ext (congrArg (fun z : {x : Q // x ^ p = 1} => z.1) h)
  let F : {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} × (Fin (D.p + D.q) → 𝓞 E ⧸ P) → {x : Q // x ^ p = 1} :=
    fun z => ⟨z.1.1 * I.ev p (φ' fun i => (z.2 i).out), by rw [mul_pow, z.1.2.1, ev_pow I hp, mul_one]⟩
  have hF : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := (I.onto p hp _).1 hx
    obtain ⟨t, π, hπ, h⟩ := hP.exists_inv hs
    let y : Fin (D.p + D.q) → 𝓞 E := t • φ a
    let y' : Fin (D.p + D.q) → 𝓞 E := fun i => (Ideal.Quotient.mk P (y i)).out
    have hm : a - φ' y' ∈ P • (⊤ : Submodule (𝓞 E) D.La) := by
      have e₁ : a - φ' y' = π • a + φ' (y - y') := by
        rw [map_sub, map_smul, hφ, smul_smul, ← add_sub_assoc, ← add_smul, add_comm π, h, one_smul]
      rw [e₁]
      refine add_mem (Submodule.smul_mem_smul hπ trivial) ?_
      rw [pi_eq_sum_univ' (y - y'), map_sum]
      refine sum_mem fun i _ => ?_
      rw [map_smul]
      exact Submodule.smul_mem_smul (Ideal.Quotient.eq.1 (Quotient.out_eq _).symm) trivial
    refine ⟨(⟨I.ev p (a - φ' y'), ev_pow I hp _, ev_orth I hu hρ hp hpP h₂ hm⟩, fun i => Ideal.Quotient.mk P (y i)),
      Subtype.ext ?_⟩
    show I.ev p (a - φ' y') * I.ev p (φ' y') = _
    rw [← I.add, sub_add_cancel]
  have hle := Nat.card_le_card_of_surjective F hF
  rw [Nat.card_prod, Nat.card_fun, ← hc, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at hle
  have : Nonempty {x : Q // x ^ p = 1 ∧ ∀ c ∈ C₀, e p x c 1} := ⟨⟨1, one_pow _, fun c hc =>
    triv_symm I hu hp (ht c hc) (one_pow _) (triv_one I hu hp (ht c hc))⟩⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.le_of_mul_le_mul_left hle Nat.card_pos

omit h₁ h₂ in

theorem eq_kerSet [IsAlgClosed k] [CharZero k] (hf : Finite {x : Q // x ^ p = 1}) (C : Subgroup Q)
    (c₁ : ∀ x ∈ C, ∀ a, ρ a x ∈ C)
    (c₃ : ∀ x ∈ C, ∀ a ∈ Ideal.span {(p : 𝓞 E)} * P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1)
    (c₄ : ∀ x ∈ C, ∀ y ∈ C, e (p * p) x y 1) (c₅ : Nat.card C = Nat.card {x : Q // x ^ p = 1}) :
    (∀ a, ∀ x ∈ C.map (powMonoidHom p), ρ a x ∈ C.map (powMonoidHom p)) ∧
    (∀ x ∈ C.map (powMonoidHom p), ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1) ∧
    (C : Set Q) = kerSet ρ e p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) (C.map (powMonoidHom p)) := by
  have h₁ : ∀ a, ∀ x ∈ C.map (powMonoidHom p), ρ a x ∈ C.map (powMonoidHom p) := by
    rintro a _ ⟨x, hx, rfl⟩
    exact ⟨ρ a x, c₁ x hx a, (map_pow _ _ _).symm⟩
  have h₂ : ∀ x ∈ C.map (powMonoidHom p), ∀ a ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E), ρ a x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hρ.kill_mul_iff p _ x).1 (c₃ x hx)
  refine ⟨h₁, h₂, ?_⟩
  obtain ⟨C', e₁, -, -, -, -, e₂, -⟩ := exists_subgroup I hu hρ hco hp hpP h₁ h₂ hf
  have : Nonempty {x : Q // x ^ p = 1} := ⟨⟨1, one_pow _⟩⟩
  have : Finite C' := Nat.finite_of_card_ne_zero (by rw [e₂]; exact Nat.card_pos.ne')
  rw [← e₁]
  refine congrArg _ (Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [e₂, c₅]))
  have := conj_isMaximal H P
  obtain ⟨n, π, j, hπ, h, hj⟩ := exists_split_one (Nat.cast_ne_zero.2 hp.ne' : (p : 𝓞 E) ≠ 0)
    (P.map (H.bar : 𝓞 E →+* 𝓞 E))
  have t : ρ π x ^ p = 1 := by rw [← map_pow]; exact h₂ _ ⟨x, hx, rfl⟩ π hπ
  refine e₁.ge ((mem_kerSet_iff I hu hρ hco hp hpP h₁ h₂ x).2 ⟨ρ π x, ρ j x, (hρ.split h x).symm, ⟨t, ?_⟩,
    ⟨n + 1, fun a ha => ?_⟩, ⟨_, c₁ x hx j, rfl⟩⟩)
  · rintro _ ⟨y, hy, rfl⟩
    have ty : (y ^ p) ^ p = 1 := datum_tors hρ hpP h₂ ⟨y, hy, rfl⟩
    exact triv_symm I hu hp ty t ((triv_down I hu hp (by rw [pow_mul, ty]) t).1 (c₄ y hy _ (c₁ x hx π)))
  · rw [← hρ.2.1]
    exact c₃ x hx _ (hj a ha)

end Kernel

end GlobalTheory.HeckeCompare
