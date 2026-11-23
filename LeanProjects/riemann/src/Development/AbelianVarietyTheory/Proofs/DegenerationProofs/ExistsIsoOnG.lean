import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.Ex.RecPeriods

section Transport
variable {O : Type} [CommRing O] {B B' : NumB O} (I : NumB.Iso B B')

theorem cubN_iso (k : ℕ) (y x : B.A) :
    cubN B'.θ k 1 (I.φ y) (I.φ x) * I.h (y ^ k) * I.h x * I.h (y * x) ^ k =
      cubN B.θ k 1 y x * I.h (y ^ k * x) * I.h y ^ k * I.h x ^ k := by
  induction k with
  | zero => simp [cubN, I.h_one]
  | succ k ih =>
    have a := I.θ_eq (y ^ k) y x
    simp only [cubN, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [map_pow] at a
    rw [pow_succ y]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow] at a ih ⊢
    linear_combination (norm := module) a + ih

theorem dbl_iso (x : B.A) : dbl B'.θ B'.σ (I.φ x) * I.h (x * x) = dbl B.θ B.σ x * I.h x ^ 4 := by
  have a := I.θ_eq x x⁻¹ x
  have b := I.σ_eq x
  rw [mul_inv_cancel, inv_mul_cancel, one_mul, I.h_one, map_inv] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at a b ⊢
  linear_combination (norm := module) a - b

theorem mulq_iso (k : ℕ) (x : B.A) :
    mulq B'.θ B'.σ k (I.φ x) * I.h x ^ (k ^ 2) = mulq B.θ B.σ k x * I.h (x ^ k) := by
  induction k with
  | zero => simp [mulq, I.h_one]
  | succ k ih =>
    have a := cubN_iso I k x x
    have b := dbl_iso I x
    simp only [mulq, Finset.prod_range_succ] at ih ⊢
    rw [pow_succ x, show (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 by ring]
    replace a := congrArg Additive.ofMul a
    replace b := congrArg (fun u => k • Additive.ofMul u) b
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at a b ih ⊢
    linear_combination (norm := module) a - b + ih

theorem wS_iso (k : ℕ) (hk : Odd k) (x : B.A) (hx : x ^ k = 1) :
    B'.wS k (I.φ x) 1 1 * I.h x ^ k = B.wS k x 1 1 := by
  obtain ⟨r, rfl⟩ := hk
  have a := cubN_iso I (2 * r + 1) x x
  have b := dbl_iso I x
  have c := mulq_iso I (2 * r + 1) x
  rw [hx, I.h_one] at a c
  rw [one_mul] at a
  have e : (2 * r + 1 - 1) / 2 = r := by omega
  simp only [NumB.wS, e, one_mul]
  replace a := congrArg (fun u => r • Additive.ofMul u) a
  replace b := congrArg (fun u => (r * (2 * r + 1)) • Additive.ofMul u) b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at a b c ⊢
  linear_combination (norm := module) c - a + b

theorem uth_iso (m : ℕ) (hm : Odd m) (b x : B.A) (hb : b ^ m ^ 2 = 1) :
    B'.uth m (I.φ b) (I.φ x) = (I.lam * I.h x ^ m ^ 2 : Oˣ) * B.uth m b x := by
  have a := cubN_iso I (m ^ 2) b x
  have w := wS_iso I (m ^ 2) hm.pow b hb
  have c := mulq_iso I m (x * b)
  rw [hb, I.h_one, one_mul, mul_comm b x] at a
  have key : B'.uV (m ^ 2) 1 (I.φ b) (I.φ x) * B'.wS (m ^ 2) (I.φ b) 1 1 * (I.lam * I.h ((x * b) ^ m)) *
      (mulq B'.θ B'.σ m (I.φ (x * b)))⁻¹ =
      I.lam * I.h x ^ m ^ 2 * (B.uV (m ^ 2) 1 b x * B.wS (m ^ 2) b 1 1) * (mulq B.θ B.σ m (x * b))⁻¹ := by
    simp only [NumB.uV, B.cub.face, B'.cub.face, div_one]
    replace a := congrArg Additive.ofMul a
    replace w := congrArg Additive.ofMul w
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a w c ⊢
    linear_combination (norm := module) a + w - c
  replace key := congrArg Units.val key
  simp only [NumB.uth, NumB.mth, ← map_mul, ← map_pow, I.th_eq]
  simp only [Units.val_mul] at key ⊢
  linear_combination B.th ((x * b) ^ m) * key
end Transport

theorem cubN_mul_exp {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ) (a b : ℕ) (y x : A) :
    cubN θ (b * a) 1 y x = cubN θ a 1 (y ^ b) x * cubN θ b 1 y x ^ a := by
  induction a with
  | zero => simp [cubN]
  | succ a ih =>
    have s := h.N_split b (y ^ (b * a)) y x
    have e : cubN θ (b * (a + 1)) 1 y x = cubN θ (b * a) 1 y x * cubN θ b (y ^ (b * a)) y x := by
      simp only [cubN, mul_add, mul_one, Finset.prod_range_add, one_mul, pow_add]
    have f : cubN θ (a + 1) 1 (y ^ b) x = cubN θ a 1 (y ^ b) x * θ (y ^ (b * a)) (y ^ b) x := by
      simp only [cubN, Finset.prod_range_succ, one_mul, pow_mul]
    rw [e, f, ih, s, pow_succ]
    ac_rfl

theorem txT_eq {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1)
    (q p₁ : N.QT m) (hq : q.1.1 = 1) (hq' : q.1.2 = p.1.2 ^ m) :
    N.txT m p p₁.1.1.toAdd =
      (N.ψ p₁.1.1.toAdd * N.wp q p₁ * mulq N.θ N.σ m p₁.1.2.b : Oˣ) * N.uth m p.1.2.b p₁.1.2.b := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m m p₁.1.2.b p.1.2.b).2.1
  have c := cubN_mul_exp N.cub m m p.1.2.b p₁.1.2.b
  rw [← sq] at c
  have key : N.wQ p / mulq N.θ N.σ m p.1.2.b * (N.ψ p₁.1.1.toAdd * (p.1.2 ^ m).s p₁.1.1.toAdd) =
      N.ψ p₁.1.1.toAdd * N.wp q p₁ * mulq N.θ N.σ m p₁.1.2.b *
        (N.uV (m ^ 2) 1 p.1.2.b p₁.1.2.b * N.wS (m ^ 2) p.1.2.b 1 1) *
        (mulq N.θ N.σ m (p₁.1.2.b * p.1.2.b))⁻¹ := by
    simp only [NumB.uV, N.cub.face, div_one, NumD.wQ, NumD.wp, NumD.tk, hp, hq, hq', toAdd_one, NumD.ψ_zero,
      NumD.Gt.s_zero, NumD.Gt.pow_b, a, c]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div, ofMul_one]
    module
  replace key := congrArg Units.val key
  simp only [NumD.txT, NumD.vt, NumB.uth, NumB.mth, mul_pow, N.QT_pow_b p₁, NumD.Gt.pow_b]
  simp only [Units.val_mul] at key ⊢
  linear_combination N.th (N.c p₁.1.1.toAdd * p.1.2.b ^ m) * key

theorem exists_torus_root {C : Type} [Field C] [IsAlgClosed C] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (k : ℕ) (hk : k ≠ 0) (t : Multiplicative X →* Cˣ) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hs : Function.Surjective ((k : ℤ) • (LinearMap.id : Additive Cˣ →ₗ[ℤ] Additive Cˣ)) := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul u : Cˣ) : C) (Nat.pos_of_ne_zero hk)
    have z0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk] at hz
      exact (Additive.toMul u).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z z0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    simpa using hz
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ (MonoidHom.toAdditiveRight t).toIntLinearMap hs
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  have := congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)
  simpa using this

theorem exists_lift {C : Type} [Field C] [IsAlgClosed C] (N : NumD C) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b)
    (k : ℕ) (hk : k ≠ 0) (b : N.A) (hb : b ^ k = 1) : ∃ p : N.QT k, p.1.1 = 1 ∧ p.1.2.b = b := by
  obtain ⟨γ, rfl⟩ := hN b
  obtain ⟨t, ht⟩ := (N.exists_tor_iff (γ ^ k)).2 (by rw [NumD.Gt.pow_b, hb])
  obtain ⟨t', rfl⟩ := exists_torus_root k hk t
  refine ⟨⟨(1, γ * (N.tor t')⁻¹), ?_⟩, rfl, by simp⟩
  rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, ht, mul_inv_cancel]
  exact N.io_zero.symm

def powRep {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : N.QT m :=
  ⟨(1, p.1.2 ^ m), by rw [NumD.mem_QT, ← pow_mul, ← sq, N.mem_QT.1 p.2, hp]⟩

section Match
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

theorem exists_partner {e : N.X ≃+ N'.X} (hB : μ.B e) (j k : ℕ) (hk : k = n ^ j) (p : N.QT k) :
    ∃ p', μ.r k p p' ∧ p'.1.1.toAdd = e p.1.1.toAdd := by
  subst hk
  obtain ⟨p', h⟩ := μ.tot j p
  obtain ⟨z, hz⟩ := hB j p p' h
  refine ⟨p' * N'.qTriv _ (-z), (μ.eqv _ p p p' _ h ((N.qEq_equivalence _).refl p)).2
    ((N'.qEq_iff _ _).2 ⟨-z, rfl⟩), ?_⟩
  change p'.1.1.toAdd + n ^ j • (-z) = _
  rw [hz, smul_neg, add_neg_cancel_right]

theorem r_pow {k : ℕ} {p : N.QT k} {p' : N'.QT k} (h : μ.r k p p') (a : ℕ) (ha : a ≠ 0) : μ.r k (p ^ a) (p' ^ a) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
  induction a with
  | zero => simpa using h
  | succ a ih => rw [Nat.succ_eq_add_one, pow_succ, pow_succ p']; exact μ.mul _ _ _ _ _ (ih (Nat.succ_ne_zero _)) h

theorem r_powRep {m : ℕ} (hm : m ≠ 0) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r (m ^ 2) p p')
    (hp : p.1.1 = 1) (hp' : p'.1.1 = 1) : μ.r m (powRep N m p hp) (powRep N' m p' hp') := by
  have key : ∀ K, K = m * m → ∀ (a : N.QT m) (a' : N'.QT m) (q : N.QT K) (q' : N'.QT K), q.1.1 = a.1.1 ^ m →
      q.1.2 = a.1.2 → q'.1.1 = a'.1.1 ^ m → q'.1.2 = a'.1.2 → μ.r K q q' → μ.r m a a' := by
    rintro K rfl a a' q q' h₁ h₂ h₃ h₄ h
    exact (μ.incl m m a a' q q' hm h₁ h₂ h₃ h₄).2 h
  refine key _ (sq m) _ _ _ _ ?_ rfl ?_ rfl (r_pow μ h m hm)
  · change p.1.1 ^ m = 1 ^ m
    rw [hp]
  · change p'.1.1 ^ m = 1 ^ m
    rw [hp']

theorem uth_prop [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {e : N.X ≃+ N'.X} (hB : μ.B e)
    (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I) (j : ℕ) (p₁ : N.QT (n ^ j)) (p₁' : N'.QT (n ^ j))
    (h₁ : μ.r _ p₁ p₁') (he : p₁'.1.1.toAdd = e p₁.1.1.toAdd) (b : N.A) (hb : b ^ (n ^ j) ^ 2 = 1) :
    (N'.ψ (e p₁.1.1.toAdd) * mulq N'.θ N'.σ (n ^ j) p₁'.1.2.b * (I.lam * I.h p₁.1.2.b ^ (n ^ j) ^ 2) : Cˣ) *
      N'.uth (n ^ j) (I.φ b) p₁'.1.2.b =
    μ.c₀ * (N.ψ p₁.1.1.toAdd * mulq N.θ N.σ (n ^ j) p₁.1.2.b : Cˣ) * N'.uth (n ^ j) (I.φ b) (I.φ p₁.1.2.b) := by
  have hm : n ^ j ≠ 0 := hn.pow.pos.ne'
  obtain ⟨p, hp, rfl⟩ := exists_lift N hN _ (pow_ne_zero 2 hm) b hb
  obtain ⟨p', h, hp'⟩ := exists_partner μ hB (j * 2) _ (pow_mul n j 2).symm p
  replace hp' : p'.1.1 = 1 := by
    rw [hp, toAdd_one, map_zero] at hp'
    exact hp'
  have hb' : p'.1.2.b = I.φ p.1.2.b := by
    have key : ∀ K, K = n ^ (j * 2) → ∀ (q : N.QT K) (q' : N'.QT K), μ.r K q q' → q.1.1 = 1 → q'.1.1 = 1 →
        q'.1.2.b = I.φ q.1.2.b := by
      rintro K rfl
      exact hI _
    exact key _ (pow_mul n j 2).symm p p' h hp hp'
  have t := hT j p p' h hp hp' p₁.1.1.toAdd
  have w := μ.wp _ _ _ _ _ (r_powRep μ hm h hp hp') h₁
  rw [← he, txT_eq N' _ p' hp' (powRep N' _ p' hp') p₁' rfl rfl, txT_eq N _ p hp (powRep N _ p hp) p₁ rfl rfl, w,
    he, hb'] at t
  rw [uth_iso I _ hn.pow _ _ hb]
  refine mul_left_cancel₀ (N.wp (powRep N _ p hp) p₁).ne_zero ?_
  simp only [Units.val_mul] at t ⊢
  linear_combination ((I.lam : C) * ((I.h p₁.1.2.b ^ (n ^ j) ^ 2 : Cˣ) : C)) * t

theorem root_eq [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {g' : ℕ} (ht : N'.Tors n g')
    {e : N.X ≃+ N'.X} (hB : μ.B e) (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I) (j : ℕ) (hj : 1 ≤ j)
    (p₁ : N.QT (n ^ j)) (p₁' : N'.QT (n ^ j)) (h₁ : μ.r _ p₁ p₁') (he : p₁'.1.1.toAdd = e p₁.1.1.toAdd) :
    p₁'.1.2.b = I.φ p₁.1.2.b := by
  refine ht.sep j hj _ _ (μ.c₀ * (N.ψ p₁.1.1.toAdd * mulq N.θ N.σ (n ^ j) p₁.1.2.b : Cˣ) /
    (N'.ψ (e p₁.1.1.toAdd) * mulq N'.θ N'.σ (n ^ j) p₁'.1.2.b * (I.lam * I.h p₁.1.2.b ^ (n ^ j) ^ 2) : Cˣ))
    (div_ne_zero (mul_ne_zero μ.c₀_ne (Units.ne_zero _)) (Units.ne_zero _)) fun b' hb' => ?_
  obtain ⟨b, rfl⟩ := I.φ.surjective b'
  rw [← map_pow, map_eq_one_iff _ I.φ.injective] at hb'
  rw [div_mul_eq_mul_div, eq_div_iff (Units.ne_zero _), ← uth_prop μ hn hN hB hT hI j p₁ p₁' h₁ he b hb', mul_comm]

theorem c_psi [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {g' : ℕ} (ht : N'.Tors n g')
    {e : N.X ≃+ N'.X} (hB : μ.B e) (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I)
    (p₁ : N.QT (n ^ 1)) : N'.c (e p₁.1.1.toAdd) = I.φ (N.c p₁.1.1.toAdd) ∧
      (I.lam * (N'.ψ (e p₁.1.1.toAdd) * I.h (N.c p₁.1.1.toAdd)) : Cˣ) = μ.c₀ * N.ψ p₁.1.1.toAdd := by
  obtain ⟨p₁', h₁, he⟩ := exists_partner μ hB 1 _ rfl p₁
  have hr := root_eq μ hn hN ht hB hT hI 1 le_rfl p₁ p₁' h₁ he
  have hc : N'.c (e p₁.1.1.toAdd) = I.φ (N.c p₁.1.1.toAdd) := by
    rw [← he, ← N'.QT_pow_b, ← N.QT_pow_b, hr, map_pow]
  refine ⟨hc, ?_⟩
  obtain ⟨t, ht₁, ht₂⟩ := ht.good (I.φ (N.c p₁.1.1.toAdd))
  obtain ⟨b', rfl⟩ := ht.div t
  obtain ⟨b, rfl⟩ := I.φ.surjective b'
  have hb : b ^ (n ^ 1) ^ 2 = 1 := by
    apply I.φ.injective
    rw [map_pow, map_one, pow_one, sq, pow_mul, ht₁]
  have u := uth_prop μ hn hN hB hT hI 1 p₁ p₁' h₁ he b hb
  have u0 : N'.uth (n ^ 1) (I.φ b) (I.φ p₁.1.2.b) ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) (mul_ne_zero ?_ (Units.ne_zero _))
    rw [mul_pow, ← map_pow, N.QT_pow_b, show I.φ b ^ n ^ 1 = I.φ b ^ n by rw [pow_one],
      ← norm_ne_zero_iff, ht₂]
    exact one_ne_zero
  rw [hr] at u
  replace u := mul_right_cancel₀ u0 u
  have q := congrArg Units.val (mulq_iso I (n ^ 1) p₁.1.2.b)
  rw [N.QT_pow_b] at q
  refine mul_left_cancel₀ (mulq N.θ N.σ (n ^ 1) p₁.1.2.b).ne_zero ?_
  simp only [Units.val_mul] at u q ⊢
  linear_combination u - (I.lam : C) * (N'.ψ (e p₁.1.1.toAdd) : C) * q
end Match

theorem exists_iso_onG : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ e, μ.B e → μ.Term e → ∀ I : NumB.Iso N.toNumB N'.toNumB, μ.OnB I → ∃ J : NumD.Iso N N', J.toIso = I ∧ J.e = e ∧ μ.OnG J := by
  intro C _ _ _ _ N N' q q' n g g' _ hn _ _ _ ht ht' μ _ e hB hT I hI
  have hN := QStr.exists_lift N
  have hQ : ∀ (j : ℕ) (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y := fun j y => by
    have hd : ∀ (i : ℕ) (x : N.A), ∃ b, b ^ n ^ i = x := fun i => by
      induction i with
      | zero => exact fun x => ⟨x, pow_one x⟩
      | succ i ih =>
        intro x
        obtain ⟨a, rfl⟩ := ih x
        obtain ⟨b, rfl⟩ := ht.div a
        exact ⟨b, by rw [pow_succ', pow_mul]⟩
    obtain ⟨b, hb⟩ := hd j (N.io y).b
    obtain ⟨γ, -, hγ⟩ := QStr.root_over N hn.pow.pos.ne' (N.io y) b hb
    exact ⟨⟨(Multiplicative.ofAdd y, γ), hγ⟩, rfl⟩
  have main : ∀ χ, N'.c (e χ) = I.φ (N.c χ) ∧ (I.lam * (N'.ψ (e χ) * I.h (N.c χ)) : Cˣ) = μ.c₀ * N.ψ χ := fun χ => by
    obtain ⟨p₁, rfl⟩ := hQ 1 χ
    exact c_psi μ hn hN ht' hB hT hI p₁
  have hl : (I.lam : C) = μ.c₀ := by simpa [I.h_one] using (main 0).2
  refine ⟨⟨I, e, fun χ => (main χ).1, fun χ => ?_⟩, rfl, rfl, fun j p p' h hp hp' => ?_⟩
  · have := (main χ).2
    rw [← hl, ← Units.val_mul, Units.val_inj] at this
    exact mul_left_cancel this
  · have hb := hI j p p' h hp hp'
    have h1 : p.1.2 ^ n ^ j = 1 := by rw [N.mem_QT.1 p.2, hp]; exact N.io_zero
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have h1' : p'.1.2 ^ n ^ 0 = 1 := by rw [N'.mem_QT.1 p'.2, hp']; exact N'.io_zero
      rw [(pow_one p.1.2).symm.trans h1, (pow_one p'.1.2).symm.trans h1']
      exact NumD.Iso.rel_one _
    refine ⟨hb, fun χ => ?_⟩
    obtain ⟨p₁, rfl⟩ := hQ j χ
    obtain ⟨p₁', h₁, he⟩ := exists_partner μ hB j _ rfl p₁
    have hr := root_eq μ hn hN ht' hB hT hI j hj p₁ p₁' h₁ he
    have w := μ.wp _ _ _ _ _ h h₁
    have a := cubN_iso I (n ^ j) p₁.1.2.b p.1.2.b
    have b := cubN_iso I (n ^ j) p.1.2.b p₁.1.2.b
    rw [N.QT_pow_b] at a
    rw [← NumD.Gt.pow_b, h1, NumD.Gt.one_b, I.h_one, one_mul, mul_comm p.1.2.b] at b
    simp only [NumD.wp, NumD.tk, hp, hp', he, hr, hb, toAdd_one, NumD.Gt.s_zero] at w
    change p'.1.2.s (e p₁.1.1.toAdd) * I.h (N.c p₁.1.1.toAdd * p.1.2.b) =
      p.1.2.s p₁.1.1.toAdd * I.h (N.c p₁.1.1.toAdd) * I.h p.1.2.b
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    replace w := congrArg Additive.ofMul w
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at a b w ⊢
    linear_combination (norm := module) w - a + b

end GlobalTheory.Ex.RecPeriods
end
