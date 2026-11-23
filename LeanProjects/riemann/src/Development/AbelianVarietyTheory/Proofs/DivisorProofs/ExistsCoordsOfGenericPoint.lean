import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.TateGlue

theorem bezout {N P : ℕ} (h : N.Coprime P) : (N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]; rfl

theorem eq_of_pow_eq {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G}
    (h1 : a ^ N = b ^ N) (h2 : a ^ P = b ^ P) : a = b := by
  have key : ∀ g : G, g = (g ^ N) ^ N.gcdA P * (g ^ P) ^ N.gcdB P := fun g => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [key a, key b, h1, h2, ← h1, ← h2]

def glue {G : Type} [CommGroup G] (N P : ℕ) (a b : G) : G := a ^ N.gcdA P * b ^ N.gcdB P

theorem zpow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a : G} (ha : a ^ P = 1) :
    a ^ ((N : ℤ) * N.gcdA P) = a := by
  have : a ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = a := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul a (P : ℤ), zpow_natCast, ha, one_zpow, _root_.mul_one] at this

theorem zpow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {b : G} (hb : b ^ N = 1) :
    b ^ ((P : ℤ) * N.gcdB P) = b := by
  have : b ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = b := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul b (N : ℤ), zpow_natCast, hb, one_zpow, _root_.one_mul] at this

theorem zpow_pow_comm {G : Type} [CommGroup G] (a : G) (z : ℤ) (n : ℕ) : (a ^ z) ^ n = (a ^ n) ^ z := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem glue_pow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ N = a := by
  rw [glue, mul_pow, zpow_pow_comm b, hb, one_zpow, _root_.mul_one, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_left h ha]

theorem glue_pow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ P = b := by
  rw [glue, mul_pow, zpow_pow_comm a, ha, one_zpow, _root_.one_mul, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_right h hb]

theorem glue_mul {G : Type} [CommGroup G] (N P : ℕ) (a b a' b' : G) :
    glue N P (a * a') (b * b') = glue N P a b * glue N P a' b' := by
  simp only [glue, mul_zpow]; exact mul_mul_mul_comm _ _ _ _

theorem map_glue {G : Type} [CommGroup G] (N P : ℕ) (f : G → G) (hf : ∀ a b, f (a * b) = f a * f b) (a b : G) :
    f (glue N P a b) = glue N P (f a) (f b) := by
  let φ : G →* G := MonoidHom.mk' f hf
  change φ (glue N P a b) = glue N P (φ a) (φ b)
  simp only [glue, map_mul, map_zpow]

theorem hom_zsmul {A G : Type} [AddCommGroup A] [CommGroup G] (f : A → G) (hf : ∀ x y, f (x + y) = f x * f y)
    (z : ℤ) (x : A) : f (z • x) = f x ^ z := by
  let φ : Multiplicative A →* G := MonoidHom.mk' (fun x => f x.toAdd) (fun a b => hf _ _)
  change φ (Multiplicative.ofAdd (z • x)) = φ (Multiplicative.ofAdd x) ^ z
  rw [ofAdd_zsmul, map_zpow]

theorem tower_add {G : Type} [CommGroup G] (p : ℕ) (f : ℕ → G) (hf : ∀ r, f (r + 1) ^ p = f r) (r s : ℕ) :
    f (r + s) ^ (p ^ s) = f r := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', pow_mul, ← add_assoc, hf, ih]

def sys {G : Type} [CommGroup G] (p : ℕ) (f g : ℕ → G) (n : ℕ) : G :=
  glue (n / p ^ n.factorization p) (p ^ n.factorization p) (f (n.factorization p)) (g (n / p ^ n.factorization p))

theorem cop {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (n / p ^ n.factorization p).Coprime (p ^ n.factorization p) :=
  ((Nat.coprime_ordCompl hp hn.ne').pow_left _).symm

theorem sys_left {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (n / p ^ n.factorization p) = f (n.factorization p) :=
  glue_pow_left (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_right {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (p ^ n.factorization p) = g (n / p ^ n.factorization p) :=
  glue_pow_right (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_pow_self {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) : sys p f g n ^ n = 1 := by
  have h := congrArg (· ^ (p ^ n.factorization p)) (sys_left hp hf hg hn)
  rwa [hf, ← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h

theorem sys_tower {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) (hf' : ∀ r, f (r + 1) ^ p = f r)
    (hg' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → g (n * m) ^ m = g n) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hl := sys_left hp hf hg hnm
  have hr := sys_right hp hf hg hnm
  have hfac : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have hc := Nat.ordCompl_mul n m p
  have hcp := (Nat.coprime_ordCompl hp hnm.ne').symm
  rw [hc] at hl hr hcp
  rw [hfac] at hl hr
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m p
  have hnp := Nat.ordCompl_pos p hn.ne'
  have hmp := Nat.ordCompl_pos p hm.ne'
  refine eq_of_pow_eq (cop hp hn) ?_ ?_
  · rw [sys_left hp hf hg hn, ← tower_add p f hf' _ (m.factorization p), ← hl, ← pow_mul, ← pow_mul]
    congr 1
    generalize n / p ^ n.factorization p = a at *
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring
  · rw [sys_right hp hf hg hn, ← hg' _ _ hnp hmp hcp, ← hr, ← pow_mul, ← pow_mul, pow_add]
    congr 1
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring

theorem exists_gTateIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  intro p hpF D k _ Q _ act E hact hex huniq hlev I ζ ev hζ hζ' hev hev' hE
  have hp : p.Prime := hpF.out
  have ζ1 : ∀ r, ζ r ^ (p ^ r) = 1 := fun r => (hζ r).pow_eq_one
  have ζ2 : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n hn hc => (I.ζ_prim n hn hc).pow_eq_one
  have e1 : ∀ (y : D.La) r, ev r y ^ (p ^ r) = 1 := fun y r => ((hev r).2.2.2 _).2 ⟨y, rfl⟩
  have e2 : ∀ (y : D.La) n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n hn hc =>
    (I.onto n hn hc _).2 ⟨y, rfl⟩
  let Z : ℕ → kˣ := sys p ζ I.ζ
  let V : ℕ → D.La → Q := fun n y => sys p (fun r => ev r y) (fun n => I.ev n y) n
  have Zl : ∀ n, 0 < n → Z n ^ (n / p ^ n.factorization p) = ζ (n.factorization p) := fun n hn =>
    sys_left hp ζ1 ζ2 hn
  have Zr : ∀ n, 0 < n → Z n ^ (p ^ n.factorization p) = I.ζ (n / p ^ n.factorization p) := fun n hn =>
    sys_right hp ζ1 ζ2 hn
  have Vl : ∀ n, 0 < n → ∀ y, V n y ^ (n / p ^ n.factorization p) = ev (n.factorization p) y := fun n hn y =>
    sys_left hp (e1 y) (e2 y) hn
  have Vr : ∀ n, 0 < n → ∀ y, V n y ^ (p ^ n.factorization p) = I.ev (n / p ^ n.factorization p) y :=
    fun n hn y => sys_right hp (e1 y) (e2 y) hn
  have V1 : ∀ n, 0 < n → ∀ y, V n y ^ n = 1 := fun n hn y => sys_pow_self hp (e1 y) (e2 y) hn
  have hker : ∀ n, 0 < n → ∀ x : D.La, V n x = 1 ↔ ∃ y, x = n • y := by
    intro n hn x
    have hl := Vl n hn x
    have hr := Vr n hn x
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have k1 := (hev (n.factorization p)).2.2.1 x
    have k2 := I.ker _ hN hNp x
    generalize V n x = q at *
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) x = a at *
    generalize p ^ n.factorization p = P at *
    constructor
    · rintro rfl
      obtain ⟨y1, h1⟩ := k1.1 (by rw [← hl, one_pow])
      obtain ⟨y2, h2⟩ := k2.1 (by rw [← hr, one_pow])
      refine ⟨N.gcdA P • y1 + N.gcdB P • y2, ?_⟩
      have hx : x = ((N : ℤ) * N.gcdA P) • x + ((P : ℤ) * N.gcdB P) • x := by
        rw [← add_smul, bezout hc, one_smul]
      rw [hx, ← hn']
      nth_rewrite 1 [h1]
      rw [h2]
      simp only [← natCast_zsmul, smul_add, smul_smul]
      congr 2 <;> push_cast <;> ring
    · rintro ⟨y, hy⟩
      refine eq_of_pow_eq hc ?_ ?_
      · rw [hl, one_pow]; exact k1.2 ⟨N • y, by rw [hy, ← hn', mul_smul]⟩
      · rw [hr, one_pow]; exact k2.2 ⟨P • y, by rw [hy, ← hn', mul_comm, mul_smul]⟩
  have honto : ∀ n, 0 < n → ∀ q : Q, q ^ n = 1 ↔ ∃ x, V n x = q := by
    intro n hn q
    refine ⟨fun hq => ?_, fun ⟨x, hx⟩ => hx ▸ V1 n hn x⟩
    have hl := Vl n hn
    have hr := Vr n hn
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have a1 := (hev (n.factorization p)).1
    have o1 := (hev (n.factorization p)).2.2.2
    have a2 := I.add (n / p ^ n.factorization p)
    have o2 := I.onto _ hN hNp
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) = f at *
    generalize p ^ n.factorization p = P at *
    obtain ⟨x1, h1⟩ := (o1 (q ^ N)).1 (by rw [← pow_mul, mul_comm, hn', hq])
    obtain ⟨x2, h2⟩ := (o2 (q ^ P)).1 (by rw [← pow_mul, hn', hq])
    refine ⟨((N : ℤ) * N.gcdA P) • x1 + ((P : ℤ) * N.gcdB P) • x2, eq_of_pow_eq hc ?_ ?_⟩
    · rw [hl, a1, hom_zsmul f a1, hom_zsmul f a1, zpow_left hc ((o1 _).2 ⟨x1, rfl⟩), zpow_mul, zpow_natCast,
        (o1 _).2 ⟨x2, rfl⟩, one_zpow, _root_.mul_one, h1]
    · rw [hr, a2, hom_zsmul _ a2, hom_zsmul _ a2, zpow_right hc ((o2 _).2 ⟨x2, rfl⟩), zpow_mul, zpow_natCast,
        (o2 _).2 ⟨x1, rfl⟩, one_zpow, _root_.one_mul, h2]
  have hisom : ∀ n, 0 < n → ∀ x y : D.La, E n (V n x) (V n y) (Z n ^ (2 * D.EF x y)) := by
    intro n hn x y
    obtain ⟨c, hc0⟩ := hex n hn _ _ (V1 n hn x) (V1 n hn y)
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hP : 0 < p ^ n.factorization p := pow_pos hp.pos _
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have hn'' := (mul_comm _ _).trans hn'
    have l1 := hlev _ _ hP hN (V n x) (V n y) c (by rw [hn']; exact V1 n hn x) (by rw [hn']; exact V1 n hn y)
      (by rw [hn']; exact hc0)
    have l2 := hlev _ _ hN hP (V n x) (V n y) c (by rw [hn'']; exact V1 n hn x) (by rw [hn'']; exact V1 n hn y)
      (by rw [hn'']; exact hc0)
    rw [Vl n hn, Vl n hn] at l1
    rw [Vr n hn, Vr n hn] at l2
    have c1 := huniq _ hP _ _ _ _ l1 (hE _ x y)
    have c2 := huniq _ hN _ _ _ _ l2 (I.isom _ hN hNp x y)
    have : c = Z n ^ (2 * D.EF x y) := by
      refine eq_of_pow_eq hc ?_ ?_
      · rw [c1, zpow_pow_comm, Zl n hn]
      · rw [c2, zpow_pow_comm, Zr n hn]
    exact this ▸ hc0
  refine ⟨{ ζ := Z
            ζ_prim := fun n hn => ⟨sys_pow_self hp ζ1 ζ2 hn, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower hp ζ1 ζ2 hζ' I.ζ_pow hn hm
            ev := V
            add := fun n (x y : D.La) => ?_
            lin := fun n (b : D.O) (x : D.La) => ?_
            ker := hker
            onto := honto
            tower := fun n m hn hm x => sys_tower hp (e1 x) (e2 x) (fun r => hev' r x)
              (fun n m hn hm hc => I.tower n m hn hm hc x) hn hm
            isom := hisom }, fun n hn hc y => ?_⟩
  · have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have d1 := (hζ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← Zl n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have d2 := (I.ζ_prim _ hN hNp).dvd_of_pow_eq_one l (by
      rw [← Zr n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have := (cop hp hn).symm.mul_dvd_of_dvd_of_dvd d1 d2
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at this
  · change glue _ _ (ev _ (x + y)) (I.ev _ (x + y)) = glue _ _ (ev _ x) (I.ev _ x) * glue _ _ (ev _ y) (I.ev _ y)
    rw [(hev _).1, I.add, glue_mul]
  · change glue _ _ (ev _ (b • x)) (I.ev _ (b • x)) = act b (glue _ _ (ev _ x) (I.ev _ x))
    rw [(hev _).2.1, I.lin, map_glue _ _ (act b) (hact b)]
  · have h0 : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm)
    have := Vr n hn y
    rw [h0, pow_zero, pow_one, Nat.div_one] at this
    exact this

end GlobalTheory.TateGlue
