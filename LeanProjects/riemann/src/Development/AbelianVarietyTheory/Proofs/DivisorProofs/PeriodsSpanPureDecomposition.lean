import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeMapFiniteEtaleSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.Gen.HeckeGen

section Crt

variable {M : Type} [CommGroup M]

theorem bezout {q a : ℕ} (h : q.Coprime a) : (q : ℤ) * Nat.gcdA q a + a * Nat.gcdB q a = 1 := by
  have e := Nat.gcd_eq_gcd_ab q a
  rw [h.gcd_eq_one] at e
  exact_mod_cast e.symm

def crt (q a : ℕ) (u v : M) : M := u ^ Nat.gcdA q a * v ^ Nat.gcdB q a

theorem crt_pow_left {q a : ℕ} (h : q.Coprime a) {u v : M} (hu : u ^ a = 1) (hv : v ^ q = 1) :
    crt q a u v ^ q = u := by
  have e : Nat.gcdA q a * (q : ℤ) = 1 - a * Nat.gcdB q a := by rw [← bezout h]; ring
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdB q a), zpow_mul,
    zpow_natCast, hv, one_zpow, mul_one, zpow_sub, zpow_mul, zpow_natCast, hu, one_zpow, zpow_one, inv_one, mul_one]

theorem crt_pow_right {q a : ℕ} (h : q.Coprime a) {u v : M} (hu : u ^ a = 1) (hv : v ^ q = 1) :
    crt q a u v ^ a = v := by
  have e : Nat.gcdB q a * (a : ℤ) = 1 - q * Nat.gcdA q a := by rw [← bezout h]; ring
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdA q a), zpow_mul,
    zpow_natCast, hu, one_zpow, one_mul, zpow_sub, zpow_mul, zpow_natCast, hv, one_zpow, zpow_one, inv_one, mul_one]

theorem crt_pow_pow {q a : ℕ} (h : q.Coprime a) (t : M) : crt q a (t ^ q) (t ^ a) = t := by
  rw [crt, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]

theorem eq_of_pow_coprime {q a : ℕ} (h : q.Coprime a) {t t' : M} (h₁ : t ^ q = t' ^ q) (h₂ : t ^ a = t' ^ a) :
    t = t' := by
  rw [← crt_pow_pow h t, h₁, h₂, crt_pow_pow h]

theorem map_zsmul_of_add {L : Type} [AddCommGroup L] (f : L → M) (hf : ∀ x y, f (x + y) = f x * f y) (j : ℤ)
    (x : L) : f (j • x) = f x ^ j :=
  (AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) fun x y => congrArg Additive.ofMul (hf x y)).map_zsmul j x

end Crt

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem exists_join {κ : Type} [Field κ] {Q : Type} [CommGroup Q] (act : D.O → Q → Q)
    (e : ℕ → Q → Q → κˣ → Prop) (hact : ∀ c a b, act c (a * b) = act c a * act c b)
    (E1 : ∀ n, 0 < n → ∀ t t', t ^ n = 1 → t' ^ n = 1 → ∃ z, e n t t' z)
    (E2 : ∀ n t t' z z', e n t t' z → e n t t' z' → z = z')
    (E3 : ∀ n j t t' z, e n t t' z → e (n * j) t t' (z ^ j))
    (E4 : ∀ n j t t' z, e n (t ^ j) (t' ^ j) z → e (n * j ^ 2) t t' z)
    (I : TateIsoO D κ Q act e) (ζ : ℕ → κˣ) (ev : ℕ → D.La → Q)
    (prim : ∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) (ζpow : ∀ r s, ζ (r + s) ^ p ^ s = ζ r)
    (add : ∀ r x y, ev r (x + y) = ev r x * ev r y) (lin : ∀ r (b : D.O) x, ev r (b • x) = act b (ev r x))
    (ker : ∀ r x, ev r x = 1 ↔ ∃ y, x = p ^ r • y) (onto : ∀ r t, t ^ p ^ r = 1 ↔ ∃ x, ev r x = t)
    (tower : ∀ r s x, ev (r + s) x ^ p ^ s = ev r x)
    (isom : ∀ r x y, e (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) :
    ∃ J : GTateIso D.toG κ Q act e, ∀ n, 0 < n → n.Coprime p → ∀ y, J.ev n y = I.ev n y := by
  have hp : p.Prime := Fact.out
  obtain ⟨r, a, h1, h2, h3, h4⟩ : ∃ r a : ℕ → ℕ, (∀ n, p ^ r n * a n = n) ∧ (∀ n, 0 < n → (a n).Coprime p) ∧
      (∀ n m, 0 < n → 0 < m → r (n * m) = r n + r m) ∧ (∀ n m, a (n * m) = a n * a m) :=
    ⟨fun n => n.factorization p, fun n => ordCompl[p] n, fun n => Nat.ordProj_mul_ordCompl_eq_self n p,
      fun n hn => (Nat.coprime_ordCompl hp hn.ne').symm,
      fun n m hn hm => by simp [Nat.factorization_mul hn.ne' hm.ne'], fun n m => Nat.ordCompl_mul n m p⟩
  have apos : ∀ n, 0 < n → 0 < a n := fun n hn => Nat.pos_of_ne_zero fun h => by
    have := h1 n; rw [h, mul_zero] at this; omega
  have cop : ∀ n, 0 < n → (p ^ r n).Coprime (a n) := fun n hn => Nat.Coprime.pow_left _ (h2 n hn).symm
  let T : ℕ → D.La → Q := fun n y => crt (p ^ r n) (a n) (I.ev (a n) y) (ev (r n) y)
  let Z : ℕ → κˣ := fun n => crt (p ^ r n) (a n) (I.ζ (a n)) (ζ (r n))
  have tI : ∀ n, 0 < n → ∀ y, I.ev (a n) y ^ a n = 1 := fun n hn y =>
    (I.onto _ (apos n hn) (h2 n hn) _).2 ⟨y, rfl⟩
  have tE : ∀ s y, ev s y ^ p ^ s = 1 := fun s y => (onto s _).2 ⟨y, rfl⟩
  have T1 : ∀ n, 0 < n → ∀ y, T n y ^ p ^ r n = I.ev (a n) y := fun n hn y =>
    crt_pow_left (cop n hn) (tI n hn y) (tE _ y)
  have T2 : ∀ n, 0 < n → ∀ y, T n y ^ a n = ev (r n) y := fun n hn y =>
    crt_pow_right (cop n hn) (tI n hn y) (tE _ y)
  have Z1 : ∀ n, 0 < n → Z n ^ p ^ r n = I.ζ (a n) := fun n hn =>
    crt_pow_left (cop n hn) (I.ζ_prim _ (apos n hn) (h2 n hn)).pow_eq_one (prim _).pow_eq_one
  have Z2 : ∀ n, 0 < n → Z n ^ a n = ζ (r n) := fun n hn =>
    crt_pow_right (cop n hn) (I.ζ_prim _ (apos n hn) (h2 n hn)).pow_eq_one (prim _).pow_eq_one
  have tT : ∀ n, 0 < n → ∀ y, T n y ^ n = 1 := fun n hn y => by
    conv_lhs => rw [← h1 n]
    rw [h1, ← h1 n, pow_mul, h1, T1 n hn, tI n hn]
  have p1 : ∀ n m, 0 < n → 0 < m → m * p ^ r n = p ^ r (n * m) * a m := fun n m hn hm => by
    rw [h3 n m hn hm, pow_add, mul_assoc, h1, mul_comm]
  have p2 : ∀ n m, m * a n = a (n * m) * p ^ r m := fun n m => by
    rw [h4, mul_assoc, mul_comm (a m), h1, mul_comm]
  have c3 : ∀ n m, 0 < n → 0 < m → (a n * a m).Coprime p := fun n m hn hm =>
    Nat.Coprime.mul_left (h2 n hn) (h2 m hm)
  suffices H : (∀ n, 0 < n → IsPrimitiveRoot (Z n) n) ∧ (∀ n m, 0 < n → 0 < m → Z (n * m) ^ m = Z n) ∧
      (∀ n x y, T n (x + y) = T n x * T n y) ∧ (∀ n (b : D.O) x, T n (b • x) = act b (T n x)) ∧
      (∀ n, 0 < n → ∀ x, T n x = 1 ↔ ∃ y, x = n • y) ∧ (∀ n, 0 < n → ∀ t, t ^ n = 1 ↔ ∃ x, T n x = t) ∧
      (∀ n m, 0 < n → 0 < m → ∀ x, T (n * m) x ^ m = T n x) ∧
      (∀ n, 0 < n → ∀ x y, e n (T n x) (T n y) (Z n ^ (2 * D.EF x y))) ∧
      ∀ n, 0 < n → n.Coprime p → ∀ y, T n y = I.ev n y from
    ⟨⟨Z, H.1, H.2.1, T, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2.1, H.2.2.2.2.2.2.2.1⟩,
      H.2.2.2.2.2.2.2.2⟩
  refine ⟨fun n hn => ⟨?_, fun l hl => ?_⟩, fun n m hn hm => ?_, fun n x y => ?_, fun n b x => ?_,
    fun n hn x => ?_, fun n hn t => ⟨fun ht => ?_, ?_⟩, fun n m hn hm x => ?_, fun n hn x y => ?_,
    fun n hn hc y => ?_⟩
  · have := (I.ζ_prim _ (apos n hn) (h2 n hn)).pow_eq_one
    rwa [← Z1 n hn, ← pow_mul, h1] at this
  · have d1 : a n ∣ l := (I.ζ_prim _ (apos n hn) (h2 n hn)).dvd_of_pow_eq_one l (by
      rw [← Z1 n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have d2 : p ^ r n ∣ l := (prim _).dvd_of_pow_eq_one l (by
      rw [← Z2 n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have := (cop n hn).mul_dvd_of_dvd_of_dvd d2 d1
    rwa [h1] at this
  · have hnm := Nat.mul_pos hn hm
    refine eq_of_pow_coprime (cop n hn) ?_ ?_
    · rw [← pow_mul, p1 n m hn hm, pow_mul, Z1 _ hnm, Z1 n hn, h4, I.ζ_pow _ _ (apos n hn) (apos m hm) (c3 n m hn hm)]
    · rw [← pow_mul, p2 n m, pow_mul, Z2 _ hnm, Z2 n hn, h3 n m hn hm, ζpow]
  · show crt _ _ (I.ev (a n) (x + y)) (ev (r n) (x + y)) = crt _ _ _ _ * crt _ _ _ _
    rw [I.add, add, crt, crt, crt, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · show crt _ _ (I.ev (a n) (b • x)) (ev (r n) (b • x)) = act b (crt _ _ _ _)
    let F : Q →* Q := MonoidHom.mk' (act b) (hact b)
    have hF : ∀ t, act b t = F t := fun _ => rfl
    rw [I.lin, lin, crt, crt, hF, hF, hF, map_mul, map_zpow, map_zpow]
  · constructor
    · intro h
      obtain ⟨u, hu⟩ := (I.ker _ (apos n hn) (h2 n hn) x).1 (by rw [← T1 n hn, h, one_pow])
      obtain ⟨w, hw⟩ := (ker (r n) x).1 (by rw [← T2 n hn, h, one_pow])
      refine ⟨Nat.gcdA (p ^ r n) (a n) • u + Nat.gcdB (p ^ r n) (a n) • w, ?_⟩
      have e1 : n • u = p ^ r n • x := by rw [hu, smul_smul, h1]
      have e2 : n • w = a n • x := by rw [hw, smul_smul, mul_comm, h1]
      rw [smul_add, smul_comm n, smul_comm n, e1, e2, ← natCast_zsmul, ← natCast_zsmul x (a n), smul_smul, smul_smul,
        ← add_smul, mul_comm, mul_comm (Nat.gcdB _ _), bezout (cop n hn), one_smul]
    · rintro ⟨y, rfl⟩
      refine eq_of_pow_coprime (cop n hn) ?_ ?_
      · rw [T1 n hn, one_pow]
        exact (I.ker _ (apos n hn) (h2 n hn) _).2 ⟨p ^ r n • y, by rw [smul_smul, mul_comm, h1]⟩
      · rw [T2 n hn, one_pow]
        exact (ker _ _).2 ⟨a n • y, by rw [smul_smul, h1]⟩
  · obtain ⟨u, hu⟩ := (I.onto _ (apos n hn) (h2 n hn) (t ^ p ^ r n)).1 (by rw [← pow_mul, h1, ht])
    obtain ⟨w, hw⟩ := (onto (r n) (t ^ a n)).1 (by rw [← pow_mul, mul_comm, h1, ht])
    have b := bezout (cop n hn)
    refine ⟨(((p ^ r n : ℕ) : ℤ) * Nat.gcdA (p ^ r n) (a n)) • u + ((a n : ℤ) * Nat.gcdB (p ^ r n) (a n)) • w,
      eq_of_pow_coprime (cop n hn) ?_ ?_⟩
    · rw [T1 n hn, I.add, map_zsmul_of_add _ (I.add _), map_zsmul_of_add _ (I.add _), ← hu, eq_sub_of_add_eq b,
        zpow_sub, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, tI n hn, tI n hn]
      simp
    · rw [T2 n hn, add, map_zsmul_of_add _ (add _), map_zsmul_of_add _ (add _), ← hw, eq_sub_of_add_eq' b,
        zpow_sub, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, tE, tE]
      simp
  · rintro ⟨x, rfl⟩
    exact tT n hn x
  · have hnm := Nat.mul_pos hn hm
    refine eq_of_pow_coprime (cop n hn) ?_ ?_
    · rw [← pow_mul, p1 n m hn hm, pow_mul, T1 _ hnm, T1 n hn, h4, I.tower _ _ (apos n hn) (apos m hm) (c3 n m hn hm)]
    · rw [← pow_mul, p2 n m, pow_mul, T2 _ hnm, T2 n hn, h3 n m hn hm, tower]
  · obtain ⟨z, hz⟩ := E1 n hn _ _ (tT n hn x) (tT n hn y)
    have e : z = Z n ^ (2 * D.EF x y) := by
      refine eq_of_pow_coprime (cop n hn) ?_ ?_
      · have i1 := I.isom _ (apos n hn) (h2 n hn) x y
        rw [← T1 n hn, ← T1 n hn] at i1
        have i2 := E4 _ _ _ _ _ i1
        rw [show a n * (p ^ r n) ^ 2 = n * p ^ r n by rw [sq, ← mul_assoc, mul_comm (a n), h1]] at i2
        rw [E2 _ _ _ _ _ (E3 _ _ _ _ _ hz) i2, ← Z1 n hn, ← zpow_natCast, ← zpow_natCast, zpow_comm]
      · have i1 := isom (r n) x y
        rw [← T2 n hn, ← T2 n hn] at i1
        have i2 := E4 _ _ _ _ _ i1
        rw [show p ^ r n * a n ^ 2 = n * a n by rw [sq, ← mul_assoc, h1]] at i2
        rw [E2 _ _ _ _ _ (E3 _ _ _ _ _ hz) i2, ← Z2 n hn, ← zpow_natCast, ← zpow_natCast, zpow_comm]
    rw [e] at hz
    exact hz
  · have q1 : p ^ r n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left _ hc.symm) (Dvd.intro _ (h1 n))
    have a1 : a n = n := by have := h1 n; rwa [q1, one_mul] at this
    have := T1 n hn y
    rwa [q1, pow_one, a1] at this

theorem exists_join_isog {κ : Type} [Field κ] {Q Q' : Type} [CommGroup Q] [Group Q'] (act : D.O → Q → Q)
    (act' : D.O → Q' → Q') (e : ℕ → Q → Q → κˣ → Prop) (e' : ℕ → Q' → Q' → κˣ → Prop)
    (hact : ∀ c a b, act c (a * b) = act c a * act c b)
    (E1 : ∀ n, 0 < n → ∀ t t', t ^ n = 1 → t' ^ n = 1 → ∃ z, e n t t' z)
    (E2 : ∀ n t t' z z', e n t t' z → e n t t' z' → z = z')
    (E3 : ∀ n j t t' z, e n t t' z → e (n * j) t t' (z ^ j))
    (E4 : ∀ n j t t' z, e n (t ^ j) (t' ^ j) z → e (n * j ^ 2) t t' z)
    (c k m : ℕ) (hc : c.Coprime p) (hk : k.Coprime p) (hm : m * c = k ^ 2) (Ψ : Q →* Q')
    (hsurj : Function.Surjective Ψ) (hker : ∀ t, Ψ t = 1 → t ^ k = 1) (hΨ : ∀ b t, Ψ (act b t) = act' b (Ψ t))
    (E5 : ∀ n t t' z, e' n (Ψ t) (Ψ t') z → e (n * m) t t' z)
    (I : TateIsoO D κ Q act e) (I' : GTateIso D.toG κ Q' act' e') :
    ∃ J : GTateIso D.toG κ Q act e, ∀ n, 0 < n → n.Coprime p → ∀ y, J.ev n y = I.ev n y := by
  have hp : p.Prime := Fact.out
  have q0 : ∀ r, 0 < p ^ r := fun r => pow_pos hp.pos r
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Q' →* Q, ∀ t, Φ (Ψ t) = t ^ k :=
    ⟨Ψ.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨powMonoidHom k, fun t ht => hker t ht⟩, fun t => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t⟩
  have hΨΦ : ∀ u, Ψ (Φ u) = u ^ k := fun u => by
    obtain ⟨t, rfl⟩ := hsurj u
    rw [hΦ, map_pow]
  have ck : ∀ r, (p ^ r).Coprime k := fun r => Nat.Coprime.pow_left _ hk.symm
  have cm : ∀ r, (p ^ r).Coprime m := fun r =>
    Nat.Coprime.coprime_dvd_right (Dvd.intro _ hm) (Nat.Coprime.pow_right 2 (ck r))
  have tor : ∀ r (x : D.La), Φ (I'.ev (p ^ r) x) ^ p ^ r = 1 := fun r x => by
    rw [← map_pow, (I'.onto _ (q0 r) _).2 ⟨x, rfl⟩, map_one]
  have e11 : e 1 1 1 1 := by
    have h := I.isom 1 one_pos (Nat.coprime_one_left p) 0 0
    rwa [(I.ker 1 one_pos (Nat.coprime_one_left p) 0).2 ⟨0, (smul_zero _).symm⟩, map_zero, mul_zero, zpow_zero] at h
  refine exists_join act e hact E1 E2 E3 E4 I (fun r => I'.ζ (p ^ r) ^ c) (fun r x => Φ (I'.ev (p ^ r) x))
    (fun r => (I'.ζ_prim _ (q0 r)).pow_of_coprime c (Nat.Coprime.pow_right _ hc)) (fun r s => ?_)
    (fun r x y => ?_) (fun r b x => ?_) (fun r x => ⟨fun h => ?_, fun h => ?_⟩) (fun r t => ⟨fun ht => ?_, ?_⟩)
    (fun r s x => ?_) (fun r x y => ?_)
  · rw [← pow_mul, mul_comm, pow_mul, pow_add, I'.ζ_pow _ _ (q0 r) (q0 s)]
  · exact (congrArg Φ (I'.add _ x y)).trans (map_mul Φ _ _)
  · refine (congrArg Φ (I'.lin _ b x)).trans ?_
    obtain ⟨t, ht⟩ := hsurj (I'.ev (p ^ r) x)
    let F : Q →* Q := MonoidHom.mk' (act b) (hact b)
    have hF : ∀ t, act b t = F t := fun _ => rfl
    show Φ (act' b (I'.ev (p ^ r) x)) = act b (Φ (I'.ev (p ^ r) x))
    rw [← ht, ← hΨ, hΦ, hΦ, hF, hF, map_pow]
  · refine (I'.ker _ (q0 r) x).1 ?_
    have h1 : I'.ev (p ^ r) x ^ k = 1 := by rw [← hΨΦ]; exact (congrArg Ψ h).trans (map_one Ψ)
    have h2 : I'.ev (p ^ r) x ^ p ^ r = 1 := (I'.onto _ (q0 r) _).2 ⟨x, rfl⟩
    have h3 := pow_gcd_eq_one.2 ⟨h2, h1⟩
    rwa [(ck r).gcd_eq_one, pow_one] at h3
  · exact (congrArg Φ ((I'.ker _ (q0 r) x).2 h)).trans (map_one Φ)
  · obtain ⟨x, hx⟩ := (I'.onto _ (q0 r) (Ψ (t ^ Nat.gcdB (p ^ r) k))).1 (by
      rw [← map_pow, ← zpow_natCast, zpow_comm, zpow_natCast, ht, one_zpow, map_one])
    refine ⟨x, ?_⟩
    have h := crt_pow_pow (ck r) t
    rw [crt, ht, one_zpow, one_mul] at h
    show Φ (I'.ev (p ^ r) x) = t
    rw [hx, hΦ, ← zpow_natCast, zpow_comm, zpow_natCast, h]
  · rintro ⟨x, rfl⟩
    exact tor r x
  · show Φ (I'.ev (p ^ (r + s)) x) ^ p ^ s = Φ (I'.ev (p ^ r) x)
    rw [← map_pow, pow_add]
    exact congrArg Φ (I'.tower _ _ (q0 r) (q0 s) x)
  · obtain ⟨z, hz⟩ := E1 _ (q0 r) _ _ (tor r x) (tor r y)
    have i1 := I'.isom _ (q0 r) (k • x) (k • y)
    have hv : ∀ w : D.La, I'.ev (p ^ r) (k • w) = Ψ (Φ (I'.ev (p ^ r) w)) := fun w =>
      (HeckeRestrict.ev_nsmul I' _ k w).trans (hΨΦ _).symm
    rw [hv, hv] at i1
    have i2 := E2 _ _ _ _ _ (E3 _ m _ _ _ hz) (E5 _ _ _ _ i1)
    have i3 : e 1 (Φ (I'.ev (p ^ r) x) ^ p ^ r) (Φ (I'.ev (p ^ r) y) ^ p ^ r) 1 := by rw [tor, tor]; exact e11
    have i4 := E4 _ _ _ _ _ i3
    rw [one_mul, sq] at i4
    have i5 := E2 _ _ _ _ _ (E3 _ (p ^ r) _ _ _ hz) i4
    have eF : D.toG.EF (k • x) (k • y) = (c : ℤ) * (D.EF x y * m) := by
      show D.EF (k • x) (k • y) = _
      have hm' : (m : ℤ) * c = k ^ 2 := by exact_mod_cast hm
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      linear_combination (-(D.EF x y)) * hm'
    have ez : z = (I'.ζ (p ^ r) ^ c) ^ (2 * D.EF x y) := by
      refine eq_of_pow_coprime (cm r) ?_ ?_
      · rw [i5, ← zpow_natCast, zpow_comm, zpow_natCast, ← pow_mul, mul_comm c, pow_mul,
          (I'.ζ_prim _ (q0 r)).pow_eq_one, one_pow, one_zpow]
      · rw [i2, eF, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
        congr 1
        ring
    rw [ez] at hz
    exact hz

open MonObj HeckeRestrict

theorem unitOn_bij {κ : Type} [CommRing κ] : Function.Bijective (unitOn (R := κ)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of κ)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

variable {R : Type} [CommRing R]

open GlobalTheory.UPel.HT.Hecke in

theorem tate_hecke_back {b : Base D R} (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (hc : c.Coprime p) (hk : k.Coprime p)
    (Npos : 0 < N) (hN : N.Coprime p) {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (h : IsHecke g c k N o o' ψ)
    (κ : Type) [Field κ] [IsAlgClosed κ] (hnκ : ∀ n : ℕ, 0 < n → (n : κ) ≠ 0) (x : Sp κ ⟶ S) (β : R →+* κ)
    (hx : x ≫ s = spMap β) (I' : _root_.GlobalTheory.UPel.HT.Gen.HeckeRestrict.TateAt D.toG o'.A o'.act o'.P x) :
    ∃ J : _root_.GlobalTheory.UPel.HT.Gen.HeckeRestrict.TateAt D.toG o.A o.act o.P x, ∀ y, toUnit _ ≫ o.eta y = J.ev (N * k) y := by
  obtain ⟨hψ, hact, heta, hGal, ⟨hiso⟩, hck⟩ := h
  obtain ⟨I, hI⟩ := o.geom κ x β hx
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have kpos : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hk; omega
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hL' : (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left).IsLB := pull_isLB o'.isLB _
  have hsurj : ∀ q : Over.mk x ⟶ o'.A, ∃ a : Over.mk x ⟶ o.A, a ≫ ψ = q := fun q => by
    haveI := hGal.fin
    haveI := hGal.onto
    obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
    let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
      show a₀ ≫ o.A.hom = x
      rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
    exact ⟨a, Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)⟩
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 → t ^ k = 1 := by
    intro t ht
    have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
      rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
    obtain ⟨h, hh, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
    obtain ⟨z, hz⟩ := h.2
    have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl h.1 :=
      Over.OverMorphism.ext (by rw [Over.comp_left]; exact hh.symm)
    rw [e2, TateTransl.one_comp_transl_pt, hz, hI, ← I.ev_nsmul, smul_smul,
      I.ker _ (Nat.mul_pos Npos kpos) (Nat.Coprime.mul_left hN hk)]
    exact ⟨g z, by rw [mul_comm]⟩
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left).pull ψ.left) := by
    have hP := o.isLB
    have hP' := o'.isLB
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB hP _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb hP, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [GlobalTheory.UPel.HT.Hecke.sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc,
      Category.comp_id]
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ o'.A) :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  obtain ⟨J, hJ⟩ := exists_join_isog (D := D) (κ := κ) (Q := Over.mk x ⟶ o.A) (Q' := Over.mk x ⟶ o'.A)
    (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o'.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))
    (fun n g g' z => Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n g g' (unitOn z))
    (fun c a a' => haveI := o.act.hom c; MonObj.mul_comp a a' _)
    (fun n hn t t' ht ht' => by
      obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S o.A _ o.ab hL κ x n hn (hnκ n hn) t t' ht ht'
      obtain ⟨z, rfl⟩ := unitOn_bij.2 e
      exact ⟨z, he⟩)
    (fun n t t' z z' h h' => unitOn_bij.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG o.ab hL h h'))
    (fun n j t t' z h => by
      have e : unitOn (z ^ j) = unitOn z ^ j := map_pow _ _ _
      rw [Nat.cast_mul, e]
      exact GlobalTheory.WeilIsogeny.weilIs_pow hG o.ab hL j h)
    (fun n j t t' z h => by
      haveI := isMonHom_mulA (A := o.A) j
      have e : ∀ u : Over.mk x ⟶ o.A, u ^ j = u ≫ Out.mulA o.A j := fun u => by
        rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
      rw [e, e] at h
      rw [Nat.cast_mul]
      exact GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL (Out.mulA o.A j)
        (GlobalTheory.HeckeWeilValue.lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ j) h)
    c k (k ^ 2 / c) hc hk (Nat.div_mul_cancel hck) Ψ hsurj hker
    (fun b' t => by
      show (t ≫ o.act.act b') ≫ ψ = (t ≫ ψ) ≫ o'.act.act b'
      rw [Category.assoc, hact, Category.assoc])
    (fun n t t' z h => by
      rw [Nat.cast_mul]
      exact GlobalTheory.WeilIsogeny.weilIs_pull_hom hG o.ab hL hL' ψ hiso2 h) I I'
  exact ⟨J, fun y => (hI y).trans (hJ _ (Nat.mul_pos Npos kpos) (Nat.Coprime.mul_left hN hk) y).symm⟩

variable [Algebra ℚ R]

theorem natCast_ne_zero_of_hom {κ : Type} [Field κ] (β : R →+* κ) (n : ℕ) (hn : 0 < n) : (n : κ) ≠ 0 := by
  have h : IsUnit ((β.comp (algebraMap ℚ R)) (n : ℚ)) :=
    (IsUnit.mk0 (n : ℚ) (by exact_mod_cast hn.ne')).map _
  rw [map_natCast] at h
  exact h.ne_zero

def baseAt (gb : GBase D.toG R) : Base D R where
  unit k hk := by
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    have k0 : k ≠ 0 := fun h => by subst h; rw [Nat.coprime_zero_left] at hk; omega
    have h := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast k0)).map (algebraMap ℚ R)
    rwa [map_natCast] at h
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart _ _ _ k _ _ β :=
    absurd (CharP.cast_eq_zero k p) (natCast_ne_zero_of_hom β p (Fact.out : p.Prime).pos)

def toObj {gb : GBase D.toG R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (s' : S ⟶ Sp R) (hs : s' = s)
    (o : GObj gb N s) (hker : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1) :
    Obj (baseAt gb) N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := hker
  rosati := o.rosati
  lie R' _ β x hx := o.lie R' β x (hs ▸ hx)
  lieRank k _ _ x β hx := o.lieRank k x β (hs ▸ hx)
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom k x β (hs ▸ hx)
    exact ⟨⟨I.ζ, fun n hn _ => I.ζ_prim n hn, fun n m hn hm _ => I.ζ_pow n m hn hm, I.ev, I.add, I.lin,
      fun n hn _ => I.ker n hn, fun n hn _ => I.onto n hn, fun n m hn hm _ => I.tower n m hn hm,
      fun n hn _ => I.isom n hn⟩, hI⟩

theorem spMap_id' : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

theorem exists_immersion [IsNoetherianRing R] (gb : GBase D.toG R) (N : ℕ) (h3 : 3 ≤ N) (hN : N.Coprime p)
    (M : Model (baseAt gb) N) (X : GenModel gb N) :
    ∃ i : X.X ⟶ M.X, IsOpenImmersion i ∧ IsClosedImmersion i ∧ i ≫ M.s = X.s ∧ IsGPull X.univ M.univ i := by
  obtain ⟨j, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre p D R (baseAt gb) R (RingHom.id R) gb rfl (fun _ => rfl) N h3 hN M X
  haveI : IsIso (spMap (RingHom.id R)) := by rw [spMap_id']; infer_instance
  refine ⟨j ≫ pullback.fst _ _, inferInstance, inferInstance, ?_, h4⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, h3, spMap_id', Category.comp_id]

open GlobalTheory.UPel.HT.Hecke in

theorem exists_gHeckeMap_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (X : GenModel gb N) (X' : GenModel gb (N * k)), ∃ π : X'.X ⟶ X.X, IsGHeckeMap g c k N X X' π ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  intro p _ D R _ _ _ gb g c k N hcp hkp hN hNp hEF hg hck X X'
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have kpos : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hkp; omega
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hcp; omega
  have Npos : 0 < N := by omega
  have hNk : 3 ≤ N * k := hN.trans (Nat.le_mul_of_pos_right _ kpos)
  have hNkp : (N * k).Coprime p := Nat.Coprime.mul_left hNp hkp
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (baseAt gb) N hN hNp
  obtain ⟨M'⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (baseAt gb) (N * k) hNk hNkp
  obtain ⟨π, hπ, πf, πe, πs⟩ := GlobalTheory.T.exists_heckeMap_finite_etale_surjective' p D R (baseAt gb) g c k N hcp hkp hN hNp hEF hg hck M M'
  change π ≫ M.s = M'.s ∧ ∃ (o' : Obj (baseAt gb) N M'.s) (ψ : M'.univ.A ⟶ o'.A), IsHecke g c k N M'.univ o' ψ ∧
    Nonempty (ObjMap o' M.univ π) at hπ
  obtain ⟨hπs, o', ψ, hH, ⟨hmap⟩⟩ := hπ
  obtain ⟨i, io, ic, hi, hX⟩ := exists_immersion gb N hN hNp M X
  obtain ⟨i', io', ic', hi', hX'⟩ := exists_immersion gb (N * k) hNk hNkp M' X'

  obtain ⟨Z, ⟨hZ⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R (baseAt gb) N M'.X X'.X M'.s i' o'
  obtain ⟨χ', χ₂', hc', hsq', hact', ⟨hpol'⟩, heta'⟩ := id hX'
  obtain ⟨eK, heK, hK⟩ := M'.univ.kerP
  let U : Obj (baseAt gb) (N * k) (i' ≫ M'.s) := toObj _ hi' X'.univ
    ⟨eK, heK, fun T x hx => GlobalTheory.HTPull.kernel_pullback hc' hsq' M'.univ.isLB X'.univ.isLB hpol' eK hK T x hx⟩
  have hU : ObjMap U M'.univ i' := ⟨χ', χ₂', hc', hsq', hact', hpol', heta'⟩
  obtain ⟨ψ₁, hH₁⟩ := PullHecke.isHecke_pull p D R (baseAt gb) g c k N hkp hN hNp _ _ M'.s i' M'.univ o' ψ U Z hH hU hZ
  have hs : X'.s ≫ spMap (RingHom.id R) = i' ≫ M'.s := by rw [spMap_id', Category.comp_id, hi']
  have hgeom : ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ X'.X) (β : R →+* κ), x ≫ X'.s = spMap β →
      ∃ I : _root_.GlobalTheory.UPel.HT.Gen.HeckeRestrict.TateAt D.toG Z.A Z.act Z.P x, ∀ y, toUnit _ ≫ Z.eta y = I.ev N y := by
    intro κ _ _ x β hx
    obtain ⟨I₀, hI₀⟩ := X'.univ.geom κ x β hx
    exact tate_hecke g c k N cpos kpos Npos hEF hg U Z ψ₁ hH₁ κ (natCast_ne_zero_of_hom β) x I₀ hI₀
  let Y : GObj gb N X'.s := toGObj (b := baseAt gb) (RingHom.id R) gb rfl (fun _ => rfl) X'.s hs Z hgeom
  obtain ⟨πX, ⟨hπX, ⟨hY⟩⟩, -⟩ := X.rep X'.X X'.s Y
  have sq : πX ≫ i = i' ≫ π := by
    obtain ⟨χ, χ₂, hc, hsq, hact, ⟨hpol⟩, heta⟩ := isGPull_comp hY hX
    refine (M.rep X'.X _ Z).unique ⟨?_, ⟨⟨χ, χ₂, hc, hsq, hact, hpol, heta⟩⟩⟩ ⟨?_, ?_⟩
    · rw [Category.assoc, hi, hπX, hi']
    · rw [Category.assoc, hπs]
    · exact GlobalTheory.UPel.HT.objMap_comp p D R (baseAt gb) N _ _ _ _ _ _ Z o' M.univ _ π hZ hmap
  refine ⟨πX, ⟨hπX, Y, ψ₁, ⟨hH₁.1, hH₁.2.1, hH₁.2.2.1, hH₁.2.2.2.1, hH₁.2.2.2.2⟩, ⟨hY⟩⟩, ?_, ?_, ⟨fun z => ?_⟩⟩
  · haveI : IsFinite (πX ≫ i) := by rw [sq]; infer_instance
    exact IsFinite.of_comp πX i
  · haveI : Etale (πX ≫ i) := by rw [sq]; infer_instance
    exact Etale.of_comp πX i
  obtain ⟨κ, _, _, x, hxz⟩ := GlobalTheory.FinEt.exists_algClosed_point X.X z
  obtain ⟨x', hx'⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π (x ≫ i)
  obtain ⟨V, ⟨hV⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R (baseAt gb) (N * k) M'.X _ M'.s x' M'.univ
  have hsV : (x' ≫ M'.s) ≫ spMap (RingHom.id R) = x' ≫ M'.s := by rw [spMap_id', Category.comp_id]
  have hgV : ∀ (κ₁ : Type) [Field κ₁] [IsAlgClosed κ₁] (y : Sp κ₁ ⟶ Sp κ) (β : R →+* κ₁),
      y ≫ x' ≫ M'.s = spMap β → ∃ I : _root_.GlobalTheory.UPel.HT.Gen.HeckeRestrict.TateAt D.toG V.A V.act V.P y, ∀ w, toUnit _ ≫ V.eta w = I.ev (N * k) w := by
    intro κ₁ _ _ y β hy
    obtain ⟨I₀, -⟩ := X.univ.geom κ₁ (y ≫ x) β (by
      rw [← hy, ← hi, ← hπs, Category.assoc, ← Category.assoc x, hx', Category.assoc])
    obtain ⟨χ, χ₂, hc, hsq, hact, ⟨hpol⟩, -⟩ := hX
    obtain ⟨I₁, -⟩ := (tate_pullback D.toG M.univ.A X.univ.A M.univ.act X.univ.act M.univ.P X.univ.P
      M.univ.isLB X.univ.isLB _ χ χ₂ hc hsq hact hpol κ₁ (y ≫ x)).1 I₀
    have e : (y ≫ x) ≫ i = (y ≫ x') ≫ π := by rw [Category.assoc, hx', Category.assoc]
    obtain ⟨I₂, -⟩ := (tate_pullback D.toG M.univ.A o'.A M.univ.act o'.act M.univ.P o'.P
      M.univ.isLB o'.isLB _ hmap.φ hmap.φ₂ hmap.cart hmap.sq hmap.act hmap.pol κ₁ (y ≫ x')).2 (e ▸ I₁)
    obtain ⟨I₃, hI₃⟩ := tate_hecke_back g c k N hcp hkp Npos hNp M'.univ o' ψ hH κ₁ (natCast_ne_zero_of_hom β)
      (y ≫ x') β (by rw [Category.assoc, hy]) I₂
    obtain ⟨I₄, hI₄⟩ := (tate_pullback D.toG M'.univ.A V.A M'.univ.act V.act M'.univ.P V.P
      M'.univ.isLB V.isLB _ hV.φ hV.φ₂ hV.cart hV.sq hV.act hV.pol κ₁ y).2 I₃
    refine ⟨I₄, fun w => (GlobalTheory.ObjPull.pushEquiv (G' := V.A) (G := M'.univ.A) hV.cart (Over.mk y)).injective
      (Over.OverMorphism.ext ?_)⟩
    have h2 : ((y ≫ x') ≫ (M'.univ.eta w).left) = (I₃.ev (N * k) w).left := by
      simpa only [Over.comp_left, toUnit_left, Over.mk_hom] using congrArg Over.Hom.left (hI₃ w)
    calc (GlobalTheory.ObjPull.pushEquiv (G' := V.A) (G := M'.univ.A) hV.cart (Over.mk y) (toUnit _ ≫ V.eta w)).left
        = y ≫ (V.eta w).left ≫ hV.φ := by
          rw [GlobalTheory.ObjPull.pushEquiv_left]; simp only [Over.comp_left, toUnit_left, Over.mk_hom, Category.assoc]
      _ = (y ≫ x') ≫ (M'.univ.eta w).left := by
          rw [hV.eta]; simp only [Category.assoc]
      _ = (I₃.ev (N * k) w).left := h2
      _ = (I₄.ev (N * k) w).left ≫ hV.φ := hI₄ _ _
      _ = _ := (GlobalTheory.ObjPull.pushEquiv_left _ _ _).symm
  obtain ⟨f, ⟨hf, ⟨hW⟩⟩, -⟩ := X'.rep _ _
    (toGObj (b := baseAt gb) (RingHom.id R) gb rfl (fun _ => rfl) (x' ≫ M'.s) hsV V hgV)
  have hfi : f ≫ i' = x' := by
    obtain ⟨χ, χ₂, hc, hsq, hact, ⟨hpol⟩, heta⟩ := isGPull_comp hW hX'
    refine (M'.rep _ _ V).unique ⟨?_, ⟨⟨χ, χ₂, hc, hsq, hact, hpol, heta⟩⟩⟩ ⟨rfl, ⟨hV⟩⟩
    rw [Category.assoc, hi', hf]
  have hfx : f ≫ πX = x := by
    rw [← cancel_mono i, Category.assoc, sq, ← Category.assoc, hfi, hx']
  obtain ⟨u, hu⟩ : z ∈ Set.range x := by rw [hxz]; rfl
  exact ⟨f u, by rw [← hu, ← hfx]; rfl⟩

end GlobalTheory.UPel.HT.Gen.HeckeGen
