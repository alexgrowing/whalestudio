import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GTateGlue

section Grp

variable {G : Type} [CommGroup G]

theorem bezout {a b : ℕ} (h : a.Coprime b) : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]

theorem ext_pow {a b : ℕ} (h : a.Coprime b) {q r : G} (ha : q ^ a = r ^ a) (hb : q ^ b = r ^ b) : q = r := by
  have e : ∀ t : G, t = (t ^ a) ^ Nat.gcdA a b * (t ^ b) ^ Nat.gcdB a b := fun t => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [e q, ha, hb, ← e r]

def crt (a b : ℕ) (x y : G) : G := x ^ Nat.gcdB a b * y ^ Nat.gcdA a b

theorem crt_mul (a b : ℕ) (x y x' y' : G) : crt a b (x * x') (y * y') = crt a b x y * crt a b x' y' := by
  simp only [crt, mul_zpow]
  exact mul_mul_mul_comm _ _ _ _

theorem crt_pow_right {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ b = x := by
  have e : Nat.gcdB a b * (b : ℤ) = 1 + a * (-Nat.gcdA a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdA a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.mul_one]

theorem crt_pow_left {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ a = y := by
  have e : Nat.gcdA a b * (a : ℤ) = 1 + b * (-Nat.gcdB a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdB a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.one_mul]

variable (p : ℕ) [hp : Fact p.Prime]

def cp (n : ℕ) : ℕ := n / p ^ n.factorization p

theorem cp_mul_pow (n : ℕ) : cp p n * p ^ n.factorization p = n := by
  rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self n p

theorem cp_pos {n : ℕ} (hn : 0 < n) : 0 < cp p n := Nat.ordCompl_pos p hn.ne'

theorem cp_coprime {n : ℕ} (hn : 0 < n) : (cp p n).Coprime p := (Nat.coprime_ordCompl hp.out hn.ne').symm

theorem cp_coprime_pow {n : ℕ} (hn : 0 < n) : (cp p n).Coprime (p ^ n.factorization p) :=
  (cp_coprime p hn).pow_right _

theorem cp_mul (n m : ℕ) : cp p (n * m) = cp p n * cp p m := Nat.ordCompl_mul n m p

def sys (f g : ℕ → G) (n : ℕ) : G := crt (cp p n) (p ^ n.factorization p) (f (cp p n)) (g (n.factorization p))

variable {p} {f g : ℕ → G} (hf : ∀ n, 0 < n → n.Coprime p → f n ^ n = 1) (hg : ∀ e, g e ^ p ^ e = 1)

include hf hg in
theorem sys_right {n : ℕ} (hn : 0 < n) : sys p f g n ^ p ^ n.factorization p = f (cp p n) :=
  crt_pow_right (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_left {n : ℕ} (hn : 0 < n) : sys p f g n ^ cp p n = g (n.factorization p) :=
  crt_pow_left (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_tower (hf' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → f (n * m) ^ m = f n)
    (hg' : ∀ e, g (e + 1) ^ p = g e) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hg'' : ∀ e d, g (e + d) ^ p ^ d = g e := fun e d => by
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, hg', ih]
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have ef : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have r := sys_right hf hg hnm
  have l := sys_left hf hg hnm
  refine ext_pow (cp_coprime_pow p hn) ?_ ?_
  · have e : m * cp p n = cp p (n * m) * p ^ m.factorization p := by
      rw [cp_mul, _root_.mul_assoc, cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, l, ef, hg'', sys_left hf hg hn]
  · have e : m * p ^ n.factorization p = p ^ (n * m).factorization p * cp p m := by
      rw [ef, pow_add, _root_.mul_assoc, mul_comm _ (cp p m), cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, r, cp_mul, hf' _ _ (cp_pos p hn) (cp_pos p hm)
      (Nat.Coprime.mul_left (cp_coprime p hn) (cp_coprime p hm)), sys_right hf hg hn]

include hf hg in
theorem sys_of_coprime {n : ℕ} (hn : 0 < n) (h : n.Coprime p) : sys p f g n = f n := by
  have e : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp.out).1 h.symm)
  have r := sys_right hf hg hn
  rwa [cp, e, pow_zero, pow_one, Nat.div_one] at r

end Grp

theorem exists_gTateIso {p : ℕ} [Fact p.Prime] (D : Datum p) {k : Type} [Field k] {Q : Type} [CommGroup Q]
    (act : D.O → Q → Q) (hact : ∀ c q r, act c (q * r) = act c q * act c r) (W : ℕ → Q → Q → kˣ → Prop)
    (hW : ∀ (a b : ℕ) (q r : Q) (c : kˣ), 0 < a → 0 < b → a.Coprime b → q ^ (a * b) = 1 → r ^ (a * b) = 1 →
      W a (q ^ b) (r ^ b) (c ^ b) → W b (q ^ a) (r ^ a) (c ^ a) → W (a * b) q r c)
    (I : TateIsoO D k Q act W) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q)
    (h₁ : ∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) (h₂ : ∀ e, ζ (e + 1) ^ p = ζ e)
    (h₃ : ∀ e y z, ev e (y + z) = ev e y * ev e z) (h₄ : ∀ e (c : D.O) y, ev e (c • y) = act c (ev e y))
    (h₅ : ∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) (h₆ : ∀ e (q : Q), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q)
    (h₇ : ∀ e y, ev (e + 1) y ^ p = ev e y)
    (h₈ : ∀ e y z, W (p ^ e) (ev e y) (ev e z) (ζ e ^ (2 * D.EF y z))) :
    ∃ J : GTateIso D.toG k Q act W, ∀ n, 0 < n → n.Coprime p → ∀ y, J.ev n y = I.ev n y := by
  have zf : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n a b => (I.ζ_prim n a b).pow_eq_one
  have zg : ∀ e, ζ e ^ p ^ e = 1 := fun e => (h₁ e).pow_eq_one
  have ef : ∀ y n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n a b => (I.onto n a b _).2 ⟨y, rfl⟩
  have eg : ∀ y e, ev e y ^ p ^ e = 1 := fun y e => (h₆ e _).2 ⟨y, rfl⟩
  let E : ℕ → D.La → Q := fun n y => sys p (fun m => I.ev m y) (fun e => ev e y) n
  have ER : ∀ n, 0 < n → ∀ y, E n y ^ p ^ n.factorization p = I.ev (cp p n) y := fun n hn y =>
    sys_right (ef y) (eg y) hn
  have EL : ∀ n, 0 < n → ∀ y, E n y ^ cp p n = ev (n.factorization p) y := fun n hn y =>
    sys_left (ef y) (eg y) hn
  have tors : ∀ n, 0 < n → ∀ y, E n y ^ (cp p n * p ^ n.factorization p) = 1 := fun n hn y => by
    rw [pow_mul, EL n hn, eg]
  refine ⟨{ ζ := sys p I.ζ ζ
            ζ_prim := fun n hn => ⟨?_, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower zf zg I.ζ_pow h₂ hn hm
            ev := E
            add := fun n (y z : D.La) => ?_
            lin := fun n (c : D.O) (y : D.La) => ?_
            ker := fun n hn (y : D.La) => ⟨fun h => ?_, ?_⟩
            onto := fun n hn q => ⟨fun h => ?_, ?_⟩
            tower := fun n m hn hm y =>
              sys_tower (ef y) (eg y) (fun a b ha hb hab => I.tower a b ha hb hab y) (fun e => h₇ e y) hn hm
            isom := fun n hn (y z : D.La) => ?_ },
    fun n hn h y => sys_of_coprime (ef y) (eg y) hn h⟩
  · have e : sys p I.ζ ζ n ^ (cp p n * p ^ n.factorization p) = 1 := by rw [pow_mul, sys_left zf zg hn, zg]
    rwa [cp_mul_pow] at e
  · have a := (I.ζ_prim _ (cp_pos p hn) (cp_coprime p hn)).dvd_of_pow_eq_one l (by
      rw [← sys_right zf zg hn, pow_right_comm, hl, one_pow])
    have b := (h₁ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← sys_left zf zg hn, pow_right_comm, hl, one_pow])
    have := (cp_coprime_pow p hn).mul_dvd_of_dvd_of_dvd a b
    rwa [cp_mul_pow] at this
  · exact (congrArg₂ (crt _ _) (I.add _ y z) (h₃ _ y z)).trans (crt_mul _ _ _ _ _ _)
  · refine (congrArg₂ (crt _ _) (I.lin _ c y) (h₄ _ c y)).trans ?_
    let φ : Q →* Q := MonoidHom.mk' (act c) (hact c)
    show φ _ ^ _ * φ _ ^ _ = φ (_ ^ _ * _ ^ _)
    rw [map_mul, map_zpow, map_zpow]
  · obtain ⟨z₁, e₁⟩ := (I.ker _ (cp_pos p hn) (cp_coprime p hn) y).1 (by rw [← ER n hn, h, one_pow])
    obtain ⟨z₂, e₂⟩ := (h₅ (n.factorization p) y).1 (by rw [← EL n hn, h, one_pow])
    have bz := bezout (cp_coprime_pow p hn)
    have en := cp_mul_pow p n
    generalize cp p n = a at *
    generalize p ^ n.factorization p = b at *
    refine ⟨(Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La), ?_⟩
    show y = n • (Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La)
    calc y = ((a : ℤ) * Nat.gcdA a b) • y + ((b : ℤ) * Nat.gcdB a b) • y := by rw [← add_smul, bz, one_smul]
      _ = ((a : ℤ) * Nat.gcdA a b) • (b • z₂) + ((b : ℤ) * Nat.gcdB a b) • (a • z₁) := by rw [← e₁, ← e₂]
      _ = _ := by rw [← en]; module
  · rintro (⟨z, hz⟩ : ∃ z : D.La, y = n • z)
    have hz' : y = (cp p n * p ^ n.factorization p) • z := by rw [cp_mul_pow]; exact hz
    refine ext_pow (cp_coprime_pow p hn) ?_ ?_
    · rw [EL n hn, one_pow]
      exact (h₅ _ _).2 ⟨cp p n • (z : D.La), by rw [hz', mul_comm, mul_smul]⟩
    · rw [ER n hn, one_pow]
      exact (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨p ^ n.factorization p • (z : D.La), by rw [hz', mul_smul]⟩
  · obtain ⟨y₁, e₁⟩ := (I.onto _ (cp_pos p hn) (cp_coprime p hn) (q ^ p ^ n.factorization p)).1 (by
      rw [← pow_mul, mul_comm, cp_mul_pow, h])
    obtain ⟨y₂, e₂⟩ := (h₆ (n.factorization p) (q ^ cp p n)).1 (by rw [← pow_mul, cp_mul_pow, h])
    have bz := bezout (cp_coprime_pow p hn)
    refine ⟨(y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) : D.La),
      ext_pow (cp_coprime_pow p hn) ?_ ?_⟩
    · have e : y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) =
          y₂ + p ^ n.factorization p • Nat.gcdB (cp p n) (p ^ n.factorization p) • (y₁ - y₂) := by
        generalize cp p n = a at *
        generalize p ^ n.factorization p = b at *
        linear_combination (norm := module) bz • (y₂ - y₁)
      rw [EL n hn, e, h₃, e₂, (h₅ _ _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [ER n hn, I.add, e₁, (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨_, rfl⟩, _root_.mul_one]
  · rintro ⟨y, rfl⟩
    have := tors n hn y
    rwa [cp_mul_pow] at this
  · have sw : ∀ (u : kˣ) (t : ℤ) (j : ℕ), (u ^ t) ^ j = (u ^ j) ^ t := fun u t j => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have := hW (cp p n) (p ^ n.factorization p) (E n y) (E n z) (sys p I.ζ ζ n ^ (2 * D.EF y z)) (cp_pos p hn)
      (pow_pos (Fact.out : p.Prime).pos _) (cp_coprime_pow p hn) (tors n hn y) (tors n hn z)
      (by rw [ER n hn, ER n hn, sw, sys_right zf zg hn]; exact I.isom _ (cp_pos p hn) (cp_coprime p hn) y z)
      (by rw [EL n hn, EL n hn, sw, sys_left zf zg hn]; exact h₈ _ y z)
    rwa [cp_mul_pow] at this

section Weil

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : LB A.left}
  (hL : L.IsLB) {T : Over S}

include hA hL in

theorem weilIs_pow_eq {a b : ℕ} (hb : 0 < b) {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c) (h' : Out.WeilIs A L a (x ^ b) (y ^ b) c') : c ^ b = c' := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h₀ := CommPairing.weilIs_symm hL h
  have pw : ∀ j : ℕ, Out.WeilIs A L ((a * b : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih h₀
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have h₂ := CommPairing.weilIs_symm hL (pw j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  exact PairingLevels.weilIs_value_eq hG hA hL ht h₂ h'

include hA hL in

theorem weilIs_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (a * b) = 1) (hy : y ^ (a * b) = 1)
    (h₁ : Out.WeilIs A L a (x ^ b) (y ^ b) (c ^ b)) (h₂ : Out.WeilIs A L b (x ^ a) (y ^ a) (c ^ a)) :
    Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c := by
  obtain ⟨w, -, hw⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hL hx hy
  have e₁ := weilIs_pow_eq hA hL hb hw h₁
  have e₂ := weilIs_pow_eq hA hL ha (by rw [mul_comm]; exact hw) h₂
  rwa [ext_pow hab e₂ e₁] at hw

end Weil

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  intro p _ D R _ b N hN hNp S s o k _ _ _ x β hx ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  obtain ⟨I, hI⟩ := o.geom k x β hx
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull o.isLB _
  have up : ∀ (u : kˣ) (j : ℕ), unitOn (u ^ j) = unitOn u ^ j := fun u j => map_pow _ _ _
  obtain ⟨J, hJ⟩ := exists_gTateIso D (Q := Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c q r => by have := o.act.hom c; exact MonObj.mul_comp _ _ _)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))
    (fun a b q r c ha hb hab hq hr w₁ w₂ => weilIs_of_coprime o.ab hL ha hb hab hq hr
      (by rw [up] at w₁; exact w₁) (by rw [up] at w₂; exact w₂))
    I ζ ev h₁ h₂ h₃ h₄ h₅ h₆ h₇ (fun e y z => by rw [Nat.cast_pow]; exact h₈ e y z)
  exact ⟨J, fun y => (hI y).trans (hJ N (by omega) hNp y).symm⟩

end GlobalTheory.UPel.HT.GTateGlue
