import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompPowPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime]

structure SimSys (D : Datum p) (N K : ℕ) where
  g : ℕ → D.La →+ D.La
  u : ℕ → ℕ
  lin : ∀ n, 0 < n → n.Coprime p → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z
  u_cop : ∀ n, 0 < n → n.Coprime p → (u n).Coprime n
  u_tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n]
  surj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, g n y = x + n • z
  inj : ∀ n, 0 < n → n.Coprime p → ∀ x z, g n x = n • z → ∃ w, x = n • w
  sim : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - u n * D.EF x y
  tower : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z
  one : ∀ x, ∃ z, g K x = x + N • z

variable {D : Datum p} {N K : ℕ}

def SimSys.id : SimSys D N K where
  g _ := AddMonoidHom.id _
  u _ := 1
  lin _ _ _ c x := ⟨0, by simp⟩
  u_cop _ _ _ := Nat.coprime_one_left _
  u_tower _ _ _ _ _ := rfl
  surj _ _ _ x := ⟨x, 0, by simp⟩
  inj _ _ _ x z h := ⟨z, h⟩
  sim _ _ _ x y := by simp
  tower _ _ _ _ _ x := ⟨0, by simp⟩
  one x := ⟨0, by simp⟩

def SimSys.comp (s t : SimSys D N K) : SimSys D N K where
  g n := (s.g n).comp (t.g n)
  u n := s.u n * t.u n
  lin n hn hc c x := by
    obtain ⟨z, hz⟩ := t.lin n hn hc c x
    obtain ⟨z', hz'⟩ := s.lin n hn hc c (t.g n x)
    exact ⟨z' + s.g n z, by simp only [AddMonoidHom.comp_apply]; rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩
  u_cop n hn hc := Nat.Coprime.mul (s.u_cop n hn hc) (t.u_cop n hn hc)
  u_tower n m hn hm hc := Nat.ModEq.mul (s.u_tower n m hn hm hc) (t.u_tower n m hn hm hc)
  surj n hn hc x := by
    obtain ⟨y, z, hy⟩ := s.surj n hn hc x
    obtain ⟨y', z', hy'⟩ := t.surj n hn hc y
    exact ⟨y', z + s.g n z', by simp only [AddMonoidHom.comp_apply]; rw [hy', map_add, hy, map_nsmul, smul_add, add_assoc]⟩
  inj n hn hc x z h := by
    obtain ⟨w, hw⟩ := s.inj n hn hc (t.g n x) z h
    exact t.inj n hn hc x w hw
  sim n hn hc x y := by
    have h₁ := s.sim n hn hc (t.g n x) (t.g n y)
    have h₂ := t.sim n hn hc x y
    have e : D.EF ((s.g n).comp (t.g n) x) ((s.g n).comp (t.g n) y) - ((s.u n * t.u n : ℕ) : ℤ) * D.EF x y =
        (D.EF (s.g n (t.g n x)) (s.g n (t.g n y)) - s.u n * D.EF (t.g n x) (t.g n y)) +
        s.u n * (D.EF (t.g n x) (t.g n y) - t.u n * D.EF x y) := by
      simp only [AddMonoidHom.comp_apply]; push_cast; ring
    rw [e]
    exact dvd_add h₁ (dvd_mul_of_dvd_right h₂ _)
  tower n m hn hm hc x := by
    obtain ⟨z, hz⟩ := t.tower n m hn hm hc x
    obtain ⟨z', hz'⟩ := s.tower n m hn hm hc (t.g n x)
    exact ⟨z' + s.g (n * m) z, by
      simp only [AddMonoidHom.comp_apply]
      rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩
  one x := by
    obtain ⟨z, hz⟩ := t.one x
    obtain ⟨z', hz'⟩ := s.one x
    exact ⟨z' + s.g K z, by
      simp only [AddMonoidHom.comp_apply]
      rw [hz, map_add, hz', map_nsmul, smul_add, add_assoc]⟩

section Tate

variable {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem TateIsoO.ev_nsmul_self (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (z : D.La) :
    I.ev n (n • z) = 1 :=
  (I.ker n hn hc _).2 ⟨z, rfl⟩

theorem TateIsoO.ev_add_nsmul (I : TateIsoO D k Q act e) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p) (x z : D.La) :
    I.ev n (x + n • z) = I.ev n x := by
  rw [I.add, I.ev_nsmul_self hn hc, _root_.mul_one]

theorem pow_eq_pow_of_modEq_sim {M : Type} [Monoid M] {x : M} {n a b : ℕ} (h : x ^ n = 1) (hab : a ≡ b [MOD n]) :
    x ^ a = x ^ b := by
  rw [← Nat.mod_add_div a n, ← Nat.mod_add_div b n, pow_add, pow_add, pow_mul, pow_mul, h, one_pow, one_pow,
    show a % n = b % n from hab]

def TateIsoO.resim (I : TateIsoO D k Q act e) (t : SimSys D N K) : TateIsoO D k Q act e where
  ζ n := I.ζ n ^ t.u n
  ζ_prim n hn hc := (I.ζ_prim n hn hc).pow_of_coprime _ (t.u_cop n hn hc)
  ζ_pow n m hn hm hc := by
    have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hc
    rw [← pow_mul, mul_comm (t.u _) m, pow_mul, I.ζ_pow n m hn hm hc]
    exact pow_eq_pow_of_modEq_sim ((I.ζ_prim n hn hnc).pow_eq_one) (t.u_tower n m hn hm hc)
  ev n y := if 0 < n ∧ n.Coprime p then I.ev n (t.g n y) else I.ev n y
  add n x y := by
    split_ifs
    · rw [map_add, I.add]
    · exact I.add _ _ _
  lin n c x := by
    split_ifs with h
    · obtain ⟨z, hz⟩ := t.lin n h.1 h.2 c x
      rw [hz, I.ev_add_nsmul h.1 h.2, I.lin]
    · exact I.lin _ _ _
  ker n hn hc x := by
    rw [if_pos ⟨hn, hc⟩, I.ker n hn hc]
    constructor
    · rintro ⟨y, hy⟩
      exact t.inj n hn hc x y hy
    · rintro ⟨w, rfl⟩
      exact ⟨t.g n w, map_nsmul _ _ _⟩
  onto n hn hc q := by
    rw [I.onto n hn hc q]
    simp only [if_pos (And.intro hn hc)]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, z, hy⟩ := t.surj n hn hc x
      exact ⟨y, by rw [hy, I.ev_add_nsmul hn hc, hx]⟩
    · rintro ⟨x, hx⟩
      exact ⟨t.g n x, hx⟩
  tower n m hn hm hc x := by
    have hnc : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hc
    rw [if_pos ⟨Nat.mul_pos hn hm, hc⟩, if_pos ⟨hn, hnc⟩, I.tower n m hn hm hc]
    obtain ⟨z, hz⟩ := t.tower n m hn hm hc x
    rw [hz, I.ev_add_nsmul hn hnc]
  isom n hn hc x y := by
    rw [if_pos ⟨hn, hc⟩, if_pos ⟨hn, hc⟩]
    have h := I.isom n hn hc (t.g n x) (t.g n y)
    have h1 : (I.ζ n) ^ n = 1 := (I.ζ_prim n hn hc).pow_eq_one
    have e' : (I.ζ n ^ t.u n) ^ (2 * D.EF x y) = I.ζ n ^ (2 * D.EF (t.g n x) (t.g n y)) := by
      rw [← zpow_natCast, ← zpow_mul, zpow_eq_zpow_emod' _ h1, zpow_eq_zpow_emod' (2 * D.EF (t.g n x) (t.g n y)) h1]
      congr 1
      obtain ⟨c, hc'⟩ := t.sim n hn hc x y
      refine Int.ModEq.eq (Int.modEq_of_dvd ⟨2 * c, ?_⟩)
      linear_combination 2 * hc'
    rw [e']
    exact h

theorem TateIsoO.resim_ev (I : TateIsoO D k Q act e) (t : SimSys D N K) {n : ℕ} (hn : 0 < n) (hc : n.Coprime p)
    (y : D.La) : (I.resim t).ev n y = I.ev n (t.g n y) := if_pos ⟨hn, hc⟩

end Tate

variable {R : Type} [CommRing R]

theorem Obj.eta_add_nsmul {b : Base D R} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b K s) (x z : D.La) :
    o.eta (x + K • z) = o.eta x := by
  rw [o.eta_add, o.eta_ker, _root_.mul_one]

def Obj.resim {b : Base D R} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b K s) (hK : 0 < K) (hKp : K.Coprime p)
    (t : SimSys D N K) : Obj b K s :=
  { o with
    eta := fun y => o.eta (t.g K y)
    eta_add := fun x y => by rw [map_add]; exact o.eta_add _ _
    eta_lin := fun c x => by
      obtain ⟨z, hz⟩ := t.lin K hK hKp c x
      rw [hz, o.eta_add_nsmul]; exact o.eta_lin _ _
    eta_ker := fun x => by rw [map_nsmul]; exact o.eta_ker _
    geom := fun k _ _ x β hx => by
      obtain ⟨I, hI⟩ := o.geom k x β hx
      exact ⟨I.resim t, fun y => by rw [I.resim_ev t hK hKp]; exact hI _⟩ }

theorem Obj.resim_eta {b : Base D R} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b K s) (hK : 0 < K)
    (hKp : K.Coprime p) (t : SimSys D N K) (y : D.La) : (o.resim hK hKp t).eta y = o.eta (t.g K y) := rfl

def ObjMap.resim {b : Base D R} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b K s'}
    {o : Obj b K s} {f : S' ⟶ S} (hK : 0 < K) (hKp : K.Coprime p) (t : SimSys D N K) (m : ObjMap o' o f) :
    ObjMap (o'.resim hK hKp t) (o.resim hK hKp t) f :=
  { m with eta := fun y => m.eta (t.g K y) }

variable (D K) in

def multSub : AddSubgroup D.La where
  carrier := {x | ∃ z, x = K • z}
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨c, rfl⟩
    exact ⟨a + c, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (smul_zero _).symm⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, (smul_neg _ _).symm⟩

variable (D K) in

abbrev LQ := D.La ⧸ multSub D K

theorem LQ.mk_eq_mk {x y : D.La} : (QuotientAddGroup.mk x : LQ D K) = QuotientAddGroup.mk y ↔ ∃ z, x = y + K • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨-z, by rw [smul_neg, ← hz]; abel⟩
  · rintro ⟨z, rfl⟩
    exact ⟨-z, by rw [smul_neg]; abel⟩

theorem LQ.finite (hK : 0 < K) : Finite (LQ D K) := by
  have := D.finLa
  have : Module.Finite ℤ (LQ D K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' (multSub D K)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  refine Module.finite_of_fg_torsion _ fun x => ?_
  refine ⟨⟨(K : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hK.ne')⟩, ?_⟩
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    show ((K : ℤ)) • (QuotientAddGroup.mk y : LQ D K) = 0
    rw [natCast_zsmul, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩

theorem LQ.finite_aut (hK : 0 < K) : Finite (Equiv.Perm (LQ D K)) := by
  have := LQ.finite (D := D) hK
  infer_instance

def SimSys.Lifts (t : SimSys D N K) (a : Equiv.Perm (LQ D K)) : Prop :=
  ∀ y, a (QuotientAddGroup.mk y) = QuotientAddGroup.mk (t.g K y)

theorem SimSys.lifts_one : (SimSys.id : SimSys D N K).Lifts 1 := fun _ => rfl

theorem SimSys.Lifts.comp {s t : SimSys D N K} {a c : Equiv.Perm (LQ D K)} (hs : s.Lifts a) (ht : t.Lifts c) :
    (s.comp t).Lifts (a * c) := fun y => by rw [Equiv.Perm.mul_apply, ht, hs]; rfl

variable (D N K) in

def levelGrp : Subgroup (Equiv.Perm (LQ D K)) where
  carrier := {a | (∃ t : SimSys D N K, t.Lifts a) ∧ ∃ t : SimSys D N K, t.Lifts a⁻¹}
  one_mem' := ⟨⟨SimSys.id, SimSys.lifts_one⟩, ⟨SimSys.id, by rw [inv_one]; exact SimSys.lifts_one⟩⟩
  mul_mem' := by
    rintro a c ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩ ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
    exact ⟨⟨s.comp t, hs.comp ht⟩, ⟨t'.comp s', by rw [mul_inv_rev]; exact ht'.comp hs'⟩⟩
  inv_mem' := by
    rintro a ⟨h₁, h₂⟩
    exact ⟨h₂, by rw [inv_inv]; exact h₁⟩

theorem mem_levelGrp {a : Equiv.Perm (LQ D K)} :
    a ∈ levelGrp D N K ↔ (∃ t : SimSys D N K, t.Lifts a) ∧ ∃ t : SimSys D N K, t.Lifts a⁻¹ := Iff.rfl

theorem mem_levelGrp_of_lifts (hK : 0 < K) {a : Equiv.Perm (LQ D K)} {t : SimSys D N K} (ht : t.Lifts a) :
    a ∈ levelGrp D N K := by
  refine ⟨⟨t, ht⟩, ?_⟩
  have hpow : ∀ j : ℕ, ∃ s : SimSys D N K, s.Lifts (a ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨SimSys.id, SimSys.lifts_one⟩
    | succ j ih =>
      obtain ⟨s, hs⟩ := ih
      rw [pow_succ]
      exact ⟨s.comp t, hs.comp ht⟩
  have := LQ.finite_aut (D := D) hK
  have ho := (isOfFinOrder_of_finite a).orderOf_pos
  have e : a⁻¹ = a ^ (orderOf a - 1) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel ho, pow_orderOf_eq_one]
  rw [e]
  exact hpow _

theorem levelGrp.finite (hK : 0 < K) : Finite (levelGrp D N K) := by
  have := LQ.finite_aut (D := D) hK
  infer_instance

def levelGrp.sys (a : levelGrp D N K) : SimSys D N K := Classical.choose (mem_levelGrp.1 a.2).1

theorem levelGrp.sys_lifts (a : levelGrp D N K) : (levelGrp.sys a).Lifts a :=
  Classical.choose_spec (mem_levelGrp.1 a.2).1

theorem Obj.eta_congr {b : Base D R} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b K s) {x y : D.La}
    (h : (QuotientAddGroup.mk x : LQ D K) = QuotientAddGroup.mk y) : o.eta x = o.eta y := by
  obtain ⟨z, rfl⟩ := LQ.mk_eq_mk.1 h
  exact o.eta_add_nsmul _ _

def ObjMap.congrLift {b : Base D R} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b K s'}
    {o : Obj b K s} {f : S' ⟶ S} (hK : 0 < K) (hKp : K.Coprime p) {t t' : SimSys D N K}
    {a : Equiv.Perm (LQ D K)} (ht : t.Lifts a) (ht' : t'.Lifts a) (m : ObjMap (o'.resim hK hKp t) o f) :
    ObjMap (o'.resim hK hKp t') o f :=
  { m with
    eta := fun y => by
      have h := m.eta y
      rwa [Obj.resim_eta, o'.eta_congr (show (QuotientAddGroup.mk (t.g K y) : LQ D K) =
        QuotientAddGroup.mk (t'.g K y) by rw [← ht, ← ht'])] at h }

def relMap {b : Base D R} (hK : 0 < K) (hKp : K.Coprime p) (F : RepFam b K) (a : levelGrp D N K) : F.X ⟶ F.X :=
  Classical.choose (F.rep F.X F.s (F.univ.resim hK hKp (levelGrp.sys a))).exists

theorem relMap_spec {b : Base D R} (hK : 0 < K) (hKp : K.Coprime p) (F : RepFam b K) (a : levelGrp D N K) :
    relMap hK hKp F a ≫ F.s = F.s ∧
      Nonempty (ObjMap (F.univ.resim hK hKp (levelGrp.sys a)) F.univ (relMap hK hKp F a)) :=
  Classical.choose_spec (F.rep F.X F.s (F.univ.resim hK hKp (levelGrp.sys a))).exists

theorem relMap_eq {b : Base D R} (hK : 0 < K) (hKp : K.Coprime p) (F : RepFam b K) (a : levelGrp D N K)
    (t : SimSys D N K) (ht : t.Lifts a) (f : F.X ⟶ F.X) (hf : f ≫ F.s = F.s)
    (m : ObjMap (F.univ.resim hK hKp t) F.univ f) : f = relMap hK hKp F a :=
  (F.rep F.X F.s (F.univ.resim hK hKp (levelGrp.sys a))).unique
    ⟨hf, ⟨m.congrLift hK hKp ht (levelGrp.sys_lifts a)⟩⟩ (relMap_spec hK hKp F a)

theorem relMap_one {b : Base D R} (hK : 0 < K) (hKp : K.Coprime p) (F : RepFam b K) :
    relMap hK hKp F (1 : levelGrp D N K) = 𝟙 _ :=
  (relMap_eq hK hKp F 1 SimSys.id SimSys.lifts_one (𝟙 _) (by simp)
    (Classical.choice (RepFamModel.objMap_refl F.univ))).symm

theorem relMap_mul {b : Base D R} (hK : 0 < K) (hKp : K.Coprime p) (F : RepFam b K) (a c : levelGrp D N K) :
    relMap hK hKp F (a * c) = relMap hK hKp F a ≫ relMap hK hKp F c := by
  obtain ⟨ha, ⟨ma⟩⟩ := relMap_spec hK hKp F a
  obtain ⟨hc, ⟨mc⟩⟩ := relMap_spec hK hKp F c
  exact (relMap_eq hK hKp F (a * c) ((levelGrp.sys a).comp (levelGrp.sys c))
    ((levelGrp.sys_lifts a).comp (levelGrp.sys_lifts c)) _ (by rw [Category.assoc, hc, ha])
    (MapComp.comp (ma.resim hK hKp (levelGrp.sys c)) mc)).symm

theorem relMap_lower {b : Base D R} {M₁ : ℕ} (hN : 0 < N) (hM : 0 < M₁) (hc : (N * M₁).Coprime p)
    (F : RepFam b (N * M₁)) (a : levelGrp D N (N * M₁)) :
    Nonempty (ObjMap (F.univ.lower hN hM hc) (F.univ.lower hN hM hc) (relMap (Nat.mul_pos hN hM) hc F a)) := by
  obtain ⟨-, ⟨m⟩⟩ := relMap_spec (Nat.mul_pos hN hM) hc F a
  refine ⟨{ m with eta := fun y => ?_ }⟩
  obtain ⟨z, hz⟩ := (levelGrp.sys a).one y
  have e : F.univ.eta ((levelGrp.sys a).g (N * M₁) (M₁ • y)) = F.univ.eta (M₁ • y) := by
    refine F.univ.eta_congr (LQ.mk_eq_mk.2 ⟨z, ?_⟩)
    rw [map_nsmul, hz, smul_add, smul_smul, Nat.mul_comm M₁ N]
  have h := m.eta (M₁ • y)
  rw [Obj.resim_eta, e] at h
  exact h

end GlobalTheory.UPel.HT
