import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TorsionGalois
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open AddSubgroup

section Def

variable (ℓ : ℕ) (A : Type*) [AddCommGroup A]

def TateModule : AddSubgroup (ℕ → A) where
  carrier := {t | (∀ k, ℓ ^ k • t k = 0) ∧ ∀ k, ℓ • t (k + 1) = t k}
  add_mem' {s t} hs ht :=
    ⟨fun k => by simp [nsmul_add, hs.1 k, ht.1 k], fun k => by simp [nsmul_add, hs.2 k, ht.2 k]⟩
  zero_mem' := ⟨fun k => by simp, fun k => by simp⟩
  neg_mem' {t} ht := ⟨fun k => by simp [ht.1 k], fun k => by simp [ht.2 k]⟩

variable {ℓ A}

theorem TateModule.pow_nsmul (t : TateModule ℓ A) (k : ℕ) : ℓ ^ k • (t : ℕ → A) k = 0 :=
  t.2.1 k

theorem TateModule.nsmul_succ (t : TateModule ℓ A) (k : ℕ) :
    ℓ • (t : ℕ → A) (k + 1) = (t : ℕ → A) k :=
  t.2.2 k

theorem nsmul_swap (a b : ℕ) (x : A) : a • b • x = b • a • x := by
  rw [← mul_nsmul', mul_comm, mul_nsmul']

theorem TateModule.pow_nsmul_add (t : TateModule ℓ A) (i j : ℕ) :
    ℓ ^ j • (t : ℕ → A) (i + j) = (t : ℕ → A) i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_nsmul', ← add_assoc, (TateModule.nsmul_succ t), ih]

theorem TateModule.zero_apply (t : TateModule ℓ A) : (t : ℕ → A) 0 = 0 := by
  simpa using (TateModule.pow_nsmul t) 0

end Def

section Module

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

instance neZero_pow_prime (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩

theorem val_nsmul_eq {k : ℕ} {P : A} (hP : ℓ ^ k • P = 0) {x : ZMod (ℓ ^ k)} {N : ℕ}
    (h : (N : ZMod (ℓ ^ k)) = x) : x.val • P = N • P := by
  rw [← h, ZMod.val_natCast, ← nsmul_eq_mod_nsmul N hP]

noncomputable instance TateModule.instSMul : SMul ℤ_[ℓ] (TateModule ℓ A) where
  smul a t := ⟨fun k => (PadicInt.toZModPow k a).val • (t : ℕ → A) k,
    fun k => by rw [nsmul_swap, (TateModule.pow_nsmul t), nsmul_zero],
    fun k => by
      rw [nsmul_swap, (TateModule.nsmul_succ t)]
      exact (val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (by rw [ZMod.natCast_val, PadicInt.cast_toZModPow _ _ (Nat.le_succ k)])).symm⟩

theorem TateModule.smul_apply (a : ℤ_[ℓ]) (t : TateModule ℓ A) (k : ℕ) :
    ((a • t : TateModule ℓ A) : ℕ → A) k = (PadicInt.toZModPow k a).val • (t : ℕ → A) k :=
  rfl

noncomputable instance TateModule.instModule : Module ℤ_[ℓ] (TateModule ℓ A) where
  one_smul t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply, val_nsmul_eq ((TateModule.pow_nsmul t) k) (N := 1) (by simp), one_nsmul]
  mul_smul a b t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply, TateModule.smul_apply, TateModule.smul_apply, ← mul_nsmul',
      val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (N := (PadicInt.toZModPow k a).val * (PadicInt.toZModPow k b).val) (by simp)]
  smul_zero a := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp
  smul_add a s t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp [nsmul_add, TateModule.smul_apply]
  add_smul a b t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp only [AddSubgroup.coe_add, Pi.add_apply, TateModule.smul_apply]
    rw [← add_nsmul, val_nsmul_eq ((TateModule.pow_nsmul t) k)
        (N := (PadicInt.toZModPow k a).val + (PadicInt.toZModPow k b).val) (by simp)]
  zero_smul t := Subtype.ext <| funext fun k => by
    rw [TateModule.smul_apply]
    simp

end Module

section Lift

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

noncomputable def zmodMulHom (m : ℕ) (P : A) (hP : m • P = 0) : ZMod m →+ A :=
  ZMod.lift m ⟨zmultiplesHom A P, by simp [hP]⟩

theorem zmodMulHom_apply {m : ℕ} [NeZero m] (P : A) (hP : m • P = 0) (a : ZMod m) :
    zmodMulHom m P hP a = a.val • P := by
  have h : ((a.val : ℤ) : ZMod m) = a := by simp
  conv_lhs => rw [← h]
  rw [zmodMulHom, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, natCast_zsmul]

variable (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
include hcard

theorem finite_torsion_of_card (k : ℕ) : Finite {P : A // ℓ ^ k • P = 0} :=
  Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (NeZero.ne _))

theorem exists_nsmul_eq_of_card (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) :
    ∃ Q : A, ℓ ^ (k + 1) • Q = 0 ∧ ℓ • Q = P := by
  let D := torsionBy A ((ℓ ^ (k + 1) : ℕ) : ℤ)
  let C := torsionBy A ((ℓ ^ k : ℕ) : ℤ)
  have hD : Nat.card D = (ℓ ^ (k + 1)) ^ 2 := by
    rw [← hcard]; exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff)
  have hC : Nat.card C = (ℓ ^ k) ^ 2 := by
    rw [← hcard]; exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff)
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; exact pow_ne_zero _ (NeZero.ne _))
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; exact pow_ne_zero _ (NeZero.ne _))
  have := finite_torsion_of_card hcard 1
  let ψ : D →+ C :=
    { toFun := fun Q => ⟨ℓ • (Q : A), by
        rw [torsionBy.nsmul_iff, ← mul_nsmul', ← pow_succ, torsionBy.nsmul_iff.mp Q.2]⟩
      map_zero' := Subtype.ext (nsmul_zero ℓ)
      map_add' := fun Q R => Subtype.ext (nsmul_add (Q : A) R ℓ) }
  have hker : Nat.card ψ.ker ≤ (ℓ ^ 1) ^ 2 := by
    rw [← hcard 1]
    refine Nat.card_le_card_of_injective (fun Q => ⟨((Q : D) : A), by
        have h := Q.2
        rw [AddMonoidHom.mem_ker] at h
        rw [pow_one]
        exact congrArg Subtype.val h⟩) ?_
    intro Q R h
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have htot : Nat.card D = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv, mul_comm]
  have hrange : ψ.range = ⊤ := by
    apply AddSubgroup.eq_top_of_le_card
    rw [hC]
    have h1 : (ℓ ^ (k + 1)) ^ 2 ≤ (ℓ ^ 1) ^ 2 * Nat.card ψ.range := by
      rw [← hD, htot]; exact Nat.mul_le_mul_right _ hker
    have h2 : (ℓ ^ (k + 1)) ^ 2 = (ℓ ^ 1) ^ 2 * (ℓ ^ k) ^ 2 := by ring
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos (pow_pos hℓ.out.pos 1) 2)
  obtain ⟨Q, hQ⟩ := AddMonoidHom.range_eq_top.mp hrange ⟨P, torsionBy.nsmul_iff.mpr hP⟩
  exact ⟨Q, torsionBy.nsmul_iff.mp Q.2, congrArg Subtype.val hQ⟩

private noncomputable def rootSeq (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) :
    (m : ℕ) → {Q : A // ℓ ^ (k + m) • Q = 0}
  | 0 => ⟨P, hP⟩
  | m + 1 =>
    ⟨(exists_nsmul_eq_of_card hcard (k + m) _ (rootSeq k P hP m).2).choose,
      (exists_nsmul_eq_of_card hcard (k + m) _ (rootSeq k P hP m).2).choose_spec.1⟩

private theorem rootSeq_spec (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) (m : ℕ) :
    ℓ • (rootSeq hcard k P hP (m + 1)).1 = (rootSeq hcard k P hP m).1 :=
  (exists_nsmul_eq_of_card hcard (k + m) _ (rootSeq hcard k P hP m).2).choose_spec.2

private theorem rootSeq_pow (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) (m : ℕ) :
    ℓ ^ m • (rootSeq hcard k P hP m).1 = P := by
  induction m with
  | zero => simp [rootSeq]
  | succ m ih => rw [pow_succ, mul_nsmul', rootSeq_spec, ih]

theorem exists_tateModule_apply_eq (k : ℕ) (P : A) (hP : ℓ ^ k • P = 0) :
    ∃ t : TateModule ℓ A, (t : ℕ → A) k = P := by
  refine ⟨⟨fun j => ℓ ^ k • (rootSeq hcard k P hP j).1, fun j => ?_, fun j => ?_⟩, ?_⟩
  · show ℓ ^ j • ℓ ^ k • _ = 0
    rw [← mul_nsmul', ← pow_add, add_comm]
    exact (rootSeq hcard k P hP j).2
  · show ℓ • ℓ ^ k • _ = ℓ ^ k • _
    rw [nsmul_swap, rootSeq_spec]
  · exact rootSeq_pow hcard k P hP k

end Lift

section Basis

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

theorem exists_toZModPow_eq (x : ∀ k : ℕ, ZMod (ℓ ^ k))
    (hx : ∀ k, ((x (k + 1)).val : ZMod (ℓ ^ k)) = x k) :
    ∃ a : ℤ_[ℓ], ∀ k, PadicInt.toZModPow k a = x k := by
  have hi : ∀ i, (ℓ : ℤ) ^ i ∣ ((x (i + 1)).val : ℤ) - ((x i).val : ℤ) := by
    intro i
    have h := (ZMod.intCast_eq_intCast_iff_dvd_sub ((x i).val : ℤ) ((x (i + 1)).val : ℤ)
      (ℓ ^ i)).mp (by rw [Int.cast_natCast, Int.cast_natCast, hx i]; simp)
    exact_mod_cast h
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub
    (fun k => ((x k).val : ℤ)) ℓ hi), fun k => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ hi]
  simp

theorem TateModule.dvd_of_nsmul_add_nsmul_eq_zero (t s : TateModule ℓ A)
    (h1 : ∀ a b : ℕ, a • (t : ℕ → A) 1 + b • (s : ℕ → A) 1 = 0 → ℓ ∣ a ∧ ℓ ∣ b) (k : ℕ) :
    ∀ a b : ℕ, a • (t : ℕ → A) k + b • (s : ℕ → A) k = 0 → ℓ ^ k ∣ a ∧ ℓ ^ k ∣ b := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro a b h
    have hk : a • (t : ℕ → A) k + b • (s : ℕ → A) k = 0 := by
      rw [← TateModule.nsmul_succ t k, ← TateModule.nsmul_succ s k, nsmul_swap a ℓ,
        nsmul_swap b ℓ, ← nsmul_add, h, nsmul_zero]
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := ih a b hk
    have h' : a' • (t : ℕ → A) 1 + b' • (s : ℕ → A) 1 = 0 := by
      rw [← TateModule.pow_nsmul_add t 1 k, ← TateModule.pow_nsmul_add s 1 k, add_comm 1 k,
        nsmul_swap a' (ℓ ^ k), nsmul_swap b' (ℓ ^ k), ← mul_nsmul', ← mul_nsmul']
      exact h
    obtain ⟨ha, hb⟩ := h1 a' b' h'
    constructor
    · rw [pow_succ]; exact mul_dvd_mul_left _ ha
    · rw [pow_succ]; exact mul_dvd_mul_left _ hb

theorem TateModule.exists_basis
    (hcard : ∀ k, Nat.card {P : A // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2)
    (hbase : ∃ P Q : A, ℓ • P = 0 ∧ ℓ • Q = 0 ∧ ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ A)) := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := hbase
  obtain ⟨t, ht⟩ := exists_tateModule_apply_eq hcard 1 P (by rwa [pow_one])
  obtain ⟨s, hs⟩ := exists_tateModule_apply_eq hcard 1 Q (by rwa [pow_one])
  have h1 : ∀ a b : ℕ, a • (t : ℕ → A) 1 + b • (s : ℕ → A) 1 = 0 → ℓ ∣ a ∧ ℓ ∣ b := by
    rw [ht, hs]; exact hPQ
  have hind := TateModule.dvd_of_nsmul_add_nsmul_eq_zero t s h1
  let g : ∀ k, ZMod (ℓ ^ k) × ZMod (ℓ ^ k) →+ A := fun k =>
    (zmodMulHom _ _ (TateModule.pow_nsmul t k)).coprod (zmodMulHom _ _ (TateModule.pow_nsmul s k))
  have hg : ∀ k x, g k x = x.1.val • (t : ℕ → A) k + x.2.val • (s : ℕ → A) k := by
    intro k x
    simp [g, zmodMulHom_apply]
  have hginj : ∀ k, Function.Injective (g k) := by
    intro k
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ hxy
    rw [hg] at hxy
    obtain ⟨hx, hy⟩ := hind k _ _ hxy
    have hx0 : x = 0 := by
      rw [← ZMod.val_eq_zero]; exact Nat.eq_zero_of_dvd_of_lt hx (ZMod.val_lt x)
    have hy0 : y = 0 := by
      rw [← ZMod.val_eq_zero]; exact Nat.eq_zero_of_dvd_of_lt hy (ZMod.val_lt y)
    simp [hx0, hy0]
  let Φ : ℤ_[ℓ] × ℤ_[ℓ] →ₗ[ℤ_[ℓ]] TateModule ℓ A :=
    (LinearMap.toSpanSingleton ℤ_[ℓ] _ t).coprod (LinearMap.toSpanSingleton ℤ_[ℓ] _ s)
  have hΦ : ∀ a b k, ((Φ (a, b) : TateModule ℓ A) : ℕ → A) k =
      g k (PadicInt.toZModPow k a, PadicInt.toZModPow k b) := by
    intro a b k
    rw [hg]
    simp [Φ, LinearMap.coprod_apply, TateModule.smul_apply]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hk : ∀ k, PadicInt.toZModPow k a = 0 ∧ PadicInt.toZModPow k b = 0 := by
      intro k
      have h := congrArg (fun u : TateModule ℓ A => (u : ℕ → A) k) hab
      simp only [hΦ, ZeroMemClass.coe_zero, Pi.zero_apply] at h
      have h0 := hginj k (h.trans (map_zero (g k)).symm)
      exact ⟨congrArg Prod.fst h0, congrArg Prod.snd h0⟩
    have ha : a = 0 := PadicInt.ext_of_toZModPow.mp fun k => by rw [(hk k).1, map_zero]
    have hb : b = 0 := PadicInt.ext_of_toZModPow.mp fun k => by rw [(hk k).2, map_zero]
    simp [ha, hb]
  have hsurj : Function.Surjective Φ := by
    intro u
    have hlev : ∀ k, ∃ x : ZMod (ℓ ^ k) × ZMod (ℓ ^ k), g k x = (u : ℕ → A) k := by
      intro k
      have := finite_torsion_of_card hcard k
      let G : ZMod (ℓ ^ k) × ZMod (ℓ ^ k) → {P : A // ℓ ^ k • P = 0} := fun x => ⟨g k x, by
        rw [hg, nsmul_add, nsmul_swap (ℓ ^ k) x.1.val, nsmul_swap (ℓ ^ k) x.2.val,
          TateModule.pow_nsmul t k, TateModule.pow_nsmul s k]
        simp⟩
      have hG : Function.Injective G := fun x y h => hginj k (congrArg Subtype.val h)
      have hGb := hG.bijective_of_nat_card_le (by rw [hcard, Nat.card_prod, Nat.card_zmod, sq])
      obtain ⟨x, hx⟩ := hGb.2 ⟨(u : ℕ → A) k, TateModule.pow_nsmul u k⟩
      exact ⟨x, congrArg Subtype.val hx⟩
    choose x hx using hlev
    have hcompat : ∀ k, (((x (k + 1)).1.val : ZMod (ℓ ^ k)), ((x (k + 1)).2.val : ZMod (ℓ ^ k)))
        = x k := by
      intro k
      apply hginj k
      rw [hx k, hg]
      dsimp only
      rw [val_nsmul_eq (TateModule.pow_nsmul t k) rfl, val_nsmul_eq (TateModule.pow_nsmul s k) rfl,
        ← TateModule.nsmul_succ t k, ← TateModule.nsmul_succ s k, nsmul_swap _ ℓ,
        nsmul_swap _ ℓ, ← nsmul_add, ← hg (k + 1) (x (k + 1)), hx (k + 1),
        TateModule.nsmul_succ u k]
    obtain ⟨a, ha⟩ := exists_toZModPow_eq (fun k => (x k).1) fun k => congrArg Prod.fst (hcompat k)
    obtain ⟨b, hb⟩ := exists_toZModPow_eq (fun k => (x k).2) fun k => congrArg Prod.snd (hcompat k)
    refine ⟨(a, b), Subtype.ext (funext fun k => ?_)⟩
    rw [hΦ, ha, hb]
    exact hx k
  exact ⟨(Module.Basis.finTwoProd ℤ_[ℓ]).map (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩)⟩

end Basis

section Curve

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem card_nsmul_pow_eq_zero (hℓF : (ℓ : F) ≠ 0) (k : ℕ) :
    Nat.card {P : W.toAffine.Point // ℓ ^ k • P = 0} = (ℓ ^ k) ^ 2 := by
  rw [← card_torsionBy W (n := ℓ ^ k) (by push_cast; exact pow_ne_zero _ hℓF)]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => torsionBy.nsmul_iff.symm)

theorem exists_independent_torsion_prime (hℓF : (ℓ : F) ≠ 0) :
    ∃ P Q : W.toAffine.Point, ℓ • P = 0 ∧ ℓ • Q = 0 ∧
      ∀ a b : ℕ, a • P + b • Q = 0 → ℓ ∣ a ∧ ℓ ∣ b := by
  obtain ⟨e⟩ := nonempty_torsionBy_addEquiv W hℓF
  refine ⟨(e.symm (1, 0) : W.toAffine.Point), (e.symm (0, 1) : W.toAffine.Point),
    torsionBy.nsmul_iff.mp (e.symm (1, 0)).2, torsionBy.nsmul_iff.mp (e.symm (0, 1)).2,
    fun a b h => ?_⟩
  have hab : ((a : ZMod ℓ), (b : ZMod ℓ)) =
      a • ((1 : ZMod ℓ), (0 : ZMod ℓ)) + b • ((0 : ZMod ℓ), (1 : ZMod ℓ)) := by
    ext <;> simp
  have h' : e.symm ((a : ZMod ℓ), (b : ZMod ℓ)) = 0 := by
    apply Subtype.ext
    rw [hab, map_add, map_nsmul, map_nsmul]
    simpa using h
  have h'' := congrArg e h'
  rw [AddEquiv.apply_symm_apply, map_zero] at h''
  exact ⟨(ZMod.natCast_eq_zero_iff a ℓ).mp (congrArg Prod.fst h''),
    (ZMod.natCast_eq_zero_iff b ℓ).mp (congrArg Prod.snd h'')⟩

theorem tateModule_basis (hℓF : (ℓ : F) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ W.toAffine.Point)) :=
  TateModule.exists_basis (card_nsmul_pow_eq_zero W ℓ hℓF) (exists_independent_torsion_prime W ℓ hℓF)

theorem tateModule_free (hℓF : (ℓ : F) ≠ 0) : Module.Free ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) :=
  let ⟨b⟩ := tateModule_basis W ℓ hℓF
  Module.Free.of_basis b

theorem finrank_tateModule (hℓF : (ℓ : F) ≠ 0) :
    Module.finrank ℤ_[ℓ] (TateModule ℓ W.toAffine.Point) = 2 := by
  obtain ⟨b⟩ := tateModule_basis W ℓ hℓF
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin]

end Curve

section Topology

variable {ℓ : ℕ} {A : Type*} [AddCommGroup A]

instance TateModule.instTopologicalSpace : TopologicalSpace (TateModule ℓ A) :=
  TopologicalSpace.induced (fun t => (t : ℕ → A)) (@Pi.topologicalSpace ℕ (fun _ => A) fun _ => ⊥)

theorem TateModule.isOpen_setOf_apply_eq (k : ℕ) (a : A) :
    IsOpen {t : TateModule ℓ A | (t : ℕ → A) k = a} := by
  letI : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  have hc : Continuous (fun f : ℕ → A => f k) := continuous_apply k
  exact isOpen_induced (hc.isOpen_preimage {a} (isOpen_discrete {a}))

end Topology

section Action

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]

noncomputable def TateModule.map (f : A →+ A) : TateModule ℓ A →ₗ[ℤ_[ℓ]] TateModule ℓ A where
  toFun t := ⟨fun k => f ((t : ℕ → A) k),
    fun k => by rw [← map_nsmul, TateModule.pow_nsmul t k, map_zero],
    fun k => by rw [← map_nsmul, TateModule.nsmul_succ t k]⟩
  map_add' s t := Subtype.ext (funext fun k => map_add f _ _)
  map_smul' a t := Subtype.ext (funext fun k => map_nsmul f _ _)

theorem TateModule.map_apply (f : A →+ A) (t : TateModule ℓ A) (k : ℕ) :
    ((TateModule.map f t : TateModule ℓ A) : ℕ → A) k = f ((t : ℕ → A) k) :=
  rfl

noncomputable def tateRep {G : Type*} [Monoid G] (φ : G →* AddMonoid.End A) :
    Representation ℤ_[ℓ] G (TateModule ℓ A) where
  toFun g := TateModule.map (φ g)
  map_one' := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    show φ 1 ((t : ℕ → A) k) = (t : ℕ → A) k
    rw [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun t => Subtype.ext <| funext fun k => by
    show φ (g * h) ((t : ℕ → A) k) = φ g (φ h ((t : ℕ → A) k))
    rw [map_mul]
    rfl

theorem tateRep_apply {G : Type*} [Monoid G] (φ : G →* AddMonoid.End A) (g : G)
    (t : TateModule ℓ A) (k : ℕ) :
    ((tateRep φ g t : TateModule ℓ A) : ℕ → A) k = φ g ((t : ℕ → A) k) :=
  rfl

theorem continuous_tateRep {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* AddMonoid.End A) (hφ : ∀ a : A, IsOpen {g : G | φ g a = a}) :
    Continuous (fun p : G × TateModule ℓ A => tateRep φ p.1 p.2) := by
  letI : TopologicalSpace A := ⊥
  have : DiscreteTopology A := ⟨rfl⟩
  apply continuous_induced_rng.2
  apply continuous_pi
  intro k
  rw [continuous_discrete_rng]
  intro a
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g0, t0⟩ hp
  change φ g0 ((t0 : ℕ → A) k) = a at hp
  refine ⟨{p : G × TateModule ℓ A | φ (g0⁻¹ * p.1) ((t0 : ℕ → A) k) = (t0 : ℕ → A) k ∧
      (p.2 : ℕ → A) k = (t0 : ℕ → A) k}, ?_, ?_, ?_⟩
  · rintro ⟨g, t⟩ ⟨hg, ht⟩
    change φ g ((t : ℕ → A) k) = a
    rw [ht, ← hp]
    calc φ g ((t0 : ℕ → A) k) = φ (g0 * (g0⁻¹ * g)) ((t0 : ℕ → A) k) := by
          rw [mul_inv_cancel_left]
      _ = φ g0 (φ (g0⁻¹ * g) ((t0 : ℕ → A) k)) := by rw [map_mul]; rfl
      _ = φ g0 ((t0 : ℕ → A) k) := by rw [hg]
  · exact ((hφ _).preimage (continuous_const.mul continuous_fst)).inter
      ((TateModule.isOpen_setOf_apply_eq k _).preimage continuous_snd)
  · refine ⟨?_, rfl⟩
    show φ (g0⁻¹ * g0) _ = _
    rw [inv_mul_cancel, map_one]
    rfl

end Action

section Galois

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [DecidableEq L] (W : WeierstrassCurve K)
  (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

noncomputable abbrev galTateRep :
    Representation ℤ_[ℓ] Gal(L/K) (TateModule ℓ (W.baseChange L).toAffine.Point) :=
  tateRep (galPointsHom K L W)

theorem continuous_galTateRep [Algebra.IsIntegral K L] :
    Continuous (fun p : Gal(L/K) × TateModule ℓ (W.baseChange L).toAffine.Point =>
      galTateRep K L W ℓ p.1 p.2) :=
  continuous_tateRep _ fun P =>
    isOpen_stabilizer_point W (GroundTheory.ProfCoh.stabilizer (galPointsZ K L W).ρ P) P fun _ h => h

theorem galTateRep_basis [IsSepClosed L] [W.IsElliptic] (hℓK : (ℓ : K) ≠ 0) :
    Nonempty (Module.Basis (Fin 2) ℤ_[ℓ] (TateModule ℓ (W.baseChange L).toAffine.Point)) :=
  tateModule_basis (W.baseChange L) ℓ (by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hℓK)

end Galois

end GroundTheory.Arith.Abelian
