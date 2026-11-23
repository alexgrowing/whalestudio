import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial

namespace GlobalTheory.Pst

section Kummer

variable (l : ℕ) [Fact l.Prime]

def lRoot (m : ℕ) : Om l :=
  Nat.rec (motive := fun _ => Om l) (l : Om l)
    (fun _ x => (IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos).choose) m

@[simp] theorem lRoot_zero : lRoot l 0 = (l : Om l) := rfl

theorem lRoot_succ (m : ℕ) : lRoot l (m + 1) ^ l = lRoot l m :=
  (IsAlgClosed.exists_pow_nat_eq (lRoot l m) (Fact.out : l.Prime).pos).choose_spec

theorem lRoot_pow (m : ℕ) : lRoot l m ^ (l ^ m) = (l : Om l) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, lRoot_succ, ih]

theorem lRoot_ne_zero (m : ℕ) : lRoot l m ≠ 0 := by
  intro h0
  have h := lRoot_pow l m
  rw [h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at h
  exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm

variable {l} (P : LocPrime l)

theorem isPrimitiveRoot_zeta (m : ℕ) : IsPrimitiveRoot (P.ζQ m) (l ^ m) := by
  have hp : ∀ k, P.ζQ k ^ l ^ k = 1 := by
    intro k
    induction k with
    | zero => simp [P.ζQ_zero]
    | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  cases m with
  | zero => simp [P.ζQ_zero]
  | succ m =>
    have h := orderOf_eq_prime_pow (x := P.ζQ (m + 1)) (p := l) (n := m)
      (by rw [h1]; exact P.ζQ_one) (hp _)
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

theorem zeta_pow_eq_iff (m a b : ℕ) :
    P.ζQ m ^ a = P.ζQ m ^ b ↔ (a : ZMod (l ^ m)) = (b : ZMod (l ^ m)) := by
  have hz := isPrimitiveRoot_zeta P m
  have hf : IsOfFinOrder (P.ζQ m) := hz.isOfFinOrder (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  rw [hf.pow_eq_pow_iff_modEq, ← hz.eq_orderOf, ZMod.natCast_eq_natCast_iff]

def IsKummer (g : GQ l) (c : ℤ_[l]) : Prop :=
  ∀ m, g (lRoot l m) = P.ζQ m ^ (PadicInt.toZModPow m c).val * lRoot l m

theorem exists_isKummer (g : GQ l) : ∃ c, IsKummer P g c := by
  have hne : ∀ m, NeZero (l ^ m) := fun m => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ m, ∃ a : ℕ, g (lRoot l m) = P.ζQ m ^ a * lRoot l m := by
    intro m
    obtain ⟨a, -, ha⟩ := (isPrimitiveRoot_zeta P m).eq_pow_of_pow_eq_one
      (ξ := g (lRoot l m) / lRoot l m) (by
        rw [div_pow, ← map_pow, lRoot_pow, map_natCast,
          div_self (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)])
    exact ⟨a, by rw [ha, div_mul_cancel₀ _ (lRoot_ne_zero l m)]⟩
  choose a ha using h1
  have hd : ∀ i, (l : ℤ) ^ i ∣ (a (i + 1) : ℤ) - (a i : ℤ) := by
    intro i
    have h2 := congrArg (· ^ l) (ha (i + 1))
    simp only [← map_pow, mul_pow, lRoot_succ] at h2
    rw [← pow_mul, mul_comm (a (i + 1)), pow_mul, P.ζQ_succ, ha i] at h2
    have h3 := (zeta_pow_eq_iff P i _ _).mp (mul_right_cancel₀ (lRoot_ne_zero l i) h2)
    rw [ZMod.natCast_eq_natCast_iff] at h3
    exact_mod_cast h3.dvd
  refine ⟨PadicInt.ofIntSeq (fun i => (a i : ℤ)) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ l hd),
    fun m => ?_⟩
  rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ l hd, ha m]
  congr 1
  rw [zeta_pow_eq_iff]
  simp

theorem IsKummer.unique {P : LocPrime l} {g : GQ l} {c c' : ℤ_[l]} (h : IsKummer P g c)
    (h' : IsKummer P g c') : c = c' := by
  refine PadicInt.ext_of_toZModPow.mp fun m => ?_
  have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h3 := (zeta_pow_eq_iff P m _ _).mp
    (mul_right_cancel₀ (lRoot_ne_zero l m) ((h m).symm.trans (h' m)))
  simpa using h3

def kummer (g : GQ l) : ℤ_[l] := (exists_isKummer P g).choose

theorem isKummer_kummer (g : GQ l) : IsKummer P g (kummer P g) := (exists_isKummer P g).choose_spec

theorem kummer_eq_zero_iff (g : GQ l) : kummer P g = 0 ↔ ∀ m, g (lRoot l m) = lRoot l m := by
  constructor
  · intro h m
    have := isKummer_kummer P g m
    rw [h] at this
    simpa using this
  · intro h
    exact (isKummer_kummer P g).unique fun m => by simpa using h m

@[simp] theorem kummer_one : kummer P 1 = 0 := (kummer_eq_zero_iff P 1).mpr fun _ => rfl

theorem kummer_mul (g h : GQ l) :
    (kummer P (g * h) : ℚ_[l]) = kummer P g + (P.χQ g : ℚ_[l]) * kummer P h := by
  have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
    obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
    have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
    rw [e]
    refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
    exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
  let x : ℤ_[l] := ⟨P.χQ g, hx⟩
  have key : IsKummer P (g * h) (kummer P g + x * kummer P h) := by
    intro m
    have : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨a, ha, hg⟩ := P.χQ_cyc g m (P.ζQ m) (isPrimitiveRoot_zeta P m).pow_eq_one
    have hxa : PadicInt.toZModPow m x = a := by
      rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow m), ← map_sub, ← RingHom.mem_ker,
        PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact ha
    rw [AlgEquiv.mul_apply, isKummer_kummer P h m, map_mul, map_pow, hg, isKummer_kummer P g m,
      ← mul_assoc, ← pow_mul, ← pow_add]
    congr 1
    rw [zeta_pow_eq_iff]
    simp [hxa, add_comm]
  rw [(isKummer_kummer P (g * h)).unique key]
  rfl

theorem exists_kummer_ne_zero : ∃ g, kummer P g ≠ 0 := by
  by_contra hc
  push Not at hc
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l]) (lRoot l 1)).2
    fun g => (kummer_eq_zero_iff P g).mp (hc g) 1
  have h1 : x ^ l = (l : ℚ_[l]) := by
    apply (algebraMap ℚ_[l] (Om l)).injective
    rw [map_pow, hx, lRoot_succ, lRoot_zero, map_natCast]
  have h2 := congrArg Padic.valuation h1
  rw [Padic.valuation_pow, Padic.valuation_p] at h2
  have h3 : (l : ℤ) ∣ 1 := ⟨_, h2.symm⟩
  exact (Fact.out : l.Prime).not_dvd_one (by exact_mod_cast h3)

end Kummer

section Ring

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def botExt (l : ℕ) [Fact l.Prime] : FinExt l := ⟨⊥, inferInstance⟩

theorem mem_GK_botExt (g : GQ l) : g ∈ GK (botExt l) := by
  simp [GK, botExt]

theorem localPrime_galoisAction_periodT (g : GQ l) : P.actQ g P.tB = (P.χQ g : ℚ_[l]) • P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_botExt g⟩
  rwa [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h

theorem localPrime_frobenius_periodT : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD (botExt l)).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h

theorem phiB_actQ (g : GQ l) (b : P.R.B) : P.φB (P.actQ g b) = P.actQ g (P.φB b) := by
  have h := (P.PD (botExt l)).φ_comm ⟨g, mem_GK_botExt g⟩ b
  rwa [P.PD_actB, P.PD_actB, P.PD_φ, P.PD_φ] at h

theorem phiB_injective : Function.Injective P.φB := fun a b hab =>
  (P.PD (botExt l)).φ_inj (by rw [P.PD_φ, P.PD_φ, hab])

theorem isUnit_tB : IsUnit P.tB := P.period_datum_t_eq (botExt l) ▸ (P.PD (botExt l)).t_unit

theorem nontrivial_B : Nontrivial P.R.B := by
  refine ⟨⟨(P.PD (botExt l)).t, 0, fun h0 => (P.PD (botExt l)).not_mem_filtration_two ?_⟩⟩
  rw [h0, map_zero]
  exact zero_mem _

abbrev Bst : Type := Polynomial P.R.B

def stHom (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) : Bst P →ₐ[ℚ_[l]] Bst P :=
  eval₂AlgHom (CAlgHom.comp f) y fun _ => Commute.all _ _

@[simp] theorem stHom_C (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) (b : P.R.B) :
    stHom P f y (C b) = C (f b) := eval₂_C _ _

@[simp] theorem stHom_X (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y : Bst P) : stHom P f y X = y := eval₂_X _ _

theorem stHom_apply (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y p : Bst P) :
    stHom P f y p = (p.map (f : P.R.B →+* P.R.B)).comp y := by
  rw [comp, eval₂_map]; rfl

theorem derivative_stHom (f : P.R.B →ₐ[ℚ_[l]] P.R.B) (y p : Bst P) :
    derivative (stHom P f y p) = derivative y * stHom P f y (derivative p) := by
  rw [stHom_apply, stHom_apply, derivative_comp, derivative_map]

theorem stHom_ext {F G : Bst P →ₐ[ℚ_[l]] Bst P} (hC : ∀ b, F (C b) = G (C b)) (hX : F X = G X) :
    F = G := algHom_ext' (AlgHom.ext hC) hX

def actSt : GQ l →* (Bst P →ₐ[ℚ_[l]] Bst P) where
  toFun g := stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB))
  map_one' := stHom_ext P (fun b => by simp) (by simp)
  map_mul' g h := stHom_ext P (fun b => by simp [AlgHom.mul_apply]) (by
    have e : (P.actQ g : P.R.B →ₐ[ℚ_[l]] P.R.B) P.tB = (P.χQ g : ℚ_[l]) • P.tB := localPrime_galoisAction_periodT P g
    simp only [AlgHom.mul_apply, stHom_X, map_add, stHom_C, map_smul, e,
      kummer_mul, add_smul, smul_smul, add_assoc, mul_comm])

@[simp] theorem actSt_C (g : GQ l) (b : P.R.B) : actSt P g (C b) = C (P.actQ g b) := stHom_C _ _ _ _

@[simp] theorem actSt_X (g : GQ l) : actSt P g X = X + C ((kummer P g : ℚ_[l]) • P.tB) :=
  stHom_X _ _ _

def phiSt : Bst P →ₐ[ℚ_[l]] Bst P := stHom P P.φB ((l : Bst P) * X)

@[simp] theorem phiSt_C (b : P.R.B) : phiSt P (C b) = C (P.φB b) := stHom_C _ _ _ _

@[simp] theorem phiSt_X : phiSt P X = (l : Bst P) * X := stHom_X _ _ _

def monSt : Bst P →ₗ[ℚ_[l]] Bst P := -(derivative.restrictScalars ℚ_[l])

@[simp] theorem monSt_apply (p : Bst P) : monSt P p = -derivative p := rfl

theorem phiSt_actSt (g : GQ l) (p : Bst P) : phiSt P (actSt P g p) = actSt P g (phiSt P p) := by
  have : (phiSt P).comp (actSt P g) = (actSt P g).comp (phiSt P) :=
    stHom_ext P (fun b => by simp [phiB_actQ]) (by
      simp only [AlgHom.comp_apply, actSt_X, phiSt_X, map_add, phiSt_C, map_smul, localPrime_frobenius_periodT, map_mul,
        map_natCast, mul_add]
      rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, map_mul, map_natCast])
  exact AlgHom.congr_fun this p

theorem monSt_actSt (g : GQ l) (p : Bst P) : monSt P (actSt P g p) = actSt P g (monSt P p) := by
  have := derivative_stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p
  simp only [derivative_add, derivative_X, derivative_C, add_zero, one_mul] at this
  rw [monSt_apply, monSt_apply, map_neg]
  exact congrArg Neg.neg this

theorem monSt_phiSt (p : Bst P) : monSt P (phiSt P p) = (l : ℚ_[l]) • phiSt P (monSt P p) := by
  have := derivative_stHom P P.φB ((l : Bst P) * X) p
  simp only [derivative_mul, derivative_natCast, zero_mul, derivative_X, mul_one, zero_add] at this
  rw [monSt_apply, monSt_apply, map_neg, smul_neg, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact congrArg Neg.neg this

theorem monSt_C_mul (b : P.R.B) (p : Bst P) : monSt P (C b * p) = C b * monSt P p := by
  simp

theorem exists_monSt_pow_eq_zero (p : Bst P) : ∃ n : ℕ, (monSt P ^ n) p = 0 := by
  have h : ∀ (n : ℕ) (q : Bst P), (monSt P ^ n) q = (-1) ^ n * derivative^[n] q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro q; rw [pow_succ, Module.End.mul_apply, ih]; simp [pow_succ]
  exact ⟨p.natDegree + 1, by rw [h, iterate_derivative_eq_zero (Nat.lt_succ_self _), mul_zero]⟩

theorem monSt_eq_zero_iff (p : Bst P) : monSt P p = 0 ↔ ∃ b, p = C b := by
  constructor
  · intro h
    have : IsAddTorsionFree P.R.B := ⟨fun n hn a b hab => by
      have h1 : (n : ℚ_[l]) • a = (n : ℚ_[l]) • b := by simpa only [Nat.cast_smul_eq_nsmul] using hab
      exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h1⟩
    rw [monSt_apply, neg_eq_zero] at h
    exact ⟨_, eq_C_of_derivative_eq_zero h⟩
  · rintro ⟨b, rfl⟩; simp

theorem phiSt_injective : Function.Injective (phiSt P) := by
  intro p q hpq
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have e : ∀ r : Bst P, (phiSt P r).comp (C (algebraMap ℚ_[l] P.R.B (l : ℚ_[l])⁻¹) * X) =
      r.map (P.φB : P.R.B →+* P.R.B) := by
    intro r
    rw [phiSt, stHom_apply, comp_assoc, mul_comp, natCast_comp, X_comp, ← mul_assoc, ← map_natCast C,
      ← map_mul, ← map_natCast (algebraMap ℚ_[l] P.R.B), ← map_mul, mul_inv_cancel₀ hl, map_one,
      map_one, one_mul, comp_X]
  exact map_injective (P.φB : P.R.B →+* P.R.B) (phiB_injective P) (by rw [← e, ← e, hpq])

example : monSt P X = -1 := by simp

end Ring

end GlobalTheory.Pst
