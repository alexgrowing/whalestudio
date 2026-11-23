import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.LevBd

section Abs

variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

theorem sum_xor {M : Type*} [AddCommMonoid M] (r : Bool) (f : Bool → M) :
    ∑ s, f (xor r s) = ∑ s, f s := by
  cases r <;> simp [Fintype.sum_bool, add_comm]

theorem xor_xor_self (r t : Bool) : xor r (xor r t) = t := by cases r <;> cases t <;> rfl

theorem xor_xor_xor (r s t : Bool) : xor r (xor s (xor r t)) = xor s t := by
  cases r <;> cases s <;> cases t <;> rfl

theorem sum_ite_const {κ M : Type*} [AddCommMonoid M] (s : Finset κ) (P : Prop) [Decidable P] (f : κ → M) :
    (∑ i ∈ s, if P then f i else 0) = if P then ∑ i ∈ s, f i else 0 := by
  split_ifs <;> simp

theorem sum_sum_ite_unique {M : Type*} [AddCommMonoid M] (P : Bool → ι → Prop) [∀ t b, Decidable (P t b)]
    (g : Bool → ι → M) (u : Bool) (c : ι) (h : ∀ t b, P t b → t = u ∧ b = c) :
    (∑ t, ∑ b, if P t b then g t b else 0) = if P u c then g u c else 0 := by
  rw [Finset.sum_eq_single u, Finset.sum_eq_single c]
  · intro b _ hb
    exact if_neg fun hP => hb (h _ _ hP).2
  · simp
  · intro t _ ht
    exact Finset.sum_eq_zero fun b _ => if_neg fun hP => ht (h _ _ hP).1
  · simp

def adA (A C : Bool → ι → ι → R) (r : Bool) (p q : ι) : R :=
  ∑ t, ∑ b, C (xor r t) p b * A t q b - ∑ t, ∑ a, C (xor r t) a q * A t a p

def Wf (A C : Bool → ι → ι → R) (s : Bool) (a b : ι) : R :=
  ∑ t, ∑ c, C (xor s t) a c * A t b c

variable {A C : Bool → ι → ι → R} {Sx : ι → ι → Prop} [DecidableRel Sx] {r : Bool} {p q : ι}

theorem comm_mul_C (x y z : R) : (x * y) * z - z * (x * y) = x * (y * z + z * y) - (x * z + z * x) * y := by
  noncomm_ring

theorem comm_mul_A (x y z : R) : (x * y) * z - z * (x * y) = x * (y * z + z * y) - (z * x + x * z) * y := by
  noncomm_ring

theorem ad_C (hcc : ∀ s a b t c d, C s a b * C t c d + C t c d * C s a b = 0)
    (hac : ∀ s a b t c d, A s a b * C t c d + C t c d * A s a b = if s = t ∧ a = c ∧ b = d ∧ Sx a b then 1 else 0)
    (c0 : ∀ s a b, ¬Sx a b → C s a b = 0) (hp : ∀ c, Sx p c ↔ Sx q c) (hq : ∀ a, Sx a p ↔ Sx a q)
    (u : Bool) (a c : ι) :
    adA A C r p q * C u a c - C u a c * adA A C r p q =
      (if q = a then C (xor r u) p c else 0) - (if c = p then C (xor r u) a q else 0) := by
  have h1 : (∑ t, ∑ b, C (xor r t) p b * A t q b) * C u a c - C u a c * (∑ t, ∑ b, C (xor r t) p b * A t q b) =
      if q = a then C (xor r u) p c else 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul_C, hcc, hac, zero_mul, sub_zero,
      mul_ite, mul_one, mul_zero]
    rw [sum_sum_ite_unique _ (fun t b => C (xor r t) p b) u c (fun t b h => ⟨h.1, h.2.2.1⟩)]
    by_cases e : q = a
    · subst e
      by_cases hs : Sx q c
      · simp [hs]
      · simp [hs, c0 _ _ _ (mt (hp c).1 hs)]
    · simp [e]
  have h2 : (∑ t, ∑ b, C (xor r t) b q * A t b p) * C u a c - C u a c * (∑ t, ∑ b, C (xor r t) b q * A t b p) =
      if c = p then C (xor r u) a q else 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul_C, hcc, hac, zero_mul, sub_zero,
      mul_ite, mul_one, mul_zero]
    rw [sum_sum_ite_unique _ (fun t b => C (xor r t) b q) u a (fun t b h => ⟨h.1, h.2.1⟩)]
    by_cases e : c = p
    · subst e
      by_cases hs : Sx a c
      · simp [hs]
      · simp [hs, c0 _ _ _ (mt (hq a).2 hs)]
    · simp [e, Ne.symm e]
  unfold adA
  rw [← h1, ← h2]
  noncomm_ring

theorem ad_A (haa : ∀ s a b t c d, A s a b * A t c d + A t c d * A s a b = 0)
    (hac : ∀ s a b t c d, A s a b * C t c d + C t c d * A s a b = if s = t ∧ a = c ∧ b = d ∧ Sx a b then 1 else 0)
    (a0 : ∀ s a b, ¬Sx a b → A s a b = 0) (hp : ∀ c, Sx p c ↔ Sx q c) (hq : ∀ a, Sx a p ↔ Sx a q)
    (u : Bool) (a c : ι) :
    adA A C r p q * A u a c - A u a c * adA A C r p q =
      (if c = q then A (xor r u) a p else 0) - (if a = p then A (xor r u) q c else 0) := by
  have h1 : (∑ t, ∑ b, C (xor r t) p b * A t q b) * A u a c - A u a c * (∑ t, ∑ b, C (xor r t) p b * A t q b) =
      -(if a = p then A (xor r u) q c else 0) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul_A, haa, hac, mul_zero, zero_sub,
      ite_mul, one_mul, zero_mul, Finset.sum_neg_distrib]
    rw [sum_sum_ite_unique _ (fun t b => A t q b) (xor r u) c
      (fun t b h => ⟨by rw [h.1, xor_xor_self], h.2.2.1.symm⟩)]
    by_cases e : a = p
    · subst e
      by_cases hs : Sx a c
      · simp [hs, xor_xor_self]
      · simp [hs, a0 _ _ _ (mt (hp c).2 hs)]
    · simp [e]
  have h2 : (∑ t, ∑ b, C (xor r t) b q * A t b p) * A u a c - A u a c * (∑ t, ∑ b, C (xor r t) b q * A t b p) =
      -(if c = q then A (xor r u) a p else 0) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul_A, haa, hac, mul_zero, zero_sub,
      ite_mul, one_mul, zero_mul, Finset.sum_neg_distrib]
    rw [sum_sum_ite_unique _ (fun t b => A t b p) (xor r u) a
      (fun t b h => ⟨by rw [h.1, xor_xor_self], h.2.1.symm⟩)]
    by_cases e : c = q
    · subst e
      by_cases hs : Sx a c
      · simp [hs, xor_xor_self]
      · simp [hs, a0 _ _ _ (mt (hq a).1 hs)]
    · simp [e]
  unfold adA
  rw [sub_eq_add_neg (if c = q then _ else _), ← neg_neg (if c = q then A (xor r u) a p else 0), ← h1, ← h2]
  noncomm_ring

theorem comm_mul (D x y : R) : D * (x * y) - (x * y) * D = (D * x - x * D) * y + x * (D * y - y * D) := by
  noncomm_ring

variable {D : R}

theorem comm_alt_ter (hA : ∀ s a b, D * A s a b - A s a b * D =
      (if b = q then A (xor r s) a p else 0) - (if a = p then A (xor r s) q b else 0))
    (hC : ∀ s a b, D * C s a b - C s a b * D =
      (if q = a then C (xor r s) p b else 0) - (if b = p then C (xor r s) a q else 0)) (s : Bool) (a b : ι) :
    D * Wf A C s a b - Wf A C s a b * D =
      (if q = a then Wf A C (xor r s) p b else 0) - (if b = p then Wf A C (xor r s) a q else 0) := by
  unfold Wf
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul, hA, hC]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_ite_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h4 : ∑ x, C (xor s x) a q * A (xor r x) b p = ∑ x, C (xor r (xor s x)) a q * A x b p := by
    rw [← sum_xor r (fun x => C (xor r (xor s x)) a q * A x b p)]
    simp only [xor_xor_xor]
  have h5 : ∑ i, ∑ c, C (xor s i) a c * A (xor r i) q c = ∑ t, ∑ c, C (xor r (xor s t)) a c * A t q c := by
    rw [← sum_xor r (fun t => ∑ c, C (xor r (xor s t)) a c * A t q c)]
    simp only [xor_xor_xor]
  rw [h4, h5]
  simp only [Bool.xor_assoc]
  abel

theorem comm_ZA {Z : Bool → ι → ι → R}
    (hA : ∀ s a b, D * A s a b - A s a b * D =
      (if b = q then A (xor r s) a p else 0) - (if a = p then A (xor r s) q b else 0))
    (hZ : ∀ s a b, D * Z s a b - Z s a b * D =
      (if q = a then Z (xor r s) p b else 0) - (if b = p then Z (xor r s) a q else 0)) :
    D * (∑ s, ∑ a, ∑ b, Z s a b * A s a b) = (∑ s, ∑ a, ∑ b, Z s a b * A s a b) * D := by
  rw [← sub_eq_zero]
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, comm_mul, hA, hZ]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_ite_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h4 : ∑ s, ∑ b, Z s p b * A (xor r s) q b = ∑ s, ∑ b, Z (xor r s) p b * A s q b := by
    rw [← sum_xor r (fun s => ∑ b, Z (xor r s) p b * A s q b)]
    simp only [xor_xor_self]
  have h5 : ∑ s, ∑ b, Z s b q * A (xor r s) b p = ∑ s, ∑ b, Z (xor r s) b q * A s b p := by
    rw [← sum_xor r (fun s => ∑ b, Z (xor r s) b q * A s b p)]
    simp only [xor_xor_self]
  rw [h4, h5]
  abel

theorem comm_bd {Xl : Bool → ι → ι → R}
    (hA : ∀ s a b, D * A s a b - A s a b * D =
      (if b = q then A (xor r s) a p else 0) - (if a = p then A (xor r s) q b else 0))
    (hC : ∀ s a b, D * C s a b - C s a b * D =
      (if q = a then C (xor r s) p b else 0) - (if b = p then C (xor r s) a q else 0))
    (hX : ∀ s a b, D * Xl s a b - Xl s a b * D =
      (if q = a then Xl (xor r s) p b else 0) - (if b = p then Xl (xor r s) a q else 0)) :
    D * (∑ s, ∑ a, ∑ b, (Xl s a b + Wf A C s a b) * A s a b) =
      (∑ s, ∑ a, ∑ b, (Xl s a b + Wf A C s a b) * A s a b) * D := by
  refine comm_ZA hA fun s a b => ?_
  have e : D * (Xl s a b + Wf A C s a b) - (Xl s a b + Wf A C s a b) * D =
      (D * Xl s a b - Xl s a b * D) + (D * Wf A C s a b - Wf A C s a b * D) := by noncomm_ring
  rw [e, hX, comm_alt_ter hA hC]
  split_ifs <;> abel

end Abs

section Conc

open PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)

variable {n : ℕ}

abbrev Sx (lev : Fin n → ℕ) (a b : Fin n) : Prop := a < b ∧ lev a < lev b

theorem sx_iff {lev : Fin n → ℕ} (hlev : Monotone lev) (a b : Fin n) : Sx lev a b ↔ lev a < lev b :=
  ⟨fun h => h.2, fun h => ⟨lt_of_not_ge fun hab => absurd (hlev hab) (not_le.2 h), h⟩⟩

theorem sum_pos {M : Type*} [AddCommMonoid M] (g : Pos n → M) :
    ∑ i, g i = ∑ a, ∑ b, if h : a < b then g ⟨(a, b), h⟩ else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun a b => if h : a < b then g ⟨(a, b), h⟩ else 0)]
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.1 < x.2)
    (fun x _ hx => by by_contra h; exact hx (dif_neg h))]
  rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.1 < x.2) _ (fun x => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.2]

theorem sum_letters {M : Type*} [AddCommMonoid M] (lev : Fin n → ℕ) [∀ l : Lt n, Decidable (inUU lev l)]
    (f : Lt n → M) :
    (∑ l : Lt n, if inUU lev l then f l else 0) =
      ∑ s, ∑ a, ∑ b, if h : Sx lev a b then f (s, ⟨(a, b), h.1⟩) else 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_pos]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : a < b
  · by_cases h2 : lev a < lev b
    · simp [h1, h2, inUU]
    · simp [h1, h2, inUU]
  · simp [h1]

theorem sum_k {M : Type*} [AddCommMonoid M] (u : Bool) {a c : Fin n} (h : a < c) (g : Lt n → M) :
    (∑ k : Lt n, if k.1 = u ∧ k.2.1 = (a, c) then g k else 0) = g (u, ⟨(a, c), h⟩) := by
  rw [Finset.sum_eq_single (u, ⟨(a, c), h⟩)]
  · simp
  · intro k _ hk
    refine if_neg fun hc => hk ?_
    exact Prod.ext hc.1 (Subtype.ext hc.2)
  · simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def aE (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : Sx lev a b then annL (s, ⟨(a, b), h.1⟩) else 0

def cE (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  if h : Sx lev a b then creL (s, ⟨(a, b), h.1⟩) else 0

def xE (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (a b : Fin n) : Module.End ℂ V :=
  if s then pA E1 E2 a b else kA E1 E2 a b

def lE (E1 E2 : Fin n → Fin n → Module.End ℂ V) (s : Bool) (a b : Fin n) : Module.End ℂ (Cq n V) :=
  liftL n (xE E1 E2 s a b)

theorem aE_aE (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) (t : Bool) (c d : Fin n) :
    (aE lev s a b * aE lev t c d + aE lev t c d * aE lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  unfold aE
  by_cases h1 : Sx lev a b
  · by_cases h2 : Sx lev c d
    · rw [dif_pos h1, dif_pos h2]; exact annL_annL _ _
    · simp [h2]
  · simp [h1]

theorem cE_cE (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) (t : Bool) (c d : Fin n) :
    (cE lev s a b * cE lev t c d + cE lev t c d * cE lev s a b : Module.End ℂ (Cq n V)) = 0 := by
  unfold cE
  by_cases h1 : Sx lev a b
  · by_cases h2 : Sx lev c d
    · rw [dif_pos h1, dif_pos h2]; exact creL_creL _ _
    · simp [h2]
  · simp [h1]

theorem aE_cE (lev : Fin n → ℕ) (s : Bool) (a b : Fin n) (t : Bool) (c d : Fin n) :
    (aE lev s a b * cE lev t c d + cE lev t c d * aE lev s a b : Module.End ℂ (Cq n V)) =
      if s = t ∧ a = c ∧ b = d ∧ Sx lev a b then 1 else 0 := by
  unfold aE cE
  by_cases h1 : Sx lev a b
  · by_cases h2 : Sx lev c d
    · rw [dif_pos h1, dif_pos h2, annL_creL]
      by_cases e : s = t ∧ a = c ∧ b = d
      · obtain ⟨rfl, rfl, rfl⟩ := e
        simp [h1]
      · rw [if_neg, if_neg]
        · exact fun h => e ⟨h.1, h.2.1, h.2.2.1⟩
        · intro h
          have h3 := congrArg Prod.fst h
          have h4 := congrArg (fun x : Lt n => x.2.1) h
          simp only [Prod.mk.injEq] at h3 h4
          exact e ⟨h3, h4.1, h4.2⟩
    · rw [dif_neg h2, if_neg]
      · simp
      · rintro ⟨-, rfl, rfl, h⟩
        exact h2 h
  · rw [dif_neg h1, if_neg]
    · simp
    · exact fun h => h1 h.2.2.2

theorem lE_aE (E1 E2 : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (r : Bool) (p q : Fin n) (s : Bool)
    (a b : Fin n) : lE E1 E2 r p q * aE lev s a b = aE lev s a b * lE E1 E2 r p q := by
  unfold aE lE
  by_cases h : Sx lev a b
  · rw [dif_pos h]; exact liftL_annL _ _
  · simp [h]

theorem lE_cE (E1 E2 : Fin n → Fin n → Module.End ℂ V) (lev : Fin n → ℕ) (r : Bool) (p q : Fin n) (s : Bool)
    (a b : Fin n) : lE E1 E2 r p q * cE lev s a b = cE lev s a b * lE E1 E2 r p q := by
  unfold cE lE
  by_cases h : Sx lev a b
  · rw [dif_pos h]; exact liftL_creL _ _
  · simp [h]

theorem xE_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hE : IsPairA E1 E2) (r : Bool) (p q : Fin n) (s : Bool)
    (a b : Fin n) :
    xE E1 E2 r p q * xE E1 E2 s a b - xE E1 E2 s a b * xE E1 E2 r p q =
      (if q = a then xE E1 E2 (xor r s) p b else 0) - (if b = p then xE E1 E2 (xor r s) a q else 0) := by
  have g1 : E1 p q * E1 a b = E1 a b * E1 p q +
      ((if q = a then E1 p b else 0) - (if b = p then E1 a q else 0)) := by
    rw [← (hE.1 p q a b : E1 p q * E1 a b - E1 a b * E1 p q = _)]; abel
  have g2 : E2 p q * E2 a b = E2 a b * E2 p q +
      ((if q = a then E2 p b else 0) - (if b = p then E2 a q else 0)) := by
    rw [← (hE.2.1 p q a b : E2 p q * E2 a b - E2 a b * E2 p q = _)]; abel
  have c1 := hE.2.2 p q a b
  have c2 := hE.2.2 a b p q
  cases r <;> cases s <;> simp only [xE, kA, pA, Bool.false_eq_true, if_false, if_true, Bool.xor_false,
    Bool.false_xor, Bool.xor_true, Bool.not_true, Bool.not_false, Bool.true_xor, LinearMap.add_apply]
  all_goals
    simp only [mul_add, add_mul, mul_sub, sub_mul, c1, ← c2, g1, g2]
  all_goals split_ifs <;> abel

theorem liftL_mul (T U : Module.End ℂ V) :
    (liftL n (T * U) : Module.End ℂ (Cq n V)) = liftL n T * liftL n U := rfl

theorem lE_comm {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hE : IsPairA E1 E2) (r : Bool) (p q : Fin n) (s : Bool)
    (a b : Fin n) :
    lE E1 E2 r p q * lE E1 E2 s a b - lE E1 E2 s a b * lE E1 E2 r p q =
      (if q = a then lE E1 E2 (xor r s) p b else 0) - (if b = p then lE E1 E2 (xor r s) a q else 0) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  have h := congrArg (fun T : Module.End ℂ V => T (x A)) (xE_comm hE r p q s a b)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [lE, LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, liftL_apply, h]
  split_ifs <;> simp [liftL_apply]

theorem row_bracket (lev : Fin n → ℕ) (s : Bool) {a b : Fin n} (h : Sx lev a b) (Y : Module.End ℂ (Cq n V)) :
    (∑ m : Lt n, ∑ k : Lt n, if inUU lev m ∧ b = m.2.1.1 ∧ k.1 = xor s m.1 ∧ k.2.1.1 = a ∧ k.2.1.2 = m.2.1.2 then
        creL k * annL m * Y else 0) = Wf (aE lev) (cE lev) s a b * Y := by
  have h1 : ∀ m : Lt n, (∑ k : Lt n, if inUU lev m ∧ b = m.2.1.1 ∧ k.1 = xor s m.1 ∧ k.2.1.1 = a ∧
        k.2.1.2 = m.2.1.2 then creL k * annL m * Y else 0) =
      if inUU lev m then (if b = m.2.1.1 then cE lev (xor s m.1) a m.2.1.2 * annL m * Y else 0) else 0 := by
    intro m
    by_cases hm : inUU lev m
    · by_cases hb : b = m.2.1.1
      · have hac : Sx lev a m.2.1.2 := ⟨h.1.trans (hb ▸ m.2.2), h.2.trans (hb ▸ hm)⟩
        rw [if_pos hm, if_pos hb]
        have h2 := sum_k (M := Module.End ℂ (Cq n V)) (xor s m.1) hac.1 (fun k => creL k * annL m * Y)
        rw [show cE lev (xor s m.1) a m.2.1.2 = (creL (xor s m.1, ⟨(a, m.2.1.2), hac.1⟩) : Module.End ℂ (Cq n V)) from
          dif_pos hac, ← h2]
        refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
        simp only [hm, hb, true_and, Prod.ext_iff]
      · simp [hb]
    · simp [hm]
  simp only [h1]
  rw [sum_letters]
  unfold Wf
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : Sx lev b c
    · simp [hc, aE]
    · simp [hc, aE]
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : Sx lev b' c
    · simp [hc, Ne.symm hb']
    · simp [hc]
  · simp

theorem ite_inst {M : Type*} {P : Prop} (i j : Decidable P) (x y : M) : @ite _ P i x y = @ite _ P j x y := by
  congr

theorem bdL_eq (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) :
    bdL (inUU lev) E1 E2 =
      ∑ s, ∑ a, ∑ b, (lE E1 E2 s a b + Wf (aE lev) (cE lev) s a b) * aE lev s a b := by
  unfold bdL
  have p1 : (∑ l : Lt n, if inUU lev l then
      (liftL n (xL E1 E2 l) : Module.End ℂ (Cq n V)) * annL l else 0) =
      ∑ s, ∑ a, ∑ b, lE E1 E2 s a b * aE lev s a b := by
    rw [sum_letters]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : Sx lev a b
    · rw [dif_pos h, show aE lev s a b = (annL (s, ⟨(a, b), h.1⟩) : Module.End ℂ (Cq n V)) from dif_pos h]
      rfl
    · rw [dif_neg h, show aE lev s a b = (0 : Module.End ℂ (Cq n V)) from dif_neg h, mul_zero]
  have p2 : (∑ l : Lt n, ∑ m : Lt n, ∑ k : Lt n,
      if inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
        (creL k * annL m * annL l : Module.End ℂ (Cq n V)) else 0) =
      ∑ s, ∑ a, ∑ b, Wf (aE lev) (cE lev) s a b * aE lev s a b := by
    have h1 : ∀ l : Lt n, (∑ m : Lt n, ∑ k : Lt n,
        if inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
          (creL k * annL m * annL l : Module.End ℂ (Cq n V)) else 0) =
        if inUU lev l then (∑ m : Lt n, ∑ k : Lt n,
          if inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2 then
            (creL k * annL m * annL l : Module.End ℂ (Cq n V)) else 0) else 0 := by
      intro l
      by_cases hl : inUU lev l
      · rw [if_pos hl]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
        simp only [hl, true_and]
      · rw [if_neg hl]
        refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun k _ => if_neg fun h => hl h.1
    simp only [h1]
    rw [sum_letters]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h : Sx lev a b
    · rw [dif_pos h, show aE lev s a b = (annL (s, ⟨(a, b), h.1⟩) : Module.End ℂ (Cq n V)) from dif_pos h,
        ← row_bracket lev s h]
    · rw [dif_neg h, show aE lev s a b = (0 : Module.End ℂ (Cq n V)) from dif_neg h, mul_zero]
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [← p1]
    exact Finset.sum_congr rfl fun l _ => ite_inst _ _ _ _
  · rw [← p2]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ =>
      ite_inst _ _ _ _

theorem row_ad {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (r t : Bool) {a b : Fin n}
    (h : Sx lev a b) (Y : Module.End ℂ (Cq n V)) :
    (∑ k : Lt n, adCL r p q (t, ⟨(a, b), h.1⟩) k • (creL k * Y)) =
      (if q = a then cE lev (xor r t) p b * Y else 0) - (if b = p then cE lev (xor r t) a q * Y else 0) := by
  simp only [adCL, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul]
  congr 1
  · by_cases e : q = a
    · subst e
      have hs : Sx lev p b := (sx_iff hlev _ _).2 (hpq ▸ h.2)
      rw [if_pos rfl, show cE lev (xor r t) p b = (creL (xor r t, ⟨(p, b), hs.1⟩) : Module.End ℂ (Cq n V)) from dif_pos hs,
        ← sum_k (M := Module.End ℂ (Cq n V)) (xor r t) hs.1 (fun k => creL k * Y)]
      refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
      simp
    · simp [e]
  · by_cases e : b = p
    · subst e
      have hs : Sx lev a q := (sx_iff hlev _ _).2 (hpq ▸ h.2)
      rw [if_pos rfl, show cE lev (xor r t) a q = (creL (xor r t, ⟨(a, q), hs.1⟩) : Module.End ℂ (Cq n V)) from dif_pos hs,
        ← sum_k (M := Module.End ℂ (Cq n V)) (xor r t) hs.1 (fun k => creL k * Y)]
      refine Finset.sum_congr rfl fun k _ => if_congr ?_ rfl rfl
      simp
    · simp [e]

theorem adLL_eq {lev : Fin n → ℕ} (hlev : Monotone lev) {p q : Fin n} (hpq : lev p = lev q) (r : Bool) :
    (adLL lev r p q : Module.End ℂ (Cq n V)) = adA (aE lev) (cE lev) r p q := by
  unfold adLL adA
  simp only [sum_ite_const]
  rw [sum_letters]
  have h1 : ∀ (t : Bool) (a b : Fin n),
      (if h : Sx lev a b then ∑ k : Lt n, adCL r p q (t, ⟨(a, b), h.1⟩) k •
          (creL k * annL (t, ⟨(a, b), h.1⟩) : Module.End ℂ (Cq n V)) else 0) =
        (if q = a then cE lev (xor r t) p b * aE lev t a b else 0) -
          (if b = p then cE lev (xor r t) a q * aE lev t a b else 0) := by
    intro t a b
    by_cases h : Sx lev a b
    · rw [dif_pos h, row_ad hlev hpq r t h,
        show aE lev t a b = (annL (t, ⟨(a, b), h.1⟩) : Module.End ℂ (Cq n V)) from dif_pos h]
    · rw [dif_neg h, show aE lev t a b = (0 : Module.End ℂ (Cq n V)) from dif_neg h]
      simp
  simp only [h1, Finset.sum_sub_distrib, sum_ite_const, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem D_comm_bd {lev : Fin n → ℕ} (hlev : Monotone lev) {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    (hE : IsPairA E1 E2) {p q : Fin n} (hpq : lev p = lev q) (r : Bool) :
    (lE E1 E2 r p q + adLL lev r p q) * bdL (inUU lev) E1 E2 =
      bdL (inUU lev) E1 E2 * (lE E1 E2 r p q + adLL lev r p q) := by
  have hp : ∀ c, Sx lev p c ↔ Sx lev q c := fun c => by rw [sx_iff hlev, sx_iff hlev, hpq]
  have hq : ∀ a, Sx lev a p ↔ Sx lev a q := fun a => by rw [sx_iff hlev, sx_iff hlev, hpq]
  have a0 : ∀ s a b, ¬Sx lev a b → (aE lev s a b : Module.End ℂ (Cq n V)) = 0 := fun s a b h => dif_neg h
  have c0 : ∀ s a b, ¬Sx lev a b → (cE lev s a b : Module.End ℂ (Cq n V)) = 0 := fun s a b h => dif_neg h
  rw [bdL_eq, adLL_eq hlev hpq]
  refine comm_bd (r := r) (p := p) (q := q) (fun s a b => ?_) (fun s a b => ?_) (fun s a b => ?_)
  · have e := ad_A (r := r) (Sx := Sx lev) (A := aE lev) (C := cE lev) (aE_aE lev) (aE_cE lev) a0 hp hq s a b
    rw [← e, add_mul, mul_add, lE_aE]
    abel
  · have e := ad_C (r := r) (Sx := Sx lev) (A := aE lev) (C := cE lev) (cE_cE lev) (aE_cE lev) c0 hp hq s a b
    rw [← e, add_mul, mul_add, lE_cE]
    abel
  · have hc : Commute (lE E1 E2 s a b) (adA (aE lev) (cE lev) r p q : Module.End ℂ (Cq n V)) := by
      unfold adA
      refine Commute.sub_right (Commute.sum_right _ _ _ fun t _ => Commute.sum_right _ _ _ fun b' _ => ?_)
        (Commute.sum_right _ _ _ fun t _ => Commute.sum_right _ _ _ fun b' _ => ?_)
      · exact Commute.mul_right (lE_cE E1 E2 lev s a b _ _ _) (lE_aE E1 E2 lev s a b _ _ _)
      · exact Commute.mul_right (lE_cE E1 E2 lev s a b _ _ _) (lE_aE E1 E2 lev s a b _ _ _)
    rw [← lE_comm hE, add_mul, mul_add, hc.eq]
    abel

theorem cre_ann_mem {lev : Fin n → ℕ} {j : ℕ} {y : Cq n V} (hy : y ∈ chU lev j) {k l : Lt n} (hk : inUU lev k)
    (hl : inUU lev l) : creL k (annL l y) ∈ chU lev j := by
  constructor
  · intro A hA m hm
    obtain ⟨h1, h2⟩ := creL_ne hA
    obtain ⟨-, h4⟩ := annL_ne h2
    by_cases e : m = k
    · exact e ▸ hk
    · exact hy.1 _ h4 m (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨e, hm⟩))
  · intro A hA
    obtain ⟨h1, h2⟩ := creL_ne hA
    obtain ⟨h3, h4⟩ := annL_ne h2
    have h5 := hy.2 _ h4
    rw [Finset.card_insert_of_notMem h3, Finset.card_erase_of_mem h1] at h5
    have h6 : 0 < A.card := Finset.card_pos.2 ⟨k, h1⟩
    omega

theorem cE_aE_mem {lev : Fin n → ℕ} {j : ℕ} {y : Cq n V} (hy : y ∈ chU lev j) (u : Bool) (a c : Fin n) (t : Bool)
    (b d : Fin n) : cE lev u a c (aE lev t b d y) ∈ chU lev j := by
  unfold cE aE
  by_cases h1 : Sx lev a c
  · by_cases h2 : Sx lev b d
    · rw [dif_pos h1, dif_pos h2]
      exact cre_ann_mem hy h1.2 h2.2
    · simp [h2]
  · simp [h1]

theorem D_mem {lev : Fin n → ℕ} (hlev : Monotone lev) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n}
    (hpq : lev p = lev q) (r : Bool) {j : ℕ} {y : Cq n V} (hy : y ∈ chU lev j) :
    (lE E1 E2 r p q + adLL lev r p q : Module.End ℂ (Cq n V)) y ∈ chU lev j := by
  rw [adLL_eq hlev hpq, LinearMap.add_apply]
  refine add_mem ⟨fun A hA l hl => hy.1 A (fun h => hA ?_) l hl, fun A hA => hy.2 A fun h => hA ?_⟩ ?_
  · simp [lE, liftL_apply, h]
  · simp [lE, liftL_apply, h]
  · unfold adA
    simp only [LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply]
    exact sub_mem (sum_mem fun t _ => sum_mem fun b _ => cE_aE_mem hy _ _ _ _ _ _)
      (sum_mem fun t _ => sum_mem fun b _ => cE_aE_mem hy _ _ _ _ _ _)

theorem evLc_gen (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) {p q : Fin n} (hpq : lev p = lev q)
    (r : Bool) : evLc lev E1 E2 (FreeAlgebra.ι ℂ (r, p, q)) = lE E1 E2 r p q + adLL lev r p q := by
  simp only [evLc, FreeAlgebra.lift_ι_apply, hpq, if_true, lE, xE]

theorem levStab : LevStab := by
  intro n lev hlev V _ _ E1 E2 hE p q hpq x hx
  rw [bdSub, Submodule.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have key : ∀ (r : Bool) (z : Cq n V), evLc lev E1 E2 (FreeAlgebra.ι ℂ (r, p, q)) (bdL (inUU lev) E1 E2 z) =
      bdL (inUU lev) E1 E2 (evLc lev E1 E2 (FreeAlgebra.ι ℂ (r, p, q)) z) := by
    intro r z
    rw [evLc_gen lev E1 E2 hpq]
    exact LinearMap.congr_fun (D_comm_bd hlev hE hpq r) z
  have mem : ∀ r : Bool, evLc lev E1 E2 (FreeAlgebra.ι ℂ (r, p, q)) y ∈ chU lev ((omU lev).card + 1) := by
    intro r
    rw [evLc_gen lev E1 E2 hpq]
    exact D_mem hlev E1 E2 hpq r hy
  constructor
  · refine Submodule.mem_map.2 ⟨(1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) y +
      evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)) y), Submodule.smul_mem _ _ (add_mem (mem _) (mem _)), ?_⟩
    simp only [firstLeviFamily, LinearMap.smul_apply, LinearMap.add_apply, map_smul, map_add, key]
  · refine Submodule.mem_map.2 ⟨(1 / 2 : ℂ) • (evLc lev E1 E2 (FreeAlgebra.ι ℂ (false, p, q)) y -
      evLc lev E1 E2 (FreeAlgebra.ι ℂ (true, p, q)) y), Submodule.smul_mem _ _ (sub_mem (mem _) (mem _)), ?_⟩
    simp only [secondLeviFamily, LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, key]

end Conc

end GlobalTheory.CompanionTheory.LevBd
