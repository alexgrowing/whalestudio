import Formalism.HermitianCurvature.StatementQr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem core {A ι : Type*} [Ring A] [Fintype ι] (y η : ι → A) (C : A) (m1 m0 mm : ι → ι → A)
    (n0 nm : ι → ι → ι → ι → A)
    (hyη : ∀ a b, y a * η b = η b * y a)
    (J : ∀ i q l p, m1 i l * m0 q p - m1 q l * m0 i p = C * n0 i q l p)
    (DV : ∀ j, C * y j = y j * C - ∑ l, y l * m1 j l)
    (MC : ∀ q p i, m0 q p * η i - η i * m0 q p = ∑ a, n0 a q i p * η a)
    (BaseTypeSubspacesMapOntoBothSides : ∀ j, ∑ i, η i * mm i j = ∑ i, m0 i j * η i)
    (PairingFactorsThroughPeriods : ∀ j, ∑ i, η i * m0 i j = ∑ i, m1 i j * η i)
    (L3 : ∀ q c p, ∑ a, η a * nm a q c p = ∑ a, n0 a q c p * η a) (q p : ι) :
    C * (∑ a, ∑ c, η a * y c * nm a q c p) + (∑ j, y j * m1 q j) * (∑ i, η i * mm i p) =
      (∑ i, ∑ j, η i * y j * m0 i j) * m0 q p := by
  have h1 : ∑ a, ∑ c, η a * y c * nm a q c p = ∑ c, y c * ∑ a, n0 a q c p * η a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← L3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hyη, mul_assoc]
  have h2 : ∑ i, ∑ j, η i * y j * m0 i j = ∑ j, y j * ∑ i, m1 i j * η i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← PairingFactorsThroughPeriods, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hyη, mul_assoc]
  rw [h1, h2, BaseTypeSubspacesMapOntoBothSides]
  have e1 : C * ∑ c, y c * ∑ a, n0 a q c p * η a =
      ∑ l, y l * (C * ∑ a, n0 a q l p * η a) - ∑ l, y l * ∑ c, m1 c l * ∑ a, n0 a q c p * η a := by
    rw [Finset.mul_sum]
    have : ∀ c, C * (y c * ∑ a, n0 a q c p * η a) =
        y c * (C * ∑ a, n0 a q c p * η a) - ∑ l, y l * (m1 c l * ∑ a, n0 a q c p * η a) := by
      intro c
      rw [← mul_assoc, DV, sub_mul, Finset.sum_mul, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_assoc]
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  have e2 : (∑ j, y j * ∑ i, m1 i j * η i) * m0 q p =
      ∑ l, y l * (∑ i, m1 i l * (m0 q p * η i)) - ∑ l, y l * ∑ c, m1 c l * ∑ a, n0 a q c p * η a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, Finset.sum_mul, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_sub, ← MC, sub_sub_cancel]
  rw [e1, e2, sub_add_eq_add_sub]
  congr 1
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← add_mul, ← J, sub_add_cancel]

theorem asym_sum {B : Type*} [AddCommGroup B] {t : ℕ} (T : Fin t → Fin t → Fin t → Fin t → B) :
    ∑ i, ∑ i', (if i < i' then T i i' i i' - T i' i i i' else 0) =
      ∑ a, ∑ b, if a = b then 0 else eps a b • T a b (min a b) (max a b) := by
  have h : ∀ a b : Fin t, (if a = b then 0 else eps a b • T a b (min a b) (max a b)) =
      (if a < b then T a b a b else 0) - (if b < a then T a b b a else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have h' : a.val < b.val := h
      rw [if_neg h.ne, if_pos h, if_neg (not_lt.2 h.le), min_eq_left h.le, max_eq_right h.le, eps, if_pos h', one_smul,
        sub_zero]
    · subst h
      simp
    · have h' : ¬ a.val < b.val := not_lt.2 (le_of_lt h)
      rw [if_neg h.ne', if_neg (not_lt.2 h.le), if_pos h, min_eq_right h.le, max_eq_left h.le, eps, if_neg h', neg_smul,
        one_smul, zero_sub]
  simp_rw [h]
  simp_rw [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if b < a then T a b b a else 0), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  split_ifs <;> simp

def mS {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (i j : Fin t) (w : ℂ) : A :=
  ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • qminor E (skip1 i) (skip1 j) w

def nS {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (a q c p : Fin t) (w : ℂ) : A :=
  if a = q ∨ c = p then 0 else
    (((eps a q : ℤ) : ℂ) * ((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((a : ℕ) + (q : ℕ) + (c : ℕ) + (p : ℕ))) •
      qminor E (skip2 (min a q) (max a q)) (skip2 (min c p) (max c p)) w

theorem cast_mul_eq_smul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (a : A) : ((z : ℤ) : A) * a = ((z : ℤ) : ℂ) • a := by
  rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]

theorem zsmul_eq_csmul {A : Type*} [Ring A] [Algebra ℂ A] (z : ℤ) (a : A) : z • a = ((z : ℤ) : ℂ) • a := by
  rw [Int.cast_smul_eq_zsmul]

theorem min_add_max {t : ℕ} (a b : Fin t) : ((min a b : Fin t) : ℕ) + ((max a b : Fin t) : ℕ) = (a : ℕ) + (b : ℕ) := by
  rw [Fin.coe_min, Fin.coe_max]; omega

section Conv

variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

theorem chY_eq (w : ℂ) (y : Fin t → A) (ξ : Fin t → ℂ) :
    chY E w y ξ = ∑ q, ξ q • ∑ j, y j * mS E q j w := by
  unfold chY mS
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_smul, mul_comm]

theorem chX_eq (w : ℂ) (x : Fin t → ℂ) (η : Fin t → A) :
    chX E w x η = ∑ p, x p • ∑ i, η i * mS E i p w := by
  unfold chX mS
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, smul_smul, mul_comm]

theorem chYY_eq (w : ℂ) (y η : Fin t → A) :
    chYY E w y η = ∑ i, ∑ j, η i * y j * mS E i j w := by
  unfold chYY mS
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm]

theorem chatA_eq (w : ℂ) (x ξ : Fin t → ℂ) :
    chatA E w x ξ = ∑ q, ∑ p, (ξ q * x p) • mS E q p w := by
  unfold chatA mS
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  congr 1
  ring

theorem secondChern_eq_double_sum (w : ℂ) (y : Fin t → A) (x : Fin t → ℂ) (η : Fin t → A) (ξ : Fin t → ℂ) :
    ch2 E w y x η ξ = ∑ q, ∑ p, (ξ q * x p) • ∑ a, ∑ c, η a * y c * nS E a q c p w := by
  set U : Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → Fin t → A := fun a b c d i i' j j' =>
    ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
      ((ξ b • η a) * (x d • y c) * qminor E (skip2 i i') (skip2 j j') w) with hU
  have s1 : ch2 E w y x η ξ = ∑ i, ∑ i', (if i < i' then
      (∑ j, ∑ j', if j < j' then U i i' j j' i i' j j' - U i i' j' j i i' j j' else 0) -
      (∑ j, ∑ j', if j < j' then U i' i j j' i i' j j' - U i' i j' j i i' j j' else 0) else 0) := by
    unfold ch2
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases h : i < i'
    · rw [if_pos h, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      by_cases h' : j < j'
      · rw [if_pos ⟨h, h'⟩, if_pos h', if_pos h']
        simp only [hU, sub_mul, mul_sub, smul_sub]
        abel
      · rw [if_neg (fun hh => h' hh.2), if_neg h', if_neg h', sub_zero]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      rw [if_neg (fun hh => h hh.1)]
  rw [s1, asym_sum (fun a b i i' => ∑ j, ∑ j', if j < j' then U a b j j' i i' j j' - U a b j' j i i' j j' else 0)]
  have s2 : ∀ a b i i', (∑ j, ∑ j', if j < j' then U a b j j' i i' j j' - U a b j' j i i' j j' else 0) =
      ∑ c, ∑ d, if c = d then 0 else eps c d • U a b c d i i' (min c d) (max c d) := fun a b i i' =>
    asym_sum (fun c d j j' => U a b c d i i' j j')
  simp_rw [s2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have s3 : ∀ a : Fin t, (if a = b then (0 : A) else eps a b • ∑ c, ∑ d, if c = d then 0 else
      eps c d • U a b c d (min a b) (max a b) (min c d) (max c d)) =
      ∑ d, ∑ c, (ξ b * x d) • (η a * y c * nS E a b c d w) := by
    intro a
    rw [Finset.sum_comm]
    by_cases hab : a = b
    · rw [if_pos hab]
      symm
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun j' _ => ?_
      rw [nS, if_pos (Or.inl hab), mul_zero, smul_zero]
    · rw [if_neg hab, Finset.smul_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hcd : c = d
      · rw [if_pos hcd, nS, if_pos (Or.inr hcd), mul_zero, smul_zero, smul_zero]
      · rw [if_neg hcd, nS, if_neg (by tauto)]
        simp only [hU]
        rw [show ((min a b : Fin t) : ℕ) + ((max a b : Fin t) : ℕ) + ((min c d : Fin t) : ℕ) + ((max c d : Fin t) : ℕ) =
          (a : ℕ) + (b : ℕ) + (c : ℕ) + (d : ℕ) by
            have h1 := min_add_max a b
            have h2 := min_add_max c d
            omega]
        simp only [zsmul_eq_csmul, smul_mul_assoc, mul_smul_comm, smul_smul]
        congr 1
        ring
  rw [Finset.sum_congr rfl fun a _ => s3 a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]

end Conv

section Red

variable {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

def Core (y η : Fin t → A) (u : ℂ) (p q : Fin t) : Prop :=
  qdet E (u + 1) * (∑ a, ∑ c, η a * y c * nS E a q c p (u - 1)) +
      (∑ j, y j * mS E q j (u + 1)) * (∑ i, η i * mS E i p (u - 1)) =
    (∑ i, ∑ j, η i * y j * mS E i j u) * mS E q p u

theorem single_sum (q : Fin t) (F : Fin t → A) : ∑ q', (Pi.single q (1 : ℂ) : Fin t → ℂ) q' • F q' = F q := by
  simp [Pi.single_apply]

theorem sum_single_single_smul (q p : Fin t) (F : Fin t → Fin t → A) :
    ∑ q', ∑ p', ((Pi.single q (1 : ℂ) : Fin t → ℂ) q' * (Pi.single p (1 : ℂ) : Fin t → ℂ) p') • F q' p' = F q p := by
  simp_rw [mul_smul, ← Finset.smul_sum, single_sum]

theorem basis_iff_core (y η : Fin t → A) (u : ℂ) (p q : Fin t) :
    (qdet E (u + 1) * ch2 E (u - 1) y (Pi.single p 1) η (Pi.single q 1) +
          chY E (u + 1) y (Pi.single q 1) * chX E (u - 1) (Pi.single p 1) η =
        chYY E u y η * chatA E u (Pi.single p 1) (Pi.single q 1)) ↔ Core E y η u p q := by
  rw [secondChern_eq_double_sum, chY_eq, chX_eq, chYY_eq, chatA_eq, sum_single_single_smul, single_sum, single_sum, sum_single_single_smul]
  exact Iff.rfl

theorem algDet_of_core (y η : Fin t → A) (u : ℂ) (h : ∀ p q, Core E y η u p q) (x ξ : Fin t → ℂ) :
    qdet E (u + 1) * ch2 E (u - 1) y x η ξ + chY E (u + 1) y ξ * chX E (u - 1) x η =
      chYY E u y η * chatA E u x ξ := by
  rw [secondChern_eq_double_sum, chY_eq, chX_eq, chYY_eq, chatA_eq, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mul_smul_comm, smul_mul_smul_comm, mul_smul_comm, ← smul_add]
  congr 1
  exact h p q

end Red

section Trans

variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)

theorem J_signed (hJ : QJacobi) (hE : GlRel E) (u : ℂ) (i q l p : Fin t) :
    mS E i l (u + 1) * mS E q p u - mS E q l (u + 1) * mS E i p u = qdet E (u + 1) * nS E i q l p u := by
  have h := hJ A t E hE u i q l p
  have a1 : mS E i l (u + 1) * mS E q p u = ((-1 : ℂ) ^ ((i : ℕ) + (q : ℕ) + (l : ℕ) + (p : ℕ))) •
      (qminor E (skip1 i) (skip1 l) (u + 1) * qminor E (skip1 q) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_smul_comm]
    congr 1
    ring
  have a2 : mS E q l (u + 1) * mS E i p u = ((-1 : ℂ) ^ ((i : ℕ) + (q : ℕ) + (l : ℕ) + (p : ℕ))) •
      (qminor E (skip1 q) (skip1 l) (u + 1) * qminor E (skip1 i) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_smul_comm]
    congr 1
    ring
  rw [a1, a2, ← smul_sub, h, nS]
  by_cases hc : i = q ∨ l = p
  · rw [if_pos hc, if_pos hc, smul_zero, mul_zero]
  · rw [if_neg hc, if_neg hc, cast_mul_eq_smul, mul_smul_comm, smul_smul]
    congr 1
    push_cast
    ring

theorem DV_signed (hD : DetVec) (hE : GlRel E) (y : Fin t → A) (hy : IsVec E y) (w : ℂ) (j : Fin t) :
    qdet E w * y j = y j * qdet E w - ∑ l, y l * mS E j l w := by
  rw [hD A t E y hE hy w j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [cast_mul_eq_smul, mS, mul_smul_comm]
  push_cast
  rfl

theorem MC_signed (hM : MinorCov) (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (u : ℂ) (q p i : Fin t) :
    mS E q p u * η i - η i * mS E q p u = ∑ a, nS E a q i p u * η a := by
  have h := hM A t E η hE hη u q p i
  have a1 : mS E q p u * η i - η i * mS E q p u = ((-1 : ℂ) ^ ((q : ℕ) + (p : ℕ))) •
      (qminor E (skip1 q) (skip1 p) u * η i - η i * qminor E (skip1 q) (skip1 p) u) := by
    unfold mS
    rw [smul_mul_assoc, mul_smul_comm, smul_sub]
  rw [a1, h]
  by_cases hi : i = p
  · rw [if_pos hi, smul_zero]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [nS, if_pos (Or.inr hi), zero_mul]
  · rw [if_neg hi, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = q
    · rw [if_pos ha, nS, if_pos (Or.inl ha), smul_zero, zero_mul]
    · rw [if_neg ha, nS, if_neg (by tauto), cast_mul_eq_smul, smul_smul, smul_mul_assoc]
      congr 1
      push_cast
      ring

theorem covariant_commutes_signed_column_sum (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (hηη : ∀ a b, η a * η b = η b * η a) (j : Fin t)
    (w : ℂ) : ∑ i, η i * mS E i j (w - 1) = ∑ i, mS E i j w * η i := by
  rcases t with _ | t
  · exact j.elim0
  · have h := quantum_minor_move.2 A (t + 1) t E η hE hη hηη id (skip1 j) w
    have hs : ∀ i : Fin (t + 1), (id ∘ i.succAbove : Fin t → Fin (t + 1)) = skip1 i := fun i =>
      funext fun k => (skip_succ_identity t i k).symm
    simp only [hs, id, cast_mul_eq_smul] at h
    push_cast at h
    have l1 : ∑ i, η i * mS E i j (w - 1) = ((-1 : ℂ) ^ (j : ℕ)) •
        ∑ i : Fin (t + 1), ((-1 : ℂ) ^ (i : ℕ)) • (η i * qminor E (skip1 i) (skip1 j) (w - 1)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mS, mul_smul_comm, smul_smul, pow_add, mul_comm]
    have l2 : ∑ i, mS E i j w * η i = ((-1 : ℂ) ^ (j : ℕ)) •
        ∑ i : Fin (t + 1), ((-1 : ℂ) ^ (i : ℕ)) • (qminor E (skip1 i) (skip1 j) w * η i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mS, smul_mul_assoc, smul_smul, pow_add, mul_comm]
    rw [l1, l2, h]

theorem skip_comp (t : ℕ) (q : Fin (t + 2)) (k : Fin (t + 1)) :
    (skip1 q ∘ k.succAbove : Fin t → Fin (t + 2)) = skip2 (min (skip1 q k) q) (max (skip1 q k) q) := by
  funext j
  apply Fin.ext
  rw [Function.comp, ← skip_succ_identity]
  simp only [skip1, skip2, Fin.coe_min, Fin.coe_max, apply_ite Fin.val]
  split_ifs <;> omega

theorem skip_one_ne (t : ℕ) (q : Fin (t + 1)) (k : Fin t) : skip1 q k ≠ q := by
  intro h
  have h' := congrArg Fin.val h
  simp only [skip1, apply_ite Fin.val] at h'
  split_ifs at h' <;> omega

theorem eps_skip (t : ℕ) (q : Fin (t + 1)) (k : Fin t) :
    ((eps (skip1 q k) q : ℤ) : ℂ) * (-1 : ℂ) ^ ((skip1 q k : Fin (t + 1)) : ℕ) = (-1 : ℂ) ^ (k : ℕ) := by
  by_cases h : k.val < q.val
  · have h1 : ((skip1 q k : Fin (t + 1)) : ℕ) = k.val := by simp only [skip1, apply_ite Fin.val]; rw [if_pos h]
    rw [eps, h1, if_pos h]
    simp
  · have h1 : ((skip1 q k : Fin (t + 1)) : ℕ) = k.val + 1 := by simp only [skip1, apply_ite Fin.val]; rw [if_neg h]
    rw [eps, h1, if_neg (by omega)]
    push_cast
    ring

theorem covariant_commutes_signed_minor_sum (hE : GlRel E) (η : Fin t → A) (hη : IsCov E η) (hηη : ∀ a b, η a * η b = η b * η a) (q c p : Fin t)
    (w : ℂ) : ∑ a, η a * nS E a q c p (w - 1) = ∑ a, nS E a q c p w * η a := by
  by_cases hcp : c = p
  · have h0 : ∀ a w', nS E a q c p w' = 0 := fun a w' => by rw [nS, if_pos (Or.inr hcp)]
    simp only [h0, mul_zero, zero_mul]
  rcases t with _ | _ | t
  · exact q.elim0
  · have h0 : ∀ a w', nS E a q c p w' = 0 := fun a w' => by rw [nS, if_pos (Or.inl (Fin.ext (by omega)))]
    simp only [h0, mul_zero, zero_mul]
  · have h := quantum_minor_move.2 A (t + 2) t E η hE hη hηη (skip1 q) (skip2 (min c p) (max c p)) w
    have hs : ∀ k : Fin (t + 1), (skip1 q ∘ k.succAbove : Fin t → Fin (t + 1 + 1)) =
        skip2 (min (skip1 q k) q) (max (skip1 q k) q) := fun k => skip_comp t q k
    simp only [hs, cast_mul_eq_smul] at h
    push_cast at h
    have key : ∀ (k : Fin (t + 1)) (w' : ℂ), nS E (q.succAbove k) q c p w' =
        ((((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) * (-1 : ℂ) ^ (k : ℕ)) •
          qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p)) w' := by
      intro k w'
      rw [← skip_succ_identity, nS, if_neg (by have := skip_one_ne _ q k; tauto), ← eps_skip (t + 1) q k]
      congr 1
      ring
    have hq : ∀ w', nS E q q c p w' = 0 := fun w' => by rw [nS, if_pos (Or.inl rfl)]
    rw [Fin.sum_univ_succAbove _ q, Fin.sum_univ_succAbove _ q, hq, hq, mul_zero, zero_mul, zero_add, zero_add]
    have l1 : ∑ k : Fin (t + 1), η (q.succAbove k) * nS E (q.succAbove k) q c p (w - 1) =
        (((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) • ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ)) •
          (η (skip1 q k) * qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p))
            (w - 1)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [key, mul_smul_comm, smul_smul, skip_succ_identity]
    have l2 : ∑ k : Fin (t + 1), nS E (q.succAbove k) q c p w * η (q.succAbove k) =
        (((eps c p : ℤ) : ℂ) * (-1 : ℂ) ^ ((q : ℕ) + (c : ℕ) + (p : ℕ))) • ∑ k : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ)) •
          (qminor E (skip2 (min (skip1 q k) q) (max (skip1 q k) q)) (skip2 (min c p) (max c p)) w *
            η (skip1 q k)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [key, smul_mul_assoc, smul_smul, skip_succ_identity]
    rw [l1, l2, h]

theorem core_holds (hJ : QJacobi) (hD : DetVec) (hM : MinorCov) (hE : GlRel E) (y η : Fin t → A) (hy : IsVec E y)
    (hη : IsCov E η) (hc : Commute2 y η) (u : ℂ) (p q : Fin t) : Core E y η u p q := by
  have PairingFactorsThroughPeriods : ∀ j, ∑ i, η i * mS E i j u = ∑ i, mS E i j (u + 1) * η i := by
    intro j
    have := covariant_commutes_signed_column_sum E hE η hη hc.2.1 j (u + 1)
    rwa [add_sub_cancel_right] at this
  exact core y η (qdet E (u + 1)) (fun i j => mS E i j (u + 1)) (fun i j => mS E i j u) (fun i j => mS E i j (u - 1))
    (fun a q c p => nS E a q c p u) (fun a q c p => nS E a q c p (u - 1)) hc.2.2
    (fun i q l p => J_signed E hJ hE u i q l p) (fun j => DV_signed E hD hE y hy (u + 1) j)
    (fun q p i => MC_signed E hM hE η hη u q p i) (fun j => covariant_commutes_signed_column_sum E hE η hη hc.2.1 j u) PairingFactorsThroughPeriods
    (fun q c p => covariant_commutes_signed_minor_sum E hE η hη hc.2.1 q c p u) q p

end Trans

end Formalism.FourierDecayAlt.P.ScalarCastIdentities

theorem Formalism.FourierDecayAlt.P.qr_algDetBasis_of :
    Formalism.FourierDecayAlt.Qr.QJacobi → Formalism.FourierDecayAlt.Qr.DetVec → Formalism.FourierDecayAlt.Qr.MinorCov → Formalism.FourierDecayAlt.Qr.AlgDetBasis := by
  intro hJ hD hM A _ _ t E y η hE hy hη hc u p q
  exact (Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core E y η u p q).2
    (Formalism.FourierDecayAlt.P.ScalarCastIdentities.core_holds E hJ hD hM hE y η hy hη hc u p q)

theorem Formalism.FourierDecayAlt.P.qr_algDet_of : Formalism.FourierDecayAlt.Qr.AlgDetBasis → Formalism.FourierDecayAlt.Qr.AlgDet := by
  intro h A _ _ t E y η hE hy hη hc u x ξ
  exact Formalism.FourierDecayAlt.P.ScalarCastIdentities.algDet_of_core E y η u
    (fun p q => (Formalism.FourierDecayAlt.P.ScalarCastIdentities.basis_iff_core E y η u p q).1 (h A t E y η hE hy hη hc u p q)) x ξ
