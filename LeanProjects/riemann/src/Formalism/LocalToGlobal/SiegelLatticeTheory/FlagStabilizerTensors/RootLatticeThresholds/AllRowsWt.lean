import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsTr
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf

noncomputable section

open MonoidAlgebra Matrix

namespace Formalism.L2.SG.Pf.AllRowsWt

open Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsTr

def posN (kk s a : ℕ) : ℕ := if a < s then a else if a < s + kk then a - s else if a = s + kk then s else a - kk

section Tor

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (kk s : ℕ) (c : ZMod g)

def tN (a : ℕ) : ZMod g := c ^ posN kk s a

theorem pair (hc : c ≠ 0) {a b : ℕ} (h : posN kk s b = posN kk s a + 1) : (tN kk s c a)⁻¹ * tN kk s c b = c := by
  unfold tN
  rw [h, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hc)]

theorem entN_conj (u : Matrix (Fin N) (Fin N) (ZMod g)) (a b : ℕ) :
    entN (diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * u * diagonal (fun i : Fin N => tN kk s c i)) a b =
      (tN kk s c a)⁻¹ * tN kk s c b * entN u a b := by
  unfold entN
  split_ifs with h
  · simp only [mul_diagonal, diagonal_mul]
    ring
  · simp

theorem phiJ_conj (hc : c ≠ 0) (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    phiJ kk s (diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * u * diagonal (fun i : Fin N => tN kk s c i)) =
      c * phiJ kk s u := by
  unfold phiJ
  simp only [entN_conj]
  have h1 : ∀ i ∈ Finset.range (s - 1), (tN kk s c i)⁻¹ * tN kk s c (i + 1) = c := fun i hi =>
    pair kk s c hc (by rw [Finset.mem_range] at hi; unfold posN; split_ifs <;> omega)
  have h3 : ∀ i ∈ Finset.range (s - 1), (tN kk s c (s + kk + 1 + i))⁻¹ * tN kk s c (s + kk + 2 + i) = c :=
    fun i hi => pair kk s c hc (by rw [Finset.mem_range] at hi; unfold posN; split_ifs <;> omega)
  have h4 : ∀ a ∈ Finset.range (kk - 1), (tN kk s c (s + a))⁻¹ * tN kk s c (s + a + 1) = c := fun a ha =>
    pair kk s c hc (by rw [Finset.mem_range] at ha; unfold posN; split_ifs <;> omega)
  have s1 : ∑ i ∈ Finset.range (s - 1), (tN kk s c i)⁻¹ * tN kk s c (i + 1) * entN u i (i + 1) =
      c * ∑ i ∈ Finset.range (s - 1), entN u i (i + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i hi => by rw [h1 i hi]
  have s3 : ∑ i ∈ Finset.range (s - 1), (tN kk s c (s + kk + 1 + i))⁻¹ * tN kk s c (s + kk + 2 + i) *
      entN u (s + kk + 1 + i) (s + kk + 2 + i) = c * ∑ i ∈ Finset.range (s - 1), entN u (s + kk + 1 + i) (s + kk + 2 + i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i hi => by rw [h3 i hi]
  have s4 : ∑ a ∈ Finset.range (kk - 1), (tN kk s c (s + a))⁻¹ * tN kk s c (s + a + 1) * entN u (s + a) (s + a + 1) =
      c * ∑ a ∈ Finset.range (kk - 1), entN u (s + a) (s + a + 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a ha => by rw [h4 a ha]
  rw [s1, s3, s4]
  split_ifs with hs
  · rw [pair kk s c hc (a := s - 1) (b := s + kk) (by unfold posN; split_ifs <;> omega),
      pair kk s c hc (a := s + kk) (b := s + kk + 1) (by unfold posN; split_ifs <;> omega)]
    ring
  · ring

end Tor

section Conj

variable {g : ℕ} [Fact g.Prime] {N : ℕ} (kk s : ℕ) (c : ZMod g) (hc : c ≠ 0)
include hc

theorem tN_ne (a : ℕ) : tN kk s c a ≠ 0 := pow_ne_zero _ hc

def T : GL (Fin N) (ZMod g) where
  val := diagonal fun i : Fin N => tN kk s c i
  inv := diagonal fun i : Fin N => (tN kk s c i)⁻¹
  val_inv := by rw [diagonal_mul_diagonal]; simp [mul_inv_cancel₀ (tN_ne kk s c hc _)]
  inv_val := by rw [diagonal_mul_diagonal]; simp [inv_mul_cancel₀ (tN_ne kk s c hc _)]

theorem T_conj_val (u : GL (Fin N) (ZMod g)) :
    (((T kk s c hc)⁻¹ * u * T kk s c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
      diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * (u : Matrix (Fin N) (Fin N) (ZMod g)) *
        diagonal (fun i : Fin N => tN kk s c i) := rfl

def PJ (M : Matrix (Fin N) (Fin N) (ZMod g)) : Prop :=
  IsUniUp M ∧ ∀ a, s ≤ a → a < s + kk → entN M a (s + kk) = 0

theorem PJ_conj (u : Matrix (Fin N) (Fin N) (ZMod g)) :
    PJ kk s (diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * u * diagonal (fun i : Fin N => tN kk s c i)) ↔ PJ kk s u := by
  have hX : ∀ i j : Fin N,
      (diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * u * diagonal (fun i : Fin N => tN kk s c i)) i j =
        (tN kk s c i)⁻¹ * tN kk s c j * u i j := by
    intro i j
    simp only [mul_diagonal, diagonal_mul]
    ring
  have hz : ∀ i j : Fin N, (tN kk s c i)⁻¹ * tN kk s c j * u i j = 0 ↔ u i j = 0 := by
    intro i j
    simp [tN_ne kk s c hc]
  have ho : ∀ i : Fin N, (tN kk s c i)⁻¹ * tN kk s c i * u i i = u i i := by
    intro i
    rw [inv_mul_cancel₀ (tN_ne kk s c hc _), one_mul]
  have hent : ∀ a b : ℕ,
      entN (diagonal (fun i : Fin N => (tN kk s c i)⁻¹) * u * diagonal (fun i : Fin N => tN kk s c i)) a b = 0 ↔
        entN u a b = 0 := by
    intro a b
    rw [entN_conj]
    simp [tN_ne kk s c hc]
  unfold PJ IsUniUp
  simp only [hX]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b => ⟨fun hab => (hz a b).1 ((h1 a b).1 hab), fun hab => ?_⟩,
      fun a ha hb => (hent a _).1 (h2 a ha hb)⟩
    subst hab
    rw [← ho]
    exact (h1 a a).2 rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b => ⟨fun hab => (hz a b).2 ((h1 a b).1 hab), fun hab => ?_⟩,
      fun a ha hb => (hent a _).2 (h2 a ha hb)⟩
    subst hab
    rw [ho]
    exact (h1 a a).2 rfl

theorem eJ_conj (ψ : AddChar (ZMod g) ℂ) :
    haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
    MonoidAlgebra.single (T kk s c hc) 1 * eJ g N kk s ψ * MonoidAlgebra.single (T kk s c hc)⁻¹ 1 =
      eJ g N kk s (ψ.mulShift c) := by
  have hP : ∀ x : GL (Fin N) (ZMod g),
      PJ kk s (((T kk s c hc)⁻¹ * x * T kk s c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) ↔
        PJ kk s (x : Matrix (Fin N) (Fin N) (ZMod g)) := fun x => by
    rw [T_conj_val]
    exact PJ_conj kk s c hc _
  have hφ : ∀ x : GL (Fin N) (ZMod g),
      phiJ kk s (((T kk s c hc)⁻¹ * x * T kk s c hc : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
        c * phiJ kk s (x : Matrix (Fin N) (Fin N) (ZMod g)) := fun x => by
    rw [T_conj_val]
    exact phiJ_conj kk s c hc _
  unfold eJ eDat
  simp only [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, MonoidAlgebra.single_mul_single,
    one_mul, mul_one]
  congr 1
  refine Finset.sum_nbij' (fun u => T kk s c hc * u * (T kk s c hc)⁻¹) (fun u => (T kk s c hc)⁻¹ * u * T kk s c hc)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have e : (T kk s c hc)⁻¹ * (T kk s c hc * a * (T kk s c hc)⁻¹) * T kk s c hc = a := by group
    have := (hP (T kk s c hc * a * (T kk s c hc)⁻¹)).1
    rw [e] at this
    exact this ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact (hP a).2 ha
  · intro a _
    group
  · intro a _
    group
  · intro a _
    have e : (T kk s c hc)⁻¹ * (T kk s c hc * a * (T kk s c hc)⁻¹) * T kk s c hc = a := by group
    rw [AddChar.mulShift_apply, ← hφ, e]

end Conj

section SA

variable {g : ℕ} [Fact g.Prime] {N kk s : ℕ}

instance instNZ : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩

open Classical in
theorem eJ_coeff (ψ : AddChar (ZMod g) ℂ) (v : GL (Fin N) (ZMod g)) :
    (eJ g N kk s ψ).coeff v = if PJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g)) then
      (ψ (phiJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹ /
        ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => PJ kk s (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)
      else 0 := by
  unfold eJ eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single] at *
  simp
  simp only [Finsupp.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ,
    true_and]
  unfold PJ
  split_ifs <;> simp [div_eq_inv_mul]
  exact Or.inl (by congr)

private theorem PJ_mul_of_PJ_of_PJ (u v : GL (Fin N) (ZMod g)) (hu : PJ kk s (u : Matrix (Fin N) (Fin N) (ZMod g)))
    (hv : PJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g))) :
    PJ kk s ((u * v : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) := by
  rw [Units.val_mul]
  refine ⟨AllRowsOf.isUniUp_mul hu.1 hv.1, fun a ha hb => ?_⟩
  rw [AllRowsOf.entN_mul_add hu.1 hv.1 hb (fun j hj1 hj2 => hv.2 j (by omega) hj2), hu.2 a ha hb,
    hv.2 a ha hb, add_zero]

theorem PJ_pow (v : GL (Fin N) (ZMod g)) (h : PJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g))) (n : ℕ) :
    PJ kk s ((v ^ n : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) := by
  induction n with
  | zero =>
    rw [pow_zero, Units.val_one]
    refine ⟨fun a b => ⟨fun hab => ?_, fun hab => ?_⟩, fun a ha hb => AllRowsOf.entN_one_ne' (by omega)⟩
    · exact Matrix.one_apply_ne (ne_of_gt hab)
    · rw [hab, Matrix.one_apply_eq]
  | succ n ih =>
    rw [pow_succ]
    exact PJ_mul_of_PJ_of_PJ _ _ ih h

theorem PJ_inv (v : GL (Fin N) (ZMod g)) (h : PJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g))) :
    PJ kk s ((v⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) := by
  have hpos : 0 < Nat.card (GL (Fin N) (ZMod g)) := Nat.card_pos
  have he : v ^ (Nat.card (GL (Fin N) (ZMod g)) - 1) * v = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_card_eq_one']
  rw [← eq_inv_of_mul_eq_one_left he]
  exact PJ_pow v h _

theorem phiJ_inv (v : GL (Fin N) (ZMod g)) (h : PJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g))) :
    phiJ kk s ((v⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) =
      -phiJ kk s (v : Matrix (Fin N) (Fin N) (ZMod g)) := by
  have hi := PJ_inv v h
  have hm := AllRowsOf.phiJ_mul (kk := kk) (s := s) hi.1 h.1 h.2
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at hm
  have e : ∀ a b : ℕ, a ≠ b → entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) a b = 0 :=
    fun a b hab => AllRowsOf.entN_one_ne' hab
  have z1 : ∑ i ∈ Finset.range (s - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) = 0 :=
    Finset.sum_eq_zero fun i _ => e _ _ (by omega)
  have z2 : ∑ i ∈ Finset.range (s - 1),
      entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + kk + 1 + i) (s + kk + 2 + i) = 0 :=
    Finset.sum_eq_zero fun i _ => e _ _ (by omega)
  have z3 : ∑ a ∈ Finset.range (kk - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + a) (s + a + 1) = 0 :=
    Finset.sum_eq_zero fun i _ => e _ _ (by omega)
  have h0 : phiJ kk s (1 : Matrix (Fin N) (Fin N) (ZMod g)) = 0 := by
    unfold phiJ
    rw [z1, z2, z3]
    split_ifs with hs
    · rw [e (s - 1) (s + kk) (by omega), e (s + kk) (s + kk + 1) (by omega)]
      simp
    · simp
  rw [h0] at hm
  linear_combination -hm

end SA

section Wt

variable {g : ℕ} [Fact g.Prime] {N kk s : ℕ}

theorem eJ_selfadj (ψ : AddChar (ZMod g) ℂ) : conjA (eJ g N kk s ψ) = eJ g N kk s ψ := by
  refine MonoidAlgebra.ext (Finsupp.ext fun w => ?_)
  rw [conjA_coeff, eJ_coeff, eJ_coeff]
  have hiff : PJ kk s ((w⁻¹ : GL (Fin N) (ZMod g)) : Matrix (Fin N) (Fin N) (ZMod g)) ↔
      PJ kk s (w : Matrix (Fin N) (Fin N) (ZMod g)) :=
    ⟨fun h => by simpa using PJ_inv _ h, PJ_inv w⟩
  have hs : ∀ x : ZMod g, star (ψ x) = (ψ x)⁻¹ := fun x => by
    rw [← AddChar.map_neg_eq_inv, AddChar.map_neg_eq_conj, starRingEnd_apply]
  by_cases hw : PJ kk s (w : Matrix (Fin N) (Fin N) (ZMod g))
  · rw [if_pos (hiff.2 hw), if_pos hw, phiJ_inv w hw, AddChar.map_neg_eq_inv, inv_inv, star_div₀, hs,
      star_natCast]
  · rw [if_neg (mt hiff.1 hw), if_neg hw, star_zero]

theorem exists_shift (ψ ψ' : AddChar (ZMod g) ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) :
    ∃ c : ZMod g, c ≠ 0 ∧ ψ' = ψ.mulShift c := by
  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  have hbij : Function.Bijective ψ.mulShift := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  exact h' (by rw [← hc, AddChar.mulShift_zero])

theorem wt_indep (ψ ψ' : AddChar (ZMod g) ℂ) (h : ψ ≠ 1) (h' : ψ' ≠ 1) (e : MonoidAlgebra ℂ (GL (Fin N) (ZMod g)))
    (hc : ∀ y, e * y = y * e) :
    (eJ g N kk s ψ' * e).coeff 1 = (eJ g N kk s ψ * e).coeff 1 ∧ (eJ g N kk s ψ').coeff 1 = (eJ g N kk s ψ).coeff 1 := by
  obtain ⟨c, hc0, rfl⟩ := exists_shift ψ ψ' h h'
  rw [← eJ_conj (N := N) kk s c hc0 ψ]
  constructor
  · rw [mul_assoc _ (MonoidAlgebra.single _ 1) e, ← hc (MonoidAlgebra.single _ 1), ← mul_assoc,
      mul_assoc _ (eJ g N kk s ψ) e]
    exact tau_conj _ _
  · exact tau_conj _ _

theorem tau_eJ (ψ : AddChar (ZMod g) ℂ) (e : MonoidAlgebra ℂ (GL (Fin N) (ZMod g))) (he : e * e = e)
    (hc : ∀ y, e * y = y * e) (hse : conjA e = e) :
    (eJ g N kk s ψ * e).coeff 1 = ((∑ h, Complex.normSq ((eJ g N kk s ψ * e).coeff h) : ℝ) : ℂ) := by
  exact tau_proj _ _ (AllRowsOf.eJ_idem g N kk s ψ) (eJ_selfadj ψ) he hc hse

end Wt

end Formalism.L2.SG.Pf.AllRowsWt
