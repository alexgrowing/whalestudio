import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

noncomputable section

namespace Formalism.L2.LocGap.Gal

open Formalism.BasicNotions Formalism.BasicNotions.Loc

variable (l : ℕ) [Fact l.Prime]

instance enoughRoots (i : ℕ) : HasEnoughRootsOfUnity (Om l) (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  infer_instance

def χZ : GQ l →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l))

def χQ : GQ l →* ℚ_[l]ˣ := (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp (χZ l)

variable {l}

theorem χQ_coe (g : GQ l) : ((χQ l g : ℚ_[l]ˣ) : ℚ_[l]) = (((χZ l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := rfl

theorem χZ_continuous : Continuous (χZ l) := by
  first
    | exact cyclotomicCharacter.continuous l ℚ_[l] (Om l)
    | (unfold χZ; exact cyclotomicCharacter.continuous l ℚ_[l] (Om l))

theorem χZ_spec (g : GQ l) (m : ℕ) (ζ : Om l) (h : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ (((χZ l g : ℤ_[l]ˣ) : ℤ_[l]).toZModPow m).val :=
  cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (GQ l) (Om l) g) ζ h

theorem norm_sub_toZModPow_val (x : ℤ_[l]) (m : ℕ) :
    ‖x - (((x.toZModPow m).val : ℕ) : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast,
    ZMod.natCast_zmod_val, sub_self]

theorem χQ_cyc (g : GQ l) (m : ℕ) (ζ : Om l) (h : ζ ^ (l ^ m) = 1) :
    ∃ a : ℕ, ‖(χQ l g : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ∧ g ζ = ζ ^ a := by
  refine ⟨_, ?_, χZ_spec g m ζ h⟩
  rw [χQ_coe]
  have h2 := norm_sub_toZModPow_val ((χZ l g : ℤ_[l]ˣ) : ℤ_[l]) m
  rw [PadicInt.norm_def] at h2
  push_cast at h2
  exact h2

variable (l)

theorem exists_root_ne_one : ∃ z : Om l, z ^ l = 1 ∧ z ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ 1)
  rw [pow_one] at hζ
  exact ⟨ζ, hζ.pow_eq_one, hζ.ne_one (Fact.out : l.Prime).one_lt⟩

theorem exists_root (x : Om l) : ∃ z : Om l, z ^ l = x :=
  IsAlgClosed.exists_pow_nat_eq x (Fact.out : l.Prime).pos

def ζQ : ℕ → Om l
  | 0 => 1
  | 1 => (exists_root_ne_one l).choose
  | (m + 2) => (exists_root l (ζQ (m + 1))).choose

theorem ζQ_zero : ζQ l 0 = 1 := rfl

theorem ζQ_one : ζQ l 1 ≠ 1 := (exists_root_ne_one l).choose_spec.2

theorem ζQ_succ (m : ℕ) : ζQ l (m + 1) ^ l = ζQ l m := by
  cases m with
  | zero => exact (exists_root_ne_one l).choose_spec.1
  | succ m => exact (exists_root l (ζQ l (m + 1))).choose_spec

theorem ζQ_pow (m k : ℕ) : ζQ l (m + k) ^ (l ^ k) = ζQ l m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ, pow_mul', ζQ_succ, ih]

theorem ζQ_pow_eq_one (m : ℕ) : ζQ l m ^ (l ^ m) = 1 := by
  have h := ζQ_pow l 0 m
  rw [zero_add, ζQ_zero] at h
  exact h

theorem ζQ_primitive (m : ℕ) : IsPrimitiveRoot (ζQ l m) (l ^ m) := by
  cases m with
  | zero =>
    rw [ζQ_zero, pow_zero]
    exact IsPrimitiveRoot.one
  | succ n =>
    rw [IsPrimitiveRoot.iff_orderOf]
    refine orderOf_eq_prime_pow ?_ (ζQ_pow_eq_one l (n + 1))
    have h := ζQ_pow l 1 n
    rw [add_comm 1 n] at h
    rw [h]
    exact ζQ_one l

end Formalism.L2.LocGap.Gal
