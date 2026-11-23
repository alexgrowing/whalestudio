import Mathlib

namespace GroundTheory.LocalField.Abstract

def profiniteIntegers : Subring (∀ n : ℕ+, ZMod n) :=
  ⨅ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n),
    RingHom.eqLocus ((ZMod.castHom h (ZMod m)).comp (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n))
      (Pi.evalRingHom (fun k : ℕ+ => ZMod k) m)

abbrev ProfiniteInteger : Type := profiniteIntegers

@[inherit_doc] scoped notation "ℤ̂" => ProfiniteInteger

theorem mem_profiniteIntegers {x : ∀ n : ℕ+, ZMod n} :
    x ∈ profiniteIntegers ↔
      ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (x n) = x m := by
  simp [profiniteIntegers, Subring.mem_iInf, RingHom.mem_eqLocus]

namespace ProfiniteInteger

def proj (n : ℕ+) : ℤ̂ →+* ZMod n :=
  (Pi.evalRingHom (fun k : ℕ+ => ZMod k) n).comp profiniteIntegers.subtype

@[simp] theorem proj_apply (n : ℕ+) (x : ℤ̂) : proj n x = (x : ∀ k : ℕ+, ZMod k) n := rfl

theorem castHom_proj {m n : ℕ+} (h : (m : ℕ) ∣ n) (x : ℤ̂) :
    ZMod.castHom h (ZMod m) (proj n x) = proj m x :=
  mem_profiniteIntegers.1 x.2 m n h

@[ext] theorem ext {x y : ℤ̂} (h : ∀ n, proj n x = proj n y) : x = y :=
  Subtype.ext (funext h)

@[simp] theorem proj_intCast (n : ℕ+) (m : ℤ) : proj n (m : ℤ̂) = m := map_intCast _ m

theorem isClosed_profiniteIntegers :
    IsClosed (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) := by
  have : (profiniteIntegers : Set (∀ n : ℕ+, ZMod n)) =
      ⋂ (m : ℕ+) (n : ℕ+) (h : (m : ℕ) ∣ n), {x | ZMod.castHom h (ZMod m) (x n) = x m} := by
    ext x
    simp only [SetLike.mem_coe, mem_profiniteIntegers, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h => ?_
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n)) (continuous_apply m)

instance : CompactSpace ℤ̂ :=
  isCompact_iff_compactSpace.mp isClosed_profiniteIntegers.isCompact

theorem continuous_proj (n : ℕ+) : Continuous (proj n) :=
  (continuous_apply n).comp continuous_subtype_val

instance : CharZero ℤ̂ := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h := congrArg (proj n.succPNat) hn
  rw [map_natCast, map_zero, ZMod.natCast_eq_zero_iff, Nat.succPNat_coe] at h
  exact Nat.eq_zero_of_dvd_of_lt h (Nat.lt_succ_self n)

theorem dvd_of_intCast_eq_nsmul {n : ℕ} (hn : 0 < n) {m : ℤ} {w : ℤ̂} (h : (m : ℤ̂) = n • w) :
    (n : ℤ) ∣ m := by
  obtain ⟨N, rfl⟩ : ∃ N : ℕ+, (N : ℕ) = n := ⟨⟨n, hn⟩, rfl⟩
  have h' := congrArg (proj N) h
  rw [map_intCast, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul] at h'
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd m N).1 h'

end ProfiniteInteger

end GroundTheory.LocalField.Abstract
