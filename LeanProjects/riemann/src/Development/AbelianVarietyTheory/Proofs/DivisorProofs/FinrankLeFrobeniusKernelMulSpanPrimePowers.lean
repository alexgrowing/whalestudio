import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def IterFrobBase (K : Type) (p r : ℕ) : Type := K

namespace IterFrobBase

variable (K : Type) (p r : ℕ) [Field K]

instance : Field (IterFrobBase K p r) := inferInstanceAs (Field K)

variable [hp : Fact p.Prime] [CharP K p]

instance : Algebra (IterFrobBase K p r) K :=
  (SS.FrobField.powHom K p r hp.out (CharP.cast_eq_zero K p)).toAlgebra

instance (H : Type) [CommRing H] [HopfAlgebra K H] : HopfAlgebra (IterFrobBase K p r) H :=
  inferInstanceAs (HopfAlgebra K H)

end IterFrobBase

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H]
  [HopfAlgebra K H] (r : ℕ)

omit hp in
theorem natCast_eq_zero_of_charP_algebra (A : Type) [CommRing A] [Algebra K A] : (p : A) = 0 := by
  rw [← map_natCast (algebraMap K A), CharP.cast_eq_zero, map_zero]

def iterFrobSemi : SemiBialgHom (algebraMap (IterFrobBase K p r) K) H H where
  toRingHom := SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H)
  smul_map c a := by
    change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
    rw [smul_pow]
  counit_map a := by
    change counit (R := K) (a ^ p ^ r) = (counit (R := K) a) ^ p ^ r
    rw [counit_pow]
  comul_map a := by
    have key : ∀ c : H ⊗[IterFrobBase K p r] H,
        SS.FrobField.powHom (H ⊗[K] H) p r hp.out (natCast_eq_zero_of_charP_algebra p K _)
          (@id (H ⊗[K] H) c) =
        TensorProduct.map (σ₁₂ := algebraMap (IterFrobBase K p r) K)
          ⟨⟨SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H),
            map_add _⟩, fun c a => by
              change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
              rw [smul_pow]⟩
          ⟨⟨SS.FrobField.powHom H p r hp.out (natCast_eq_zero_of_charP_algebra p K H),
            map_add _⟩, fun c a => by
              change (c • a) ^ p ^ r = ((c : K) ^ p ^ r) • a ^ p ^ r
              rw [smul_pow]⟩ c := by
      intro c
      induction c with
      | zero => exact map_zero _
      | add x y hx hy =>
        rw [map_add, ← hx, ← hy]
        exact map_add _ (@id (H ⊗[K] H) x) (@id (H ⊗[K] H) y)
      | tmul x y =>
        change (x ⊗ₜ[K] y) ^ p ^ r = (x ^ p ^ r) ⊗ₜ[K] (y ^ p ^ r)
        exact Algebra.TensorProduct.tmul_pow x y _
    change comul (R := K) (a ^ p ^ r) = _
    rw [comul_pow]
    exact key (comul a)

def iterRelFrob : K ⊗[IterFrobBase K p r] H →ₐc[K] H := (iterFrobSemi p K H r).liftBC

theorem iterRelFrob_tmul (c : K) (a : H) : iterRelFrob p K H r (c ⊗ₜ a) = c • a ^ p ^ r :=
  SemiBialgHom.liftBC_tmul _ c a

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

theorem finrank_le_frobKer_mul_span_pow (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] (r : ℕ) :
    Module.finrank K H ≤ Module.finrank K (H ⧸ frobKerIdeal (p ^ r) K H) *
      Module.finrank K (Submodule.span K (Set.range fun a : H => a ^ p ^ r)) := by
  set f := iterRelFrob p K H r
  rw [finrank_eq_ker_mul_range K H _ f]
  refine Nat.mul_le_mul ?_ ?_
  · have hle : frobKerIdeal (p ^ r) K H ≤ kerIdeal f := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      have ha' : counit (R := K) a = 0 := ha
      have hb : (1 : K) ⊗ₜ[IterFrobBase K p r] a ∈
          augIdeal K (K ⊗[IterFrobBase K p r] H) := by
        change counit (R := K) ((1 : K) ⊗ₜ[IterFrobBase K p r] a) = 0
        rw [← toBaseChange_apply (IterFrobBase K p r) K H a, SemiBialgHom.counit_map]
        have ha'' : counit (R := IterFrobBase K p r) a = 0 := ha'
        rw [ha'', map_zero]
      have e : f ((1 : K) ⊗ₜ a) = a ^ p ^ r := by
        rw [iterRelFrob_tmul, one_smul]
      show a ^ p ^ r ∈ _
      rw [← e]
      exact Ideal.mem_map_of_mem _ hb
    exact LinearMap.finrank_le_finrank_of_surjective
      (f := (Ideal.Quotient.factorₐ K hle).toLinearMap)
      (Ideal.Quotient.factor_surjective hle)
  · refine Submodule.finrank_mono ?_
    rintro _ ⟨x, rfl⟩
    induction x with
    | zero => simp
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    | tmul c a =>
      change f (c ⊗ₜ a) ∈ _
      rw [iterRelFrob_tmul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.PDiv
