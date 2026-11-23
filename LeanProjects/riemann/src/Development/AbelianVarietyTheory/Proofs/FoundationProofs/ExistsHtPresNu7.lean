import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IwSys2
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsClosedInertiaCyclotomicKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPrimitiveRootSubOnePowTotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyProdInv

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ.UnitPres

open GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem kumVal_int {n : ℕ} {ζ u v : Ω} {s : G ℚ Ω} {j : ℤ} (hζ : ζ ^ (l ^ n) = 1) (hv : v ^ (l ^ n) = u)
    (hs : s v = ζ ^ j * v) : GlobalTheory.Col.KumVal (l := l) n ζ u s (j : ZMod (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨v, hv, ?_⟩
  rw [hs, ← zpow_natCast, ZMod.val_intCast]
  congr 1
  conv_lhs => rw [← Int.emod_add_mul_ediv j ((l ^ n : ℕ) : ℤ)]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem cg_intCast (n : ℕ) (j : ℤ) : Cg (l := l) n (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) (j : Qbar l) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h1 : (((j : ZMod (l ^ n)).val : ℕ) : ℤ) - j = ((l ^ n : ℕ) : ℤ) * (-(j / ((l ^ n : ℕ) : ℤ))) := by
    rw [ZMod.val_intCast, Int.emod_def]; ring
  have e : (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) - (j : Qbar l) =
      (l : Qbar l) ^ n * ((-(j / ((l ^ n : ℕ) : ℤ)) : ℤ) : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) h1
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow] at this
    exact this
  rw [Cg, e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one (Qbar l) _)

theorem exists_open [IsAlgClosure ℚ Ω] (h : G ℚ Ω → Qbar l) (hc : Continuous h) (h1 : h 1 = 0) (m : ℕ) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, Cg m (h s) 0 := by
  have hl : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ m‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hn : {s | ‖h s‖ < ‖((l : ℕ) : Qbar l) ^ m‖} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa [h1] using hl)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hn
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun s hs => ?_⟩
  rw [Cg, sub_zero]
  exact le_of_lt (hsub hs)

theorem layer_one {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) : z 1 1 = 0 := by
  have h := hz.2 1 (one_mem _) 1 (one_mem _) 1
  rw [mul_one, map_one, inv_one, mul_one] at h
  have h' : (ν 1 : Qbar l) * z 1 1 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left (ν 1).ne_zero

theorem layer_add {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A)
    (ht : t ∈ Dec (F := ℚ) A) (hc : cycMod ℚ Ω l r s = 1) : z (s * t) 1 = z s 1 + (ν s : Qbar l) * z t 1 := by
  have h := hz.2 s hs t ht 1
  rwa [hc, inv_one, mul_one] at h

end GlobalTheory.KZ.UnitPres
