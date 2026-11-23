import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MassConstUniqueOne

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Arith

variable {F : Type} [Field F] [NumberField F]

def nfT (F : Type) [Field F] [NumberField F] (T : ℕ) : Multiset (Ideal (𝓞 F)) :=
  UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((T : ℕ) : 𝓞 F)})

def supT (F : Type) [Field F] [NumberField F] (T : ℕ) : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
  (nfT F T).toFinset.subtype (fun 𝔭 => 𝔭.IsMaximal)

theorem span_natCast_ne_bot {T : ℕ} (hT : 0 < T) : Ideal.span {((T : ℕ) : 𝓞 F)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hT.ne'

theorem mem_nfT_iff {T : ℕ} (hT : 0 < T) (P : Ideal (𝓞 F)) :
    P ∈ nfT F T ↔ P.IsPrime ∧ ((T : ℕ) : 𝓞 F) ∈ P := by
  unfold nfT
  rw [Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hT), Ideal.span_singleton_le_iff_mem]

theorem isMaximal_of_mem_nfT {T : ℕ} (hT : 0 < T) {P : Ideal (𝓞 F)} (h : P ∈ nfT F T) :
    P.IsMaximal := by
  obtain ⟨hP, hm⟩ := (mem_nfT_iff hT P).1 h
  refine hP.isMaximal ?_
  rintro rfl
  rw [Ideal.mem_bot] at hm
  exact (Nat.cast_ne_zero.2 hT.ne') hm

theorem mem_supT {T : ℕ} (hT : 0 < T) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    𝔭 ∈ supT F T ↔ ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 := by
  unfold supT
  rw [Finset.mem_subtype, Multiset.mem_toFinset, mem_nfT_iff hT]
  exact ⟨fun h => h.2, fun h => ⟨𝔭.2.isPrime, h⟩⟩

theorem tprod_supT {T : ℕ} (hT : 0 < T) (g : Ideal (𝓞 F) → ℝ) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then g 𝔭.1 else 1)) =
      ∏ P ∈ (nfT F T).toFinset, g P := by
  rw [tprod_eq_prod (s := supT F T)]
  · unfold supT
    rw [Finset.prod_subtype_eq_prod_filter (f := fun P => if ((T : ℕ) : 𝓞 F) ∈ P then g P else 1)]
    rw [Finset.filter_true_of_mem (fun P hP => isMaximal_of_mem_nfT hT (Multiset.mem_toFinset.1 hP))]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [if_pos ((mem_nfT_iff hT P).1 (Multiset.mem_toFinset.1 hP)).2]
  · intro 𝔭 h𝔭
    rw [if_neg (fun h => h𝔭 ((mem_supT hT 𝔭).2 h))]

theorem absNorm_span_natCast (T : ℕ) :
    Ideal.absNorm (Ideal.span {((T : ℕ) : 𝓞 F)}) = T ^ finrank ℚ F := by
  rw [Ideal.absNorm_span_singleton]
  have e : ((T : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (T : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem prod_absNorm_pow {T : ℕ} (hT : 0 < T) :
    ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P : ℝ) ^ (vT F T P) = (T : ℝ) ^ finrank ℚ F := by
  have h1 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (Multiset.count P (nfT F T)) =
      ((nfT F T).map Ideal.absNorm).prod := (Finset.prod_multiset_map_count _ _).symm
  have h2 : ((nfT F T).map Ideal.absNorm).prod = Ideal.absNorm (nfT F T).prod :=
    (map_multiset_prod Ideal.absNorm _).symm
  have h3 : (nfT F T).prod = Ideal.span {((T : ℕ) : 𝓞 F)} :=
    Ideal.prod_normalizedFactors_eq_self (span_natCast_ne_bot hT)
  have h4 : ∏ P ∈ (nfT F T).toFinset, (Ideal.absNorm P) ^ (vT F T P) = T ^ finrank ℚ F := by
    have : ∀ P, vT F T P = Multiset.count P (nfT F T) := fun P => rfl
    simp only [this]
    rw [h1, h2, h3, absNorm_span_natCast]
  exact_mod_cast h4

end Arith

theorem etaF_cases (K F : Type) [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) :
    etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
  unfold etaF
  split_ifs <;> simp

theorem factor_eq (q η x : ℝ) (hq : q ≠ 1) (hq0 : 0 ≤ q) (hη : η = 1 ∨ η = -1) (k v : ℕ) (hk : 1 ≤ k) :
    q ^ ((k - 1) * v) * x / (1 - η * q⁻¹) * (q ^ v * (1 - η * q⁻¹)) = (q ^ v) ^ k * x := by
  have hne : 1 - η * q⁻¹ ≠ 0 := by
    rcases hη with rfl | rfl
    · rw [one_mul, sub_ne_zero]
      intro h
      exact hq (inv_eq_one.mp h.symm)
    · have : 0 ≤ q⁻¹ := inv_nonneg.2 hq0
      have : 0 < 1 - (-1) * q⁻¹ := by linarith
      exact this.ne'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel, div_mul_eq_mul_div, div_eq_iff hne]
  ring

theorem lamGlue : LamGlue := by
  intro K F _ _ _ _ k T hk hT
  have e1 := tprod_supT (F := F) hT (fun P => (Ideal.absNorm P : ℝ) ^ ((k - 1) * vT F T P) *
    (1 - etaF K F P ^ k * (Ideal.absNorm P : ℝ) ^ (-(k : ℤ))) / (1 - etaF K F P * (Ideal.absNorm P : ℝ)⁻¹))
  have e2 := tprod_supT (F := F) hT (fun P => (Ideal.absNorm P : ℝ) ^ vT F T P *
    (1 - etaF K F P * (Ideal.absNorm P : ℝ)⁻¹))
  have e3 := tprod_supT (F := F) hT (fun P => 1 - etaF K F P ^ k * (Ideal.absNorm P : ℝ) ^ (-(k : ℤ)))
  beta_reduce at e1 e2 e3
  unfold lamT glueT
  rw [e1, e2, e3, ← Finset.prod_mul_distrib, pow_mul', ← prod_absNorm_pow hT, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hmax : P.IsMaximal := isMaximal_of_mem_nfT hT (Multiset.mem_toFinset.1 hP)
  have hq : (Ideal.absNorm P : ℝ) ≠ 1 := by
    rw [Ne, Nat.cast_eq_one, Ideal.absNorm_eq_one_iff]
    exact hmax.ne_top
  exact factor_eq _ _ _ hq (Nat.cast_nonneg _) (etaF_cases K F P) k _ hk

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
