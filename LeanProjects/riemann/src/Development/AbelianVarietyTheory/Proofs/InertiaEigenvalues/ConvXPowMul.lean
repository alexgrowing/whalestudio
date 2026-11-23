import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Approx

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) (f : ℤ → M) (k : ℤ) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → f (k - j) = 0) :
    conv e f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • f (k - j) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hj (by rw [hN j (not_lt.1 hc), smul_zero])

theorem exists_bound {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (k : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → f (k - j) = 0 := by
  refine ⟨(k - m₀ + 1).toNat, fun j hj => hf _ ?_⟩
  have h1 := Int.self_le_toNat (k - m₀ + 1)
  have h2 : (((k - m₀ + 1).toNat : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  omega

theorem conv_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (e e' : PowerSeries L) :
    conv (e + e') f = conv e f + conv e' f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.add_apply, conv_eq_sum _ f k N hN, map_add, add_smul, Finset.sum_add_distrib]

theorem conv_smul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e : PowerSeries L) :
    conv (c • e) f = c • conv e f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.smul_apply, conv_eq_sum _ f k N hN, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem conv_smul_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e e' : PowerSeries L) :
    conv (c • (e + e')) f = c • conv e f + c • conv e' f := by
  rw [conv_smul hf, conv_add hf, smul_add]

theorem conv_X_pow_mul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (m : ℕ) (p : PowerSeries L)
    (k : ℤ) : conv (PowerSeries.X ^ m * p) f k = conv p f (k - m) := by
  obtain ⟨N, hN⟩ := exists_bound hf (k - m)
  have hN' : ∀ j : ℕ, m + N ≤ j → f (k - j) = 0 := by
    intro j hj
    have := hN (j - m) (by omega)
    rwa [show k - (m : ℤ) - ((j - m : ℕ) : ℤ) = k - j by push_cast [show m ≤ j by omega]; ring] at this
  rw [conv_eq_sum _ f k _ hN', conv_eq_sum _ f (k - m) N hN, Finset.sum_range_add]
  rw [Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show m + j - m = j by omega]
    congr 2
    push_cast
    ring
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]

theorem combine {ι : Type} [Fintype ι] (F : ι → ℤ → M) (m₀ : ι → ℤ) (hbd : ∀ j, ∀ k < m₀ j, F j k = 0)
    (c : L) (e p : ι → PowerSeries L) (m : ℕ) (k : ℤ) :
    (∑ j, conv (c • (e j + PowerSeries.X ^ m * p j)) (F j)) k - c • (∑ j, conv (e j) (F j)) k =
      (∑ j, c • conv (p j) (F j)) (k - m) := by
  simp only [fun j => conv_smul_add (hbd j) c (e j) (PowerSeries.X ^ m * p j), Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum, fun j => conv_X_pow_mul (hbd j) m (p j) k]
  abel

end Series

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem approx : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ g ∈ Lat C h T i ζ, ∀ m : ℕ, ∃ (n : ↥(W.N T)) (c : ↥LL.1), c ≠ 0 ∧ ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ n j - c • g j = f (j - m) := by
  intro D HW F Cm l _ K s LL h W C T hT i ζ hζ g hg m
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨s, hζ⟩
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hFull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  obtain ⟨hsm, hB⟩ := GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ hζ' hFull
  obtain ⟨-, hspan, -⟩ := hB _ nb
  obtain ⟨e, rfl⟩ := hspan g hg
  have hW := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.1 i ζ hζ'
  choose a c hc hdiv using fun j => hW (e j) m
  choose p hp using hdiv
  haveI := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ↥(OL LL)) c
  have ho : ∀ j, ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = (b : ↥(OL LL)) • c j :=
    fun j => RingHom.mem_rangeS.1 (hb j)
  choose o ho using ho
  obtain ⟨cc, hccd⟩ : ∃ x : ↥LL.1, x = algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) := ⟨_, rfl⟩
  have hcc : cc ≠ 0 := hccd ▸ IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (o j) = cc * c j := by
    intro j
    rw [ho j, hccd, Algebra.smul_def]
  choose m0 hm0 using fun j => (C.C K s LL h).tie.levB_supp T i ζ (nb j)
  have hlev : ∀ j, W.lev i ζ (o j • a j) = cc • (e j + PowerSeries.X ^ m * p j) := by
    intro j
    rw [map_smul, ← algebraMap_smul ↥LL.1 (o j), ho' j, mul_smul, ← hp j, add_sub_cancel]
  have hbd : ∀ j, ∀ k < m0 j, ex C h T i ζ (nb j) k = 0 := hm0
  have hexn : ex C h T i ζ (∑ j, (o j • a j) • nb j) =
      ∑ j, conv (cc • (e j + PowerSeries.X ^ m * p j)) (ex C h T i ζ (nb j)) := by
    have := map_sum ((C.C K s LL h).tie.levB T i ζ) (fun j => (o j • a j) • nb j) Finset.univ
    refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hlev j]
    exact hsm _ _
  refine ⟨∑ j, (o j • a j) • nb j, cc, hcc, ∑ j, cc • conv (p j) (ex C h T i ζ (nb j)),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p j, nb j, rfl⟩),
    fun k => ?_⟩
  rw [hexn]
  exact combine _ m0 hbd cc e p m k

end GlobalTheory.NL.Approx
