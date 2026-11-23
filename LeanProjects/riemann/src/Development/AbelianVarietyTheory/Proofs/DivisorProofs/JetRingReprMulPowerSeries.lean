import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.JetMul

theorem finite_jet_index {I : Type} [Fintype I] {n : ℕ} : Finite (Idx I n) := by
  refine Finite.of_injective (fun ν : Idx I n => fun i => (⟨ν.1 i, ?_⟩ : Fin (n + 2))) ?_
  · have h1 : ν.1 i ≤ ∑ j, ν.1 j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := ν.2
    omega
  · intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa using congrArg Fin.val this

theorem reprMul {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (μ : Idx I n) :
    J.b.repr (x * y) μ = ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm μ.1) (F * G) := by
  haveI : Finite (Idx I n) := finite_jet_index
  haveI : Fintype (Idx I n) := Fintype.ofFinite _
  have hb : ∀ ν ν' : Idx I n, J.b.repr (J.b ν * J.b ν') μ =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0 := by
    intro ν ν'
    rw [J.mul]
    split_ifs with h1 h2 h2
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_pos (Subtype.ext h2)]
      simp [nsmul_eq_mul]
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (fun h => h2 (congrArg Subtype.val h))]
      simp
    · exact absurd (by rw [h2]; exact μ.2) h1
    · simp
  have hxy : x * y = ∑ ν, ∑ ν', (J.b.repr x ν * J.b.repr y ν') • (J.b ν * J.b ν') := by
    conv_lhs => rw [← J.b.sum_repr x, ← J.b.sum_repr y]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν' _ => ?_
    rw [smul_mul_smul_comm]
  rw [hxy, map_sum, Finsupp.finset_sum_apply]
  simp_rw [map_sum, Finsupp.finset_sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hb, hx, hy]
  have hfac : ∀ ν ν' : Idx I n, ν.1 + ν'.1 = μ.1 →
      (∏ i, (ν.1 i).factorial) * (∏ i, (ν'.1 i).factorial) * (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) =
        ∏ i, (μ.1 i).factorial := by
    intro ν ν' h
    rw [← h, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ← Nat.add_choose_mul_factorial_mul_factorial (ν.1 i) (ν'.1 i), Nat.choose_symm_add]
    ring
  have hterm : ∀ ν ν' : Idx I n,
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F *
        (((∏ i, (ν'.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G) *
        (if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0) =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0 := by
    intro ν ν'
    split_ifs with h
    · rw [← hfac ν ν' h]
      push_cast
      ring
    · simp
  simp_rw [hterm]
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_product' (f := fun ν ν' : Idx I n => if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0), ← Finset.sum_filter]
  have hle : ∀ p : (I →₀ ℕ) × (I →₀ ℕ), p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.equivFunOnFinite.symm μ.1) →
      (∑ i, p.1 i ≤ n + 1) ∧ (∑ i, p.2 i ≤ n + 1) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hμ := μ.2
    have e : ∀ i, p.1 i + p.2 i = μ.1 i := fun i => by
      have := DFunLike.congr_fun hp i
      simpa using this
    have s : ∑ i, p.1 i + ∑ i, p.2 i = ∑ i, μ.1 i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => e i
    omega
  refine Finset.sum_bij' (fun a _ => (Finsupp.equivFunOnFinite.symm a.1.1, Finsupp.equivFunOnFinite.symm a.2.1))
    (fun p hp => (⟨p.1, (hle p hp).1⟩, ⟨p.2, (hle p hp).2⟩)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext i
    simp [← ha.2]
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    funext i
    have := DFunLike.congr_fun hp i
    simpa using this
  · intro a ha
    rfl
  · intro p hp
    ext i <;> simp
  · intro a ha
    rw [Finset.mem_filter] at ha

end GlobalTheory.JetMul
