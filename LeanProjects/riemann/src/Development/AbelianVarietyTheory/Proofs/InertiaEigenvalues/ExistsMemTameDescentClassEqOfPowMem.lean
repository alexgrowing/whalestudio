import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentMonodromyImageValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDivisibilityOfDescentDatumStatement

noncomputable section

namespace GlobalTheory.LcImage

open PowerSeries GlobalTheory.BK GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction

theorem norm_intCast_eq_one {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] {u : ℤ} (hu : ¬ (l : ℤ) ∣ u) : ‖(u : K)‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one u)
    (not_lt.1 fun h => hu (Padic.norm_intCast_lt_one_iff.1 h))

theorem exists_mul_intCast_eq {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {r : ℤ} (hr : r ≠ 0)
    {m : ℕ} (hm : padicValInt l r ≤ m) : ∃ t : O, algebraMap O K t * (r : K) = (l : K) ^ m := by
  obtain ⟨v, hvdef⟩ : ∃ v, padicValInt l r = v := ⟨_, rfl⟩
  have hdv := padicValInt_dvd (p := l) r
  rw [hvdef] at hdv hm
  obtain ⟨u, hu⟩ := hdv
  have hpr : (l : ℕ).Prime := Fact.out
  have hu' : ¬ (l : ℤ) ∣ u := by
    rintro ⟨k, rfl⟩
    have h := (padicValInt_dvd_iff (p := l) (v + 1) r).1
      ⟨k, by rw [hu, pow_succ]; ring⟩
    omega
  have hl0 : (l : K) ≠ 0 := natCast_ne_zero' l hpr.ne_zero
  have hu0 : (u : K) ≠ 0 := by
    intro h
    have := norm_intCast_eq_one (K := K) l hu'
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set t : K := (l : K) ^ (m - v) * (u : K)⁻¹ with ht
  obtain ⟨t', ht'⟩ := (IsUnitBall.mem_range_iff (O := O) t).2 (by
    rw [ht, norm_mul, norm_pow, norm_inv, norm_intCast_eq_one l hu', inv_one, mul_one, norm_l l]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_le)))
  refine ⟨t', ?_⟩
  rw [ht', ht, hu]
  push_cast
  rw [mul_comm ((l : K) ^ v), ← mul_assoc, mul_assoc _ _ (u : K), inv_mul_cancel₀ hu0,
    mul_one, ← pow_add, Nat.sub_add_cancel hm]

theorem exists_mem_Y'_Lc_cls_eq : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (U : Finset ℤ) (N : ℕ), D.jumps ⊆ U → U ⊆ Finset.Icc (-(η : ℤ)) H → U.card ≤ N + 1 → η < H → H + η < l → 10 * H + 2 ≤ l → ∀ c : ℕ, ∀ w ∈ D.Zl, (l : K) ^ c • D.Lc w ∈ D.Z → ∃ y ∈ D.Y', D.Lc (D.cls y) = (l : K) ^ (c + η + (N + 1) * η) • D.Lc w := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D U N hJ hU hN hηH hl h10 c w hw hc
  obtain ⟨-, hVal, hInt⟩ := GlobalTheory.T.breuilKisinDescent_monodromy_image_valuation O K l e a ι η H D U N hJ hU hN hηH
  obtain ⟨-, hR0, hv, hcard, hcard'⟩ := hVal hl

  obtain ⟨z, hz, hRz⟩ := hInt h10 (c : ℤ) (D.LcZ ⟨w, hw⟩) ⟨_, rfl⟩ (by
    rw [zpow_natCast, D.coe_LcZ]; exact hc)
  rw [zpow_natCast] at hz
  have hRz' : (((polyR l e U η).eval 0 : ℤ) : K) • D.Lc w = D.Lc z := by
    simpa using congrArg Subtype.val hRz

  obtain ⟨t, ht⟩ := exists_mul_intCast_eq (O := O) (K := K) l hR0 (m := (N + 1) * η)
    (by omega)
  have hx1 : t • ((l : K) ^ c • (z : D.Pol)) ∈ D.Z := D.Z.smul_mem t hz
  have hLx1 : D.Lc (t • ((l : K) ^ c • (z : D.Pol))) = (l : K) ^ (c + (N + 1) * η) • D.Lc w := by
    rw [← algebraMap_smul K t, map_smul, map_smul, ← hRz', smul_smul, smul_smul, pow_add]
    congr 1
    rw [← ht]; ring

  obtain ⟨z'', hz'', hv''⟩ := (GlobalTheory.T.prime_pow_divisibility_of_descentDatum O K l e a ι η H D).1 _ hx1

  have hz3 : z'' ∈ (D.desc.Y η).map (D.cls.restrictScalars O) := by
    rw [Descent.map_Y]; exact hz''
  obtain ⟨y'', hy'', rfl⟩ := hz3
  refine ⟨(X : K⟦X⟧) ^ e • y'', (Descent.mem_Y' _).2 ⟨y'', hy'', rfl⟩, ?_⟩
  have h1 : D.cls ((X : K⟦X⟧) ^ e • y'') = (l : K) ^ η • (t • ((l : K) ^ c • (z : D.Pol))) := by
    rw [hv'']; rfl
  rw [h1, map_smul, hLx1, smul_smul, ← pow_add]
  congr 2
  ring

end GlobalTheory.LcImage
