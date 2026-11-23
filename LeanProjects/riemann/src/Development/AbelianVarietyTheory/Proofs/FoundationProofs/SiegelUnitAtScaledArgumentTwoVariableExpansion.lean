import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsupp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionSiegelUnitInTower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSmoothedEisensteinFxWeightOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedEisensteinFxCoefficientSeqOneMemSubringStatement

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.DlogOne GlobalTheory.Sieg.Model

namespace GlobalTheory.SiegTwo

theorem map_smF {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K'] (ε : K →+* K') (c : ℤ) (j M : ℕ) (ζ : K)
    (a b : ℤ) (n : ℕ) : ε (smF c j M ζ a b n) = smF c j M (ε ζ) a b n := by
  simp [smF, eisF, const0, coefPos, apply_ite ε, map_ofNat]

theorem map_finsum_zpow {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (θ : ℤ →₀ ℤ) (w : ℤ → ℤ → ℤ) (hw : ∀ k, w k 0 = 0) (ζ : Ω)
    (g : ℤ) : ε (∑ᶠ k : ℤ, ((w k (θ k) : ℤ) : Ω) * ζ ^ (g * k)) = θ.sum fun k n => ((w k n : ℤ) : ℂ) * (ε ζ ^ g) ^ k := by
  rw [finsum_eq_sum_of_support_subset (s := θ.support), map_sum]
  · simp [Finsupp.sum, zpow_mul]
  · intro k hk
    by_contra h
    have : θ k = 0 := by simpa using h
    exact hk (by simp [this, hw])

theorem coeff_sgN {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : GlobalTheory.KZ.Tower Ω ε) (c : ℕ) {N : ℕ}
    (hN : 0 < N) (M : ℕ) (a : ℤ × ℤ) (r : ℚ) :
    (X.exp (sgN X c N M a)).coeff (r * N) = (X.exp (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M])).coeff r := by
  have hd : (0 : ℤ) < (!![(N : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simpa [Matrix.det_fin_two] using hN
  have he : ∀ i k, ent (toGQ !![(N : ℤ), 0; 0, 1]) i k = ((!![(N : ℤ), 0; 0, 1] i k : ℤ) : ℚ) := fun i k => by
    simp only [ent, toGQ, dif_pos hd]; rfl
  have h := X.exp_upper (toGQ !![(N : ℤ), 0; 0, 1]) (by rw [he]; simp) (siegel X c ![(a.1 : ℚ) / M, (a.2 : ℚ) / M]) r
  rw [he, he, he] at h
  have h0 : eOm ε 0 = 1 := ε.injective (by rw [GalUnits.eps_eOm]; simp [ee])
  simpa [h0, sgN] using h

theorem sgN_two_variable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (L N c : ℕ) (A₁ a₂ g : ℤ), 1 ≤ L → a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∃ θ : ℤ → ℤ → ℤ,
    (∀ r : ℤ, ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k r = 0) ∧
    (∃ r0 : ℤ, ∀ k r : ℤ, r < r0 → θ k r = 0) ∧
    (∀ k r : ℤ, θ k r ≠ 0 → (p : ℤ) ^ L ∣ r - A₁ * k) ∧
    (∀ r : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = ∑ᶠ k : ℤ, (θ k r : Ω) * zt ε p L ^ (g * k)) ∧
    (∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ω) * zt ε p L ^ (g * k) =
      -∑ᶠ i : ℤ, (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L)) ∧
    (∀ n : ℕ, smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ n ∈ Subring.closure {zt ε p L}) ∧
    (∃ r m : ℤ, (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = zt ε p L ^ m ∨
      (X.exp (sgN X c N (N * p ^ L) (A₁, a₂))).coeff ((r : ℚ) / (p : ℚ) ^ L) = -(zt ε p L ^ m)) := by
  intro Ω _ _ _ ε X _ p hp _ L N c A₁ a₂ g _ hg hNa hN hNp hc hcop hA
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain ⟨g', rfl⟩ := hNa
  set M := N * p ^ L with hMd
  have hp0 : 0 < p := hp.out.pos
  have hM : 0 < M := by positivity
  have hMq : (M : ℚ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hMc : (M : ℂ) = N * p ^ L := by rw [hMd]; push_cast; rfl
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hc6 : Nat.Coprime c 6 := (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_right_right
  have hcM : Nat.Coprime c M := Nat.Coprime.mul_right (Nat.Coprime.coprime_mul_right_right hcop).coprime_mul_left_right
    (hcop.coprime_mul_left_right.pow_right L)
  have hA2 : ¬ (M : ℤ) ∣ A₁ * c := fun h =>
    hA ((Nat.isCoprime_iff_coprime.2 hcM.symm).dvd_of_dvd_mul_right h)
  have hadm : admitted c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M] := by
    refine ⟨hc, hc6, fun ⟨⟨m, hm⟩, _⟩ => hA2 ⟨m, ?_⟩⟩
    have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have : (A₁ : ℚ) * c = M * m := by
      rw [hm]; simp only [Matrix.cons_val_zero]; field_simp
    exact_mod_cast this
  have ez : ε (zt ε p L) = ee (1 / (p : ℂ) ^ L) := by rw [zt, GalUnits.eps_eOm]; push_cast; rfl
  have eM : ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by rw [GalUnits.eps_eOm]; push_cast; rfl
  have hz1 : ee (1 / (p : ℂ) ^ L) ^ ((p : ℤ) ^ L) = 1 := by
    rw [← ee_int_mul]; push_cast; rw [mul_one_div_cancel (pow_ne_zero _ hpc)]; simp [ee]
  have hv : ee (((N * g' : ℤ) : ℂ) / M) = ε (zt ε p L) ^ g := by
    have hco : IsCoprime ((p : ℤ) ^ L) (N : ℤ) := (Nat.isCoprime_iff_coprime.2 hNp.symm).pow_left
    obtain ⟨u, hu⟩ := hco.dvd_of_dvd_mul_left (by simpa only [← mul_sub] using hg.dvd : (p : ℤ) ^ L ∣ N * (g - g'))
    rw [ez, show g = g' + (p : ℤ) ^ L * u by linarith, zpow_add₀ (ee_ne_zero _), zpow_mul, hz1, one_zpow, mul_one,
      ← ee_int_mul, hMc]
    congr 1
    push_cast
    field_simp
  obtain ⟨k, a, b, qa, qb, hj, i, hi⟩ := sg_jets hM hadm hA hA2
  rw [hv] at hj hi
  obtain ⟨r1, r2⟩ := exp_of_hasQ X _ _ hM k a (SiegelMem.an_siegel_eq Ω ε X c _ hadm) qa
  set y := X.exp (sgN X c N M (A₁, N * g')) with hy
  have hco : ∀ r : ℤ, y.coeff ((r : ℚ) / (p : ℚ) ^ L) =
      (X.exp (siegel X c ![(A₁ : ℚ) / M, ((N * g' : ℤ) : ℚ) / M])).coeff ((r : ℚ) / M) := fun r => by
    rw [← coeff_sgN X c hN M (A₁, N * g')]
    congr 1
    rw [hMq]; field_simp
  have c1 : ∀ n : ℕ, ε (y.coeff (((k + n : ℤ) : ℚ) / (p : ℚ) ^ L)) = a n := fun n => by
    rw [hco, ← r1]; push_cast; rfl
  have c0 : ∀ r : ℤ, r < k → y.coeff ((r : ℚ) / (p : ℚ) ^ L) = 0 := fun r hr => by
    rw [hco]
    refine r2 _ fun n h => ?_
    rw [div_left_inj' (by exact_mod_cast hM.ne')] at h
    have : r = k + n := by exact_mod_cast h
    omega
  have hb := HasQ.coeff_unique hM qb (by
    simpa only [neg_mul, one_mul] using ((GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne c M A₁ (N * g') hM).mul_conv qa).const_mul (-1))
  choose θ t1 t2 t3 using fun n => exists_finsupp (hj n)
  have cases : ∀ r : ℤ, r < k ∨ ∃ n : ℕ, r = k + n := fun r => by
    rcases lt_or_ge r k with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(r - k).toNat, by omega⟩
  set Θ : ℤ → ℤ → ℤ := fun l r => if r < k then 0 else θ (r - k).toNat l with hΘ
  have T0 : ∀ l r, r < k → Θ l r = 0 := fun l r h => if_pos h
  have T1 : ∀ l (n : ℕ), Θ l (k + n) = θ n l := fun l n => by
    simp only [hΘ]
    rw [if_neg (by omega), add_sub_cancel_left, Int.toNat_natCast]
  refine ⟨Θ, fun r => ?_, ⟨k, T0⟩, fun l r h => ?_, fun r => ?_, fun r => ?_, ?_, k, g * i, ?_⟩
  · rcases cases r with h | ⟨n, rfl⟩
    · exact ⟨0, fun l _ => T0 l r h⟩
    · refine ⟨(θ n).support.sup Int.natAbs, fun l hl => ?_⟩
      rw [T1]
      by_contra h
      have := Finset.le_sup (f := Int.natAbs) (Finsupp.mem_support_iff.2 h)
      rw [Int.abs_eq_natAbs] at hl
      omega
  · rcases cases r with h' | ⟨n, rfl⟩
    · exact absurd (T0 l r h') h
    · rw [T1] at h
      refine Dvd.dvd.trans ⟨N, ?_⟩ (t1 n l h)
      rw [hMd]; push_cast; ring
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp [c0 r h', T0 _ r h']
    · simp only [T1]
      apply ε.injective
      rw [c1, map_finsum_zpow ε (θ n) (fun _ m => m) (fun _ => rfl)]
      exact t2 n
  · rcases cases r with h' | ⟨n, rfl⟩
    · simp only [T0 _ r h', mul_zero, Int.cast_zero, zero_mul, finsum_zero]
      rw [finsum_eq_zero_of_forall_eq_zero, neg_zero]
      intro l
      split_ifs with h
      · rw [c0 _ (by omega), mul_zero]
      · rw [zero_mul]
    · simp only [T1]
      apply ε.injective
      rw [map_finsum_zpow ε (θ n) (fun l m => l * m) (fun _ => mul_zero _), ← t3 n,
        finsum_eq_sum_of_support_subset (s := (Finset.range (n + 1)).image (Nat.cast : ℕ → ℤ)),
        Finset.sum_image (fun _ _ _ _ h => by exact_mod_cast h), hb, map_neg, map_sum]
      · simp only [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, neg_inj]
        refine Finset.sum_congr rfl fun l hl => ?_
        have := Finset.mem_range.1 hl
        rw [map_mul, if_pos (by omega), Int.toNat_natCast, map_smF, eM, ← c1,
          show k + n - l = k + ((n - l : ℕ) : ℤ) by omega]
      · intro l hl
        by_contra h
        apply hl
        dsimp only
        split_ifs with h1
        · rw [c0, mul_zero]
          by_contra h2
          exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨l.toNat, Finset.mem_range.2 (by omega), by omega⟩))
        · rw [zero_mul]
  · have hz : eOm ε (1 / (M : ℚ)) ^ (N * g') = zt ε p L ^ g := ε.injective (by
      rw [map_zpow₀, map_zpow₀, ← hv, eM, ← ee_int_mul, mul_one_div])
    have m0 : zt ε p L ∈ Subring.closure {zt ε p L} := Subring.subset_closure rfl
    have m1 : (zt ε p L)⁻¹ ∈ Subring.closure {zt ε p L} := by
      have h1 : zt ε p L ^ (p ^ L) = 1 := ε.injective (by
        rw [map_pow, ez, map_one, ← zpow_natCast]; push_cast; exact hz1)
      have : (zt ε p L)⁻¹ = zt ε p L ^ (p ^ L - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (pow_pos hp0 L), h1]
      rw [this]
      exact pow_mem m0 _
    have m2 : ∀ m : ℤ, zt ε p L ^ m ∈ Subring.closure {zt ε p L} := fun m => by
      rcases Int.eq_nat_or_neg m with ⟨m, rfl | rfl⟩
      · rw [zpow_natCast]; exact pow_mem m0 _
      · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact pow_mem m1 _
    refine GlobalTheory.T.smoothedEisensteinFxCoefficientSeq_one_mem_subring Ω _ c M _ A₁ _ hM hcM hA (by rw [hz]; exact m2 _) ?_
    rw [zpow_neg, hz, ← zpow_neg]
    exact m2 _
  · have := c1 0
    rw [Nat.cast_zero, add_zero] at this
    refine hi.imp (fun h => ε.injective ?_) (fun h => ε.injective ?_)
    · rw [this, h, map_zpow₀, zpow_mul]
    · rw [this, h, map_neg, map_zpow₀, zpow_mul]

end GlobalTheory.SiegTwo
