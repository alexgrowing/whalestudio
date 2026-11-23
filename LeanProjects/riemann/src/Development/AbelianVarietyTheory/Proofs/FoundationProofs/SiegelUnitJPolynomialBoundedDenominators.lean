import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerAnEqSiegelUnitOnComplex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitQExpansionCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique

noncomputable section

open scoped MatrixGroups UpperHalfPlane
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.Sieg

namespace GlobalTheory.FracBd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def Good (F : HahnSeries ℚ Ω) : Prop :=
  ∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, F.coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
    IsIntegral ℤ ((D : Ω) * F.coeff r)

theorem isIntegral_natCast' (n : ℕ) : IsIntegral ℤ (n : Ω) := by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := (n : ℤ)))

theorem adj_mono {S S' : Finset Ω} (h : S ⊆ S') :
    IntermediateField.adjoin ℚ (S : Set Ω) ≤ IntermediateField.adjoin ℚ (S' : Set Ω) :=
  IntermediateField.adjoin.mono ℚ _ _ (Finset.coe_subset.2 h)

theorem good_add {F G : HahnSeries ℚ Ω} (hF : Good F) (hG : Good G) : Good (F + G) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hF
  obtain ⟨S', D', hD', h'⟩ := hG
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ⟨?_, ?_⟩⟩
  · rw [HahnSeries.coeff_add]
    exact add_mem (adj_mono Finset.subset_union_left (h r).1) (adj_mono Finset.subset_union_right (h' r).1)
  · rw [HahnSeries.coeff_add]
    have e : ((D * D' : ℕ) : Ω) * (F.coeff r + G.coeff r) =
        (D' : Ω) * ((D : Ω) * F.coeff r) + (D : Ω) * ((D' : Ω) * G.coeff r) := by push_cast; ring
    rw [e]
    exact ((isIntegral_natCast' D').mul (h r).2).add ((isIntegral_natCast' D).mul (h' r).2)

theorem good_mul {F G : HahnSeries ℚ Ω} (hF : Good F) (hG : Good G) : Good (F * G) := by
  classical
  obtain ⟨S, D, hD, h⟩ := hF
  obtain ⟨S', D', hD', h'⟩ := hG
  refine ⟨S ∪ S', D * D', Nat.mul_pos hD hD', fun r => ⟨?_, ?_⟩⟩
  · rw [HahnSeries.coeff_mul]
    exact sum_mem fun ij _ => mul_mem (adj_mono Finset.subset_union_left (h ij.1).1)
      (adj_mono Finset.subset_union_right (h' ij.2).1)
  · rw [HahnSeries.coeff_mul, Finset.mul_sum]
    refine IsIntegral.sum _ fun ij _ => ?_
    have e : ((D * D' : ℕ) : Ω) * (F.coeff ij.1 * G.coeff ij.2) =
        ((D : Ω) * F.coeff ij.1) * ((D' : Ω) * G.coeff ij.2) := by push_cast; ring
    rw [e]
    exact (h ij.1).2.mul (h' ij.2).2

theorem good_C [Algebra.IsAlgebraic ℚ Ω] (c : Ω) : Good (algebraMap Ω (HahnSeries ℚ Ω) c) := by
  classical
  have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy0, hy⟩ := hc.exists_integral_multiple
  have hyc : IsIntegral ℤ ((y.natAbs : Ω) * c) := by
    rw [zsmul_eq_mul] at hy
    rcases Int.natAbs_eq y with e | e
    · rw [e] at hy; simpa using hy
    · rw [e] at hy
      have := hy.neg
      simpa using this
  refine ⟨{c}, y.natAbs, Int.natAbs_pos.2 hy0, fun r => ?_⟩
  have hcoef : (algebraMap Ω (HahnSeries ℚ Ω) c).coeff r = if r = 0 then c else 0 := by
    have e : algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := by
      rw [HahnSeries.algebraMap_apply']
      simp
    rw [e]
    by_cases hr : r = 0 <;> simp [hr]
  rw [hcoef]
  split_ifs
  · exact ⟨IntermediateField.subset_adjoin ℚ _ (by simp), hyc⟩
  · exact ⟨zero_mem _, by simpa using (isIntegral_zero : IsIntegral ℤ (0 : Ω))⟩

theorem good_int {F : HahnSeries ℚ Ω} (h : ∀ r, ∃ n : ℤ, F.coeff r = n) : Good F := by
  refine ⟨∅, 1, one_pos, fun r => ?_⟩
  obtain ⟨n, hn⟩ := h r
  rw [hn]
  refine ⟨intCast_mem _ n, ?_⟩
  simpa using (isIntegral_algebraMap (R := ℤ) (A := Ω) (x := n))

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

open GlobalTheory.QFam

theorem shift_hasQ {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (h : HasQ N f a) (d : ℕ) :
    HasQ N (fun τ => f τ * ee ((d : ℂ) / N * (τ : ℂ))) (fun n => if d ≤ n then a (n - d) else 0) := by
  intro τ
  have h1 := (h τ).mul_right (ee ((d : ℂ) / N * (τ : ℂ)))
  rw [← hasSum_nat_add_iff' d]
  have hz : ∑ i ∈ Finset.range d, (if d ≤ i then a (i - d) else 0) *
      Complex.exp (2 * Real.pi * Complex.I * (i : ℂ) * τ / N) = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [not_le.2 (Finset.mem_range.1 hi)]
  rw [hz, sub_zero]
  convert h1 using 2 with n
  case e'_5 =>
    simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, ee]
    rw [mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  all_goals rfl

theorem coeff_cmp {N : ℕ} (hN : 0 < N) {g : ℍ → ℂ} {k k' : ℤ} {A B : ℕ → ℂ}
    (hA : HasQ N (fun τ => g τ * ee (-((k : ℂ) / N) * (τ : ℂ))) A)
    (hB : HasQ N (fun τ => g τ * ee (-((k' : ℂ) / N) * (τ : ℂ))) B) (n : ℕ) :
    B n = 0 ∨ ∃ m, B n = A m := by
  rcases le_total k k' with hk | hk
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, k' = k + d := ⟨(k' - k).toNat, by omega⟩
    have hS := shift_hasQ hB d
    have e : (fun τ : ℍ => g τ * ee (-(((k + d : ℤ) : ℂ) / N) * (τ : ℂ)) * ee ((d : ℂ) / N * (τ : ℂ))) =
        fun τ => g τ * ee (-((k : ℂ) / N) * (τ : ℂ)) := by
      funext τ
      simp only [ee]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e] at hS
    have := HasQ.coeff_unique hN hA hS
    right
    refine ⟨n + d, ?_⟩
    rw [this]
    simp
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ, k = k' + d := ⟨(k - k').toNat, by omega⟩
    have hS := shift_hasQ hA d
    have e : (fun τ : ℍ => g τ * ee (-(((k' + d : ℤ) : ℂ) / N) * (τ : ℂ)) * ee ((d : ℂ) / N * (τ : ℂ))) =
        fun τ => g τ * ee (-((k' : ℂ) / N) * (τ : ℂ)) := by
      funext τ
      simp only [ee]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [e] at hS
    have := HasQ.coeff_unique hN hB hS
    rw [this]
    by_cases h : d ≤ n
    · right; exact ⟨n - d, by simp [h]⟩
    · left; simp [h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem eps_zeta [IsAlgClosed Ω] (ε : Ω →+* ℂ) {M : ℕ} (hM : 0 < M) :
    ε (eOm ε (1 / (M : ℚ))) = ee (1 / (M : ℂ)) := by
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (M : ℚ)) : ℚ) : ℂ)) = ee (1 / (M : ℂ)) := by
    unfold ee; push_cast; rfl
  unfold eOm
  rw [e]
  exact Function.invFun_eq (GlobalTheory.KZ.SiegelMem.mem_range_of_isIntegral ε (GlobalTheory.KZ.SiegelMem.isIntegral_ee hM))

theorem mem_closure_of_eps (ε : Ω →+* ℂ) {ζ x : Ω} (h : ε x ∈ Subring.closure {ε ζ}) : x ∈ Subring.closure {ζ} := by
  rw [← Set.image_singleton, ← RingHom.map_closure] at h
  obtain ⟨y, hy, hyx⟩ := Subring.mem_map.1 h
  rwa [← ε.injective hyx]

theorem admissible_of_integral_conj_le {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c) (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) {a b : ℤ}
    (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) : admitted c ![(a : ℚ) / M, (b : ℚ) / M] := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcop : IsCoprime (M : ℤ) (c : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    have := hcM.gcd_eq
    rw [Nat.gcd_one_left] at this
    exact Nat.Coprime.symm this
  have key : ∀ x : ℤ, (c : ℚ) * ((x : ℚ) / M) ∈ Set.range ((↑) : ℤ → ℚ) → (M : ℤ) ∣ x := by
    rintro x ⟨m, hm⟩
    have h1 : (M : ℤ) * m = x * c := by
      have : (M : ℚ) * m = x * c := by rw [hm]; field_simp
      exact_mod_cast this
    exact hcop.dvd_of_dvd_mul_right ⟨m, h1.symm⟩
  exact ⟨hc1, hc6, fun ⟨h0, h1⟩ => hab ⟨key a h0, key b h1⟩⟩

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

open GlobalTheory.QFam

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem siegel_coeff [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c)
    (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ) (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b)) (r : ℚ) :
    (X.exp (siegel X c ![(a : ℚ) / M, (b : ℚ) / M])).coeff r ∈ Subring.closure {eOm ε (1 / (M : ℚ))} := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hcop : Nat.Coprime c M := by
    have := hcM.gcd_eq
    rwa [Nat.gcd_one_left] at this
  set a0 : ℕ := (a % (M : ℤ)).toNat with ha0
  set b0 : ℕ := (b % (M : ℤ)).toNat with hb0
  have ha0' : (a0 : ℤ) = a % M := Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)
  have hb0' : (b0 : ℤ) = b % M := Int.toNat_of_nonneg (Int.emod_nonneg _ hMz)
  have hlt : a0 < M := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hM : (0 : ℤ) < M)
    omega
  have hqa : (a : ℚ) = (M : ℚ) * ((a / (M : ℤ) : ℤ) : ℚ) + (a0 : ℚ) := by
    have h : a = (M : ℤ) * (a / (M : ℤ)) + (a0 : ℤ) := by linarith [Int.emod_def a (M : ℤ), ha0']
    exact_mod_cast h
  have hqb : (b : ℚ) = (M : ℚ) * ((b / (M : ℤ) : ℤ) : ℚ) + (b0 : ℚ) := by
    have h : b = (M : ℤ) * (b / (M : ℤ)) + (b0 : ℤ) := by linarith [Int.emod_def b (M : ℤ), hb0']
    exact_mod_cast h
  have hab0 : ¬ ((M : ℤ) ∣ (a0 : ℤ) ∧ (M : ℤ) ∣ (b0 : ℤ)) := by
    rintro ⟨h1, h2⟩
    apply hab
    rw [ha0'] at h1
    rw [hb0'] at h2
    exact ⟨(Int.dvd_iff_emod_eq_zero).2 (by have := Int.emod_emod_of_dvd a (dvd_refl (M : ℤ)); omega),
      (Int.dvd_iff_emod_eq_zero).2 (by have := Int.emod_emod_of_dvd b (dvd_refl (M : ℤ)); omega)⟩
  have hadm : admitted c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    have := admissible_of_integral_conj_le hM hc1 hc6 hcM hab0
    simpa using this
  set n : Fin 2 → ℤ := ![a / (M : ℤ), b / (M : ℤ)] with hn
  have hx : (![(a : ℚ) / M, (b : ℚ) / M] : Fin 2 → ℚ) = fun i => (![(a0 : ℚ) / M, (b0 : ℚ) / M] : Fin 2 → ℚ) i + n i := by
    funext i
    fin_cases i
    · simp only [n, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [hqa]; field_simp; ring
    · simp only [n, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hqb]; field_simp; ring
  have hsg : sgC c ![(a : ℚ) / M, (b : ℚ) / M] = sgC c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    funext z
    unfold sgC
    rw [hx]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c _ n _ hadm
  have hsie : siegel X c ![(a : ℚ) / M, (b : ℚ) / M] = siegel X c ![(a0 : ℚ) / M, (b0 : ℚ) / M] := by
    unfold siegel
    rw [hsg]
  rw [hsie]
  obtain ⟨k, A, hQ, hc, hz⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε X c M a0 b0 hM hlt hadm
  obtain ⟨k', hk'⟩ := GlobalTheory.T.smoothedSiegelUnit_qExpansion_coeffs_integral c M a0 hM hlt
  obtain ⟨A', hQ', -, -, hA', -⟩ := hk' b0 hadm
  have hAn : ∀ m, A m ∈ Subring.closure {eOm ε (1 / (M : ℚ))} := by
    intro m
    apply mem_closure_of_eps ε
    rw [eps_zeta ε hM]
    rcases coeff_cmp hM hQ' hQ m with h | ⟨m', h⟩
    · rw [show ε (A m) = 0 from h]; exact zero_mem _
    · rw [show ε (A m) = A' m' from h]; exact hA' hcop m'
  by_cases hr : ∃ m : ℕ, r = ((k : ℚ) + m) / M
  · obtain ⟨m, rfl⟩ := hr
    rw [hc m]
    exact hAn m
  · push_neg at hr
    rw [hz r hr]
    exact zero_mem _

end GlobalTheory.FracBd

namespace GlobalTheory.FracBd

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem good_closure {F : HahnSeries ℚ Ω} {ζ : Ω} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1)
    (h : ∀ r, F.coeff r ∈ Subring.closure {ζ}) : Good F := by
  classical
  have hi : IsIntegral ℤ ζ := IsIntegral.of_pow hM (by rw [hζ]; exact isIntegral_one)
  have h1 : Subring.closure {ζ} ≤ (IntermediateField.adjoin ℚ (({ζ} : Finset Ω) : Set Ω)).toSubring :=
    Subring.closure_le.2 (by simpa using IntermediateField.subset_adjoin ℚ ({ζ} : Set Ω))
  have h2 : Subring.closure {ζ} ≤ (integralClosure ℤ Ω).toSubring :=
    Subring.closure_le.2 (by simpa [mem_integralClosure_iff] using hi)
  refine ⟨{ζ}, 1, one_pos, fun r => ⟨h1 (h r), ?_⟩⟩
  simpa [mem_integralClosure_iff] using h2 (h r)

theorem good_siegel [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) {M c : ℕ} (hM : 0 < M) (hc1 : 1 < c)
    (hc6 : Nat.Coprime c 6) (hcM : c ≡ 1 [MOD M]) (a b : ℤ) (hab : ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b))
    (γ : SL(2, ℤ)) : Good (X.exp (X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]))) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c _ γ (admissible_of_integral_conj_le hM hc1 hc6 hcM hab)]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this
  set a' : ℤ := a * γ 0 0 + b * γ 1 0 with ha'
  set b' : ℤ := a * γ 0 1 + b * γ 1 1 with hb'
  have hact : act ![(a : ℚ) / M, (b : ℚ) / M] γ = ![(a' : ℚ) / M, (b' : ℚ) / M] := by
    funext i
    fin_cases i
    · simp [act, Fin.sum_univ_two, a']
      field_simp
    · simp [act, Fin.sum_univ_two, b']
      field_simp
  have hab' : ¬ ((M : ℤ) ∣ a' ∧ (M : ℤ) ∣ b') := by
    rintro ⟨h1, h2⟩
    apply hab
    have ea : a = a' * γ 1 1 - b' * γ 1 0 := by simp only [a', b']; linear_combination (-a) * hdet
    have eb : b = b' * γ 0 0 - a' * γ 0 1 := by simp only [a', b']; linear_combination (-b) * hdet
    exact ⟨ea ▸ dvd_sub (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_left h2 _),
      eb ▸ dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)⟩
  rw [hact]
  have hζ : eOm ε (1 / (M : ℚ)) ^ M = 1 := by
    apply ε.injective
    rw [map_pow, eps_zeta ε hM, map_one]
    unfold ee
    rw [← Complex.exp_nat_mul]
    have : (M : ℂ) * (2 * Real.pi * Complex.I * (1 / M)) = 2 * Real.pi * Complex.I := by
      have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  exact good_closure hM hζ (siegel_coeff ε X hM hc1 hc6 hcM a' b' hab')

theorem frac_bd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε),
    ∀ (M c : ℕ), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] →
    ∀ f ∈ Algebra.adjoin Ω ({X.jK} ∪ {g | ∃ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      g = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]}), ∀ γ : SL(2, ℤ),
    (∃ (S : Finset Ω) (D : ℕ), 0 < D ∧ ∀ r, (X.exp (X.sl (ofSL γ) f)).coeff r ∈ IntermediateField.adjoin ℚ (S : Set Ω) ∧
      IsIntegral ℤ ((D : Ω) * (X.exp (X.sl (ofSL γ) f)).coeff r)) := by
  intro Ω _ _ _ ε X M c hM hc1 hc6 hcM f hf γ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  show Good (X.exp (X.sl (ofSL γ) f))
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨a, b, hab, rfl⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [X.j_inv γ]
      exact good_int X.j_exp.2.2
    · exact good_siegel ε X hM hc1 hc6 hcM a b hab γ
  | algebraMap r =>
    rw [AlgEquiv.commutes, AlgHom.commutes]
    exact good_C r
  | add x y _ _ hx hy =>
    rw [map_add, map_add]
    exact good_add hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    exact good_mul hx hy

end GlobalTheory.FracBd
