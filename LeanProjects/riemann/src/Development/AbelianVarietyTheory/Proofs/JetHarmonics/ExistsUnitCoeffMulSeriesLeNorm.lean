import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulPowTwoLeTripleProdOfGe

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulDegree

section Lattice
open Module

set_option backward.isDefEq.respectTransparency false in

theorem relIndex_eq_abs_det {ι : Type} [Fintype ι] [DecidableEq ι] (b₁ b₂ : Basis ι ℝ ℂ) {L₁ L₂ : AddSubgroup ℂ}
    (h₁ : (Submodule.span ℤ (Set.range b₁)).toAddSubgroup = L₁)
    (h₂ : (Submodule.span ℤ (Set.range b₂)).toAddSubgroup = L₂) (h : L₁ ≤ L₂) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  subst h₁ h₂
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ h (b₁.restrictScalars ℤ) (b₂.restrictScalars ℤ),
    Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  have := b₂.restrictScalars_repr_apply ℤ
    ⟨b₁.restrictScalars ℤ j, h (Submodule.coe_mem _)⟩ i
  refine this.trans ?_
  simp

theorem relIndex_mul (L : PeriodPair) (β : ℂ) (N : ℕ) (hβ : β ≠ 0) (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice)
    (hN : (N : ℂ) = β * conj β) :
    (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft β)).relIndex L.lattice.toAddSubgroup = N := by
  let f : ℂ ≃ₗ[ℝ] ℂ := LinearEquiv.ofBijective (Algebra.lmul ℝ ℂ β)
    ⟨fun x y h => mul_left_cancel₀ hβ h, fun y => ⟨β⁻¹ * y, by simp [hβ]⟩⟩
  have hf : ∀ x, f x = β * x := fun _ => rfl
  have h := relIndex_eq_abs_det (L.basis.map f) L.basis
    (L₁ := L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft β)) (L₂ := L.lattice.toAddSubgroup) ?_
    (by rw [L.lattice_eq_span_range_basis]) (by rintro _ ⟨l, hl, rfl⟩; exact hL l hl)
  · have h2 : L.basis.det (L.basis.map f) = Complex.normSq β := by
      have := L.basis.det_comp (Algebra.lmul ℝ ℂ β) L.basis
      rw [Basis.det_self, mul_one, ← Algebra.norm_apply, Algebra.norm_complex_apply] at this
      exact this
    rw [h2, abs_of_nonneg (Complex.normSq_nonneg β)] at h
    rw [Complex.mul_conj] at hN
    have h3 : (N : ℝ) = Complex.normSq β := by exact_mod_cast hN
    exact_mod_cast h.trans h3.symm
  · ext x
    have e : Set.range (L.basis.map f) = (LinearMap.mulLeft ℤ β) '' Set.range L.basis := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, ← L.lattice_eq_span_range_basis]
    simp

theorem dvd_of_mem (L : PeriodPair) (K : ℕ) (hK : 0 < K) (m a b : ℤ)
    (h : (m : ℂ) / K * (a * L.ω₁ + b * L.ω₂) ∈ L.lattice) : (K : ℤ) ∣ m * a ∧ (K : ℤ) ∣ m * b := by
  obtain ⟨s, t, e⟩ := PeriodPair.mem_lattice.mp h
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  have e' : (K : ℂ) * (s * L.ω₁ + t * L.ω₂) = m * (a * L.ω₁ + b * L.ω₂) := by
    rw [e]; field_simp
  have := LinearIndependent.pair_iff.mp L.indep ((m * a - K * s : ℤ) : ℝ) ((m * b - K * t : ℤ) : ℝ)
    (by simp; linear_combination -e')
  obtain ⟨h1, h2⟩ := this
  have h1' : m * a - K * s = 0 := by exact_mod_cast h1
  have h2' : m * b - K * t = 0 := by exact_mod_cast h2
  exact ⟨⟨s, by linarith⟩, ⟨t, by linarith⟩⟩

theorem exists_points (L : PeriodPair) (β : ℂ) (hβ : β ≠ 0) (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice)
    (q n : ℕ) (hq : q.Prime) : ∃ (K : ℕ) (P : ℕ → ℂ), Nat.Coprime K q ∧ (∀ i, (K : ℂ) * P i ∈ L.lattice) ∧
      (∀ i < n, β * P i ∉ L.lattice) ∧
      ∀ i < n, ∀ j < n, i ≠ j → P i + P j ∉ L.lattice ∧ P i - P j ∉ L.lattice := by
  obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp (hL _ L.ω₁_mem_lattice)
  obtain ⟨K, hK, hKp⟩ := Nat.exists_infinite_primes (q + 2 * n + 2 + a.natAbs + b.natAbs + 1)
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hKp.pos.ne'
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  have small : ∀ m : ℤ, (K : ℤ) ∣ m → m.natAbs < K → m = 0 := fun m h1 h2 =>
    Int.eq_zero_of_abs_lt_dvd h1 (by rw [Int.abs_eq_natAbs]; exact_mod_cast h2)
  have hp : Prime (K : ℤ) := Nat.prime_iff_prime_int.mp hKp
  have one : ∀ m : ℤ, m ≠ 0 → m.natAbs < K → (m : ℂ) / K * L.ω₁ ∉ L.lattice := fun m h0 h1 h => by
    have := (dvd_of_mem L K hKp.pos m 1 0 (by simpa using h)).1
    exact h0 (small m (by simpa using this) h1)
  refine ⟨K, fun i => ((i + 1 : ℤ) : ℂ) / K * L.ω₁, (Nat.coprime_primes hKp hq).mpr (by omega), fun i => ?_,
    fun i hi h => ?_, fun i hi j hj hij => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact PeriodPair.mem_lattice.mpr ⟨i + 1, 0, by simp only; field_simp; simp⟩
  · have := dvd_of_mem L K hKp.pos (i + 1) a b (by rw [hab]; convert h using 1; ring)
    have h0 : ¬ (K : ℤ) ∣ (i + 1) := fun h => by have := small _ h (by omega); omega
    have ha := small a ((hp.dvd_or_dvd this.1).resolve_left h0) (by omega)
    have hb := small b ((hp.dvd_or_dvd this.2).resolve_left h0) (by omega)
    rw [ha, hb] at hab
    exact mul_ne_zero hβ hω (by simpa using hab.symm)
  · refine one (i + 1 + (j + 1)) (by omega) (by omega) ?_
    convert h using 1; push_cast; ring
  · refine one (i + 1 - (j + 1)) (by omega) (by omega) ?_
    convert h using 1; push_cast; ring

end Lattice

variable {q : ℕ} [Fact q.Prime]

theorem exists_rational (M : Mdl q) (hc : M.c ≠ 0) (β : ℂ) (N : ℕ) (hβ : β ≠ 0)
    (hL : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) (hN : (N : ℂ) = β * conj β) :
    ∃ A D : Polynomial ℂ, A.natDegree ≤ N ∧ D.natDegree ≤ N ∧ ∀ z, β * z ∉ M.L.lattice →
      D.eval (M.x z) ≠ 0 ∧ M.x (β * z) * D.eval (M.x z) = A.eval (M.x z) := by
  obtain ⟨A, D, -, -, -, -, -, hA, hD, h0, h⟩ := GlobalTheory.exists_weierstrassP_mul_eq_div hβ hL ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  rw [relIndex_mul M.L β N hβ hL hN] at hA
  set r := M.ι.symm (M.W.b₂ / 12) with hr
  let T : Polynomial ℂ := Polynomial.C (M.c ^ 2) * Polynomial.X + Polynomial.C (M.c ^ 2 * r)
  have hT : T.natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hTe : ∀ z, T.eval (M.x z) = M.L.weierstrassP z := fun z => by
    simp only [T, Mdl.x, ← hr, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    field_simp; ring
  have hdA : (A.comp T).natDegree ≤ N := Polynomial.natDegree_comp_le.trans (by nlinarith)
  have hdD : (D.comp T).natDegree ≤ N := Polynomial.natDegree_comp_le.trans (by nlinarith)
  refine ⟨Polynomial.C (M.c ^ 2)⁻¹ * A.comp T - Polynomial.C r * D.comp T, D.comp T, ?_, hdD, fun z hz => ?_⟩
  · exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_C_mul_le _ _).trans hdA)
      ((Polynomial.natDegree_C_mul_le _ _).trans hdD))
  · have hz' : z ∉ M.L.lattice := fun h => hz (hL z h)
    have hD0 : D.eval (M.L.weierstrassP z) ≠ 0 := fun e => hz ((h0 z hz').mp e)
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, hTe]
    refine ⟨hD0, ?_⟩
    rw [Mdl.x, ← hr, h z hz]
    field_simp

theorem norm_sub_le_of {x y : ℂ_[q]} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x - y‖ ≤ B := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rw [norm_neg, ← sub_eq_add_neg] at this
  exact this.trans (max_le hx hy)

theorem norm_add_le_of {x y : ℂ_[q]} {B : ℝ} (hx : ‖x‖ ≤ B) (hy : ‖y‖ ≤ B) : ‖x + y‖ ≤ B :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem coeff_le_of_values (B : ℝ) (hB : 0 ≤ B) (p : ℕ → ℂ_[q]) : ∀ (n : ℕ) (A : Polynomial ℂ_[q]), A.degree < n →
    (∀ i < n, ‖p i‖ ≤ 1) → (∀ i < n, ∀ j < n, i ≠ j → ‖p i - p j‖ = 1) → (∀ i < n, ‖A.eval (p i)‖ ≤ B) →
    ∀ k, ‖A.coeff k‖ ≤ B := by
  intro n
  induction n with
  | zero =>
    intro A hA _ _ _ k
    have : A = 0 := by
      by_contra h
      rw [Polynomial.degree_eq_natDegree h] at hA
      simp at hA
    simpa [this] using hB
  | succ n ih =>
    intro A hA h1 h2 h3 k
    by_cases h0 : A = 0
    · simpa [h0] using hB
    set A₁ := A /ₘ (Polynomial.X - Polynomial.C (p n)) with hA₁
    have e : A = Polynomial.C (A.eval (p n)) + (Polynomial.X - Polynomial.C (p n)) * A₁ := by
      rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval, hA₁, Polynomial.modByMonic_add_div]
    have hd : A₁.degree < n := by
      have h4 := Polynomial.degree_divByMonic_lt A (Polynomial.X - Polynomial.C (p n)) h0 (by simp)
      rw [Polynomial.degree_eq_natDegree h0] at hA h4
      have h5 : A.natDegree < n + 1 := by exact_mod_cast hA
      exact h4.trans_le (by exact_mod_cast Nat.lt_succ_iff.mp h5)
    have hc := ih A₁ hd (fun i hi => h1 i (by omega)) (fun i hi j hj => h2 i (by omega) j (by omega)) (fun i hi => by
      have e2 : (p i - p n) * A₁.eval (p i) = A.eval (p i) - A.eval (p n) := by
        conv_rhs => enter [1]; rw [e]
        simp
      have := norm_sub_le_of (h3 i (by omega)) (h3 n (by omega))
      rwa [← e2, norm_mul, h2 i (by omega) n (by omega) (by omega), one_mul] at this)
    rw [e, Polynomial.coeff_add, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
    refine norm_add_le_of ?_ (norm_sub_le_of ?_ ?_)
    · rw [Polynomial.coeff_C]; split_ifs
      · exact h3 n (by omega)
      · simpa using hB
    · cases k with
      | zero => simpa using hB
      | succ k => rw [Polynomial.coeff_X_mul]; exact hc k
    · rw [norm_mul]
      calc _ ≤ 1 * B := mul_le_mul (h1 n (by omega)) (hc k) (norm_nonneg _) zero_le_one
        _ = B := one_mul B

def BdT (n : ℕ) (B : ℝ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ m < n, ‖coeff m f‖ ≤ B

theorem BdT.mul {n : ℕ} {A B : ℝ} {f g : ℂ_[q]⟦X⟧} (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : BdT n A f) (hg : BdT n B g) :
    BdT n (A * B) (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  rw [norm_mul]
  exact mul_le_mul (hf _ (by omega)) (hg _ (by omega)) (norm_nonneg _) hA

theorem BdT.mul_one {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n 1 f) (hg : BdT n 1 g) : BdT n 1 (f * g) := by
  simpa using BdT.mul zero_le_one zero_le_one hf hg

theorem BdT.add {n : ℕ} {B : ℝ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n B f) (hg : BdT n B g) : BdT n B (f + g) :=
  fun m hm => by rw [map_add]; exact norm_add_le_of (hf m hm) (hg m hm)

theorem BdT.const {n : ℕ} {a : ℂ_[q]} (ha : ‖a‖ ≤ 1) : BdT n 1 (C a) := fun m _ => by
  rw [coeff_C]; split_ifs <;> simp [ha]

theorem BdT.of_bd {n : ℕ} {B : ℝ} {f : ℂ_[q]⟦X⟧} (hf : Bd B f) : BdT n B f := fun m _ => hf m

theorem BdT.sq {n : ℕ} {r : ℝ} {f : ℂ_[q]⟦X⟧} (hr : 0 ≤ r) (h1 : Bd 1 f) (hf : BdT n r f) :
    BdT (2 * n) r (f * f) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  rw [norm_mul]
  by_cases h : p.1 < n
  · simpa using mul_le_mul (hf _ h) (h1 p.2) (norm_nonneg _) hr
  · simpa using mul_le_mul (h1 p.1) (hf p.2 (by omega)) (norm_nonneg _) zero_le_one

theorem BdT.mul_succ {n : ℕ} {f g : ℂ_[q]⟦X⟧} (hf : BdT n 1 f) (hg : BdT n 1 g) (hf0 : constantCoeff f = 0)
    (hg0 : constantCoeff g = 0) : BdT (n + 1) 1 (f * g) := by
  intro m hm
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p hp
  have : p.1 + p.2 = m := by simpa using hp
  by_cases h1 : p.1 = 0
  · simp [h1, hf0]
  by_cases h2 : p.2 = 0
  · simp [h2, hg0]
  rw [norm_mul]
  exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))

theorem exists_cube (b w : ℂ_[q]⟦X⟧) (a₁ a₂ a₃ a₄ a₆ : ℂ_[q]) (h₁ : ‖a₁‖ ≤ 1) (h₂ : ‖a₂‖ ≤ 1) (h₃ : ‖a₃‖ ≤ 1)
    (h₄ : ‖a₄‖ ≤ 1) (h₆ : ‖a₆‖ ≤ 1) (hb : Bd 1 b) (hb0 : constantCoeff b = 0) (hw0 : constantCoeff w = 0)
    (e : w = b * b * b + w * (C a₁ * b + C a₂ * (b * b) + C a₃ * w + C a₄ * (b * w) + C a₆ * (w * w))) :
    ∃ v, Bd 1 v ∧ w = b * b * b * v := by
  set Q := C a₁ * b + C a₂ * (b * b) + C a₃ * w + C a₄ * (b * w) + C a₆ * (w * w) with hQ
  have hQ0 : constantCoeff Q = 0 := by simp [hQ, hb0, hw0]
  have hQb : ∀ n, BdT n 1 w → BdT n 1 Q := fun n hw =>
    ((((((BdT.const h₁).mul_one (.of_bd hb)).add ((BdT.const h₂).mul_one ((BdT.of_bd hb).mul_one (.of_bd hb)))).add
      ((BdT.const h₃).mul_one hw)).add ((BdT.const h₄).mul_one ((BdT.of_bd hb).mul_one hw))).add
      ((BdT.const h₆).mul_one (hw.mul_one hw)))
  have hw : ∀ n, BdT n 1 w := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      rw [e]
      exact (((BdT.of_bd hb).mul_one (.of_bd hb)).mul_one (.of_bd hb)).add (ih.mul_succ (hQb n ih) hw0 hQ0)
  have h1 : Bd 1 (1 - Q) := fun m => by
    rw [map_sub]
    refine norm_sub_le_of ?_ (hQb (m + 1) (hw _) m (by omega))
    rw [coeff_one]; split_ifs <;> simp
  have h0 : constantCoeff (1 - Q) = 1 := by simp [hQ0]
  have hi : (1 - Q) * (1 - Q)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [h0]; exact one_ne_zero)
  refine ⟨(1 - Q)⁻¹, (GlobalTheory.MomOne.sup_norm_laws q).2.2.1 _ _ h1 (by rw [h0]; simp) hi, ?_⟩
  linear_combination (1 - Q)⁻¹ * e - w * hi

theorem norm_le_of_bdT (xs : ℂ_[q]⟦X⟧) (k : ℕ) (c : ℕ → ℂ_[q]) (B : ℝ) (hx : Bd 1 xs) (h0 : ‖constantCoeff xs‖ = 1)
    (hB : BdT (2 * k + 1) B (∑ i ∈ Finset.range (k + 1), C (c i) * X ^ (2 * (k - i)) * xs ^ i)) :
    ∀ i ≤ k, ‖c i‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega))
  suffices h : ∀ n, ∀ j ≤ k, k - j = n → ‖c j‖ ≤ B from fun j hj => h _ j hj rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro j hj hn
    have h1 := hB (2 * n) (by omega)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)), map_add, map_sum, mul_assoc,
      coeff_C_mul, coeff_X_pow_mul', if_pos (by omega), hn, Nat.sub_self, coeff_zero_eq_constantCoeff] at h1
    have h2 : ‖∑ l ∈ (Finset.range (k + 1)).erase j, coeff (2 * n) (C (c l) * X ^ (2 * (k - l)) * xs ^ l)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 ?_
      intro l hl
      obtain ⟨hlj, hls⟩ := Finset.mem_erase.mp hl
      have hls' := Finset.mem_range.mp hls
      rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
      split_ifs with hle
      · rw [norm_mul]
        simpa using mul_le_mul (ih (k - l) (by omega) l (by omega) rfl) (Triang.bd_one_pow hx l _) (norm_nonneg _) hB0
      · simpa using hB0
    have h3 := norm_sub_le_of h1 h2
    rwa [add_sub_cancel_right, norm_mul, map_pow, norm_pow, h0, one_pow, mul_one] at h3

theorem bd_sum (xs : ℂ_[q]⟦X⟧) (k : ℕ) (c : ℕ → ℂ_[q]) (B : ℝ) (hB : 0 ≤ B) (hx : Bd 1 xs) (hc : ∀ i, ‖c i‖ ≤ B) :
    Bd B (∑ i ∈ Finset.range (k + 1), C (c i) * X ^ (2 * (k - i)) * xs ^ i) := by
  intro m
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB ?_
  intro l _
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hle
  · rw [norm_mul]
    simpa using mul_le_mul (hc l) (Triang.bd_one_pow hx l _) (norm_nonneg _) hB
  · simpa using hB

theorem hat_equation (M : Mdl q) (hM : M.Ok) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    let b := hat M.ι ℓ M.u
    let w := hat M.ι ℓ M.w
    w = b * b * b + w * (C M.W.a₁ * b + C M.W.a₂ * (b * b) + C M.W.a₃ * w + C M.W.a₄ * (b * w) +
      C M.W.a₆ * (w * w)) := by
  intro b w
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hM
  obtain ⟨hu, hw, -, -, -, he⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨H, hc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  have hadd := fun F G hF hG => (H F G hF hG).1
  have hmul := fun F G hF hG => (H F G hF hG).2.1
  have h1 := (H M.w (fun z => M.u z * M.u z * M.u z + M.w z * (M.ι.symm M.W.a₁ * M.u z +
    M.ι.symm M.W.a₂ * (M.u z * M.u z) + M.ι.symm M.W.a₃ * M.w z + M.ι.symm M.W.a₄ * (M.u z * M.w z) +
    M.ι.symm M.W.a₆ * (M.w z * M.w z))) hw (by fun_prop)).2.2.1 (by
      filter_upwards [nhdsWithin_le_nhds he] with z hz
      linear_combination hz.1)
  simp (disch := fun_prop) only [hadd, hmul, hc, RingEquiv.apply_symm_apply] at h1
  exact h1

theorem exists_unit_coeff : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (β : ℂ) (N : ℕ), M.Chart ℓ → β ≠ 0 → (∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice) → (N : ℂ) = β * conj β → Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) → ∃ n ≤ N, ‖coeff n (hat M.ι ℓ (fun z => M.u (β * z)))‖ = 1 := by
  intro q hq M ℓ β N hch hβ hL hN hb
  by_contra hcon
  push Not at hcon
  have hM := hch.1
  have hℓ := hch.2.1
  obtain ⟨hc, h₁, h₂, h₃, h₄, h₆, -⟩ := id hM
  obtain ⟨A, D, hA, hD, hAD⟩ := exists_rational M hc β N hβ hL hN
  obtain ⟨hℓ1, v, xs, ys, -, hxs, -, -, hxs0, -, -, -, -, hxy⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hch
  obtain ⟨-, -, -, -, hu0, hw0, hu', -, hs⟩ := GlobalTheory.MomOne.uw_elliptic_flow q M hM
  obtain ⟨hu, hw, -, -, hev, -⟩ := hs 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, -, -, hsc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι ℓ hℓ
  have hℓ' : constantCoeff (C (M.ι β) * ℓ) = 0 := by simp [hℓ]
  obtain ⟨H', hc', -, hcc', -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hℓ'

  have hub : AnalyticAt ℂ (fun z => M.u (β * z)) 0 :=
    AnalyticAt.comp (g := M.u) (f := fun z => β * z) (by simpa using hu) (by fun_prop)
  have hwb : AnalyticAt ℂ (fun z => M.w (β * z)) 0 :=
    AnalyticAt.comp (g := M.w) (f := fun z => β * z) (by simpa using hw) (by fun_prop)
  have ht : Filter.Tendsto (fun z : ℂ => β * z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Filter.Tendsto (fun z : ℂ => β * z) (𝓝 0) (𝓝 (β * 0)) := (by fun_prop : Continuous _).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_ne_zero hβ hz
  have key := hxy _ A 0 N hub hA (by simp) _ hwb D N hD (by
    filter_upwards [ht.eventually hev] with z hz
    have := (hAD z hz.1).2
    simp only [Polynomial.eval_zero, zero_mul, add_zero]
    rw [← this, ← hz.2.2.1]; ring)
  rw [hsc _ β hu] at hb hcon key
  rw [hsc _ β hw] at key
  set b := hat M.ι (C (M.ι β) * ℓ) M.u with hbdef
  set w := hat M.ι (C (M.ι β) * ℓ) M.w with hwdef
  obtain ⟨e, he, hwe⟩ := exists_cube b w _ _ _ _ _ h₁ h₂ h₃ h₄ h₆ hb (by rw [hbdef, hcc', hu0, map_zero])
    (by rw [hwdef, hcc', hw0, map_zero]) (hat_equation M hM _ hℓ')
  have hb0 : b ≠ 0 := fun h0 => by
    have := (H' M.u (fun _ => 0) hu (by fun_prop)).2.2.2 (by simp [hβ, hℓ1]) (by rw [hc', ← hbdef, h0]; simp)
    have := this.deriv_eq
    rw [hu'] at this
    exact hc (by simpa using this)
  set Dh := ∑ i ∈ Finset.range (N + 1), C (M.ι (D.coeff i)) * X ^ (2 * (N - i)) * xs ^ i with hDh
  set Ah := ∑ i ∈ Finset.range (N + 1), C (M.ι (A.coeff i)) * X ^ (2 * (N - i)) * xs ^ i with hAh
  have hsum : ∑ i ∈ Finset.range (N + 1), (C (M.ι (A.coeff i)) * X ^ (2 * (N - i) + 3) * xs ^ i +
      C (M.ι ((0 : Polynomial ℂ).coeff i)) * X ^ (2 * (N - i)) * xs ^ i * ys) = X ^ 3 * Ah := by
    rw [hAh, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Polynomial.coeff_zero, map_zero, zero_mul, add_zero]
    ring
  rw [hsum, hwe] at key
  have key2 : Dh = b * b * (e * Ah) := by
    refine mul_left_cancel₀ (mul_ne_zero hb0 (pow_ne_zero (2 * N + 3) X_ne_zero)) ?_
    rw [key]; ring

  obtain ⟨n, hn, hnmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun n => ‖coeff n b‖) (by simp)
  have hr : ‖coeff n b‖ < 1 := lt_of_le_of_ne (hb n) (hcon n (by simpa [Nat.lt_succ_iff] using hn))
  obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) (fun n => ‖M.ι (D.coeff n)‖) (by simp)
  have hDc : ∀ i, ‖M.ι (D.coeff i)‖ ≤ ‖M.ι (D.coeff m)‖ := fun i => by
    by_cases hi : i ≤ N
    · exact hmmax i (by simpa [Nat.lt_succ_iff] using hi)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp

  obtain ⟨K, P, hK, hKP, hβP, hPP⟩ := exists_points M.L β hβ hL q (N + 1) hq.out
  obtain ⟨hint, hdist⟩ := GlobalTheory.MomOne.TorsionReduction.torsion_integral_and_distinct q M K hM hK
  have hP : ∀ i < N + 1, P i ∉ M.L.lattice := fun i hi h => hβP i hi (hL _ h)
  have hAc : ∀ i, ‖M.ι (A.coeff i)‖ ≤ ‖M.ι (D.coeff m)‖ := by
    have := coeff_le_of_values ‖M.ι (D.coeff m)‖ (norm_nonneg _) (fun i => M.ι (M.x (P i))) (N + 1)
      (A.map (M.ι : ℂ →+* ℂ_[q]))
      (Polynomial.degree_map_le.trans_lt (Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast by omega)))
      (fun i hi => hint _ (hKP i) (hP i hi))
      (fun i hi j hj hij => hdist _ _ (hKP i) (hKP j) (hP i hi) (hP j hj) (hPP i hi j hj hij).1 (hPP i hi j hj hij).2)
      (fun i hi => ?_)
    · simpa using this
    · have e1 : (A.map (M.ι : ℂ →+* ℂ_[q])).eval (M.ι (M.x (P i))) = M.ι (A.eval (M.x (P i))) :=
        Polynomial.eval_map_apply (p := A) (M.ι : ℂ →+* ℂ_[q]) (M.x (P i))
      rw [e1, ← (hAD _ (hβP i hi)).2, map_mul, norm_mul]
      have e2 : ‖M.ι (M.x (β * P i))‖ ≤ 1 := hint _ (by rw [mul_left_comm]; exact hL _ (hKP i)) (hβP i hi)
      have e3 : ‖M.ι (D.eval (M.x (P i)))‖ ≤ ‖M.ι (D.coeff m)‖ := by
        rw [Polynomial.eval_eq_sum_range, map_sum]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
        rw [map_mul, map_pow, norm_mul, norm_pow]
        simpa using mul_le_mul (hDc l) (pow_le_one₀ (norm_nonneg _) (hint _ (hKP i) (hP i hi)) (n := l))
          (by positivity) (norm_nonneg _)
      simpa using mul_le_mul e2 e3 (norm_nonneg _) zero_le_one
  have hAh' : Bd ‖M.ι (D.coeff m)‖ Ah := bd_sum xs N _ _ (norm_nonneg _) hxs hAc
  have hbb : BdT (2 * (N + 1)) ‖coeff n b‖ (b * b) :=
    BdT.sq (norm_nonneg _) hb fun i hi => hnmax i (by simpa using hi)
  have hfin := hbb.mul (norm_nonneg _) (by positivity)
    ((BdT.of_bd he).mul zero_le_one (norm_nonneg _) (BdT.of_bd hAh'))
  rw [← key2, one_mul] at hfin
  have h5 := norm_le_of_bdT xs N (fun i => M.ι (D.coeff i)) _ hxs hxs0 (fun i hi => hfin i (by omega)) m
    (by simpa [Nat.lt_succ_iff] using hm)
  have h6 : ‖M.ι (D.coeff m)‖ ≤ 0 := by nlinarith [norm_nonneg (M.ι (D.coeff m))]
  have hD0 : D = 0 := by
    ext i
    simpa using (hDc i).trans h6
  exact (hAD _ (hβP 0 (by omega))).1 (by simp [hD0])

end GlobalTheory.MomOne.MulDegree
