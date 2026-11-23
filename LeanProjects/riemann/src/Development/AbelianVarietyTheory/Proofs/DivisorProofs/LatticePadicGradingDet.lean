import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt GlobalTheory.LieRead Matrix

namespace GlobalTheory.LieRead.CovolBasis

theorem norm_le_one_of_isIntegral_int {k : Type} [NormedField k] [IsUltrametricDist k] {y : k}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  have h : IsIntegral (NormedField.valuation (K := k)).integer y := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := k))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

theorem norm_natCast_of_not_dvd (p : ℕ) [Fact p.Prime] {s : ℕ} (h : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (s : ℚ_[p])
  rw [Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)] at h1
  simpa using h1

theorem iSup_norm_det_submatrix {C : Type} [NormedField C] {g : ℕ} (H : Matrix (Fin g) (Fin g) C) :
    (⨆ σ : Fin g → Fin g, ‖(H.submatrix σ id).det‖) = ‖H.det‖ := by
  haveI : Nonempty (Fin g → Fin g) := ⟨id⟩
  have hle : ∀ σ : Fin g → Fin g, ‖(H.submatrix σ id).det‖ ≤ ‖H.det‖ := by
    intro σ
    by_cases hσ : Function.Injective σ
    · have hb : Function.Bijective σ := Finite.injective_iff_bijective.mp hσ
      rw [show H.submatrix σ id = H.submatrix (Equiv.ofBijective σ hb) id from rfl, Matrix.det_permute]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.ofBijective σ hb)) with h | h <;> simp [h]
    · simp only [Function.Injective, not_forall] at hσ
      obtain ⟨a, b, hab, hne⟩ := hσ
      rw [Matrix.det_zero_of_row_eq hne (by ext; simp [hab])]
      simp
  apply le_antisymm (ciSup_le hle)
  exact le_ciSup (f := fun σ : Fin g → Fin g => ‖(H.submatrix σ id).det‖) (Set.finite_range _).bddAbove id

theorem sum_lnGrP_eq_neg_log_norm_det (K : Type) [Field K] [NumberField K] (g p : ℕ) [Fact p.Prime]
    (j : K →+* ℂ_[p]) (L : Submodule (𝓞 K) (Fin g → K)) (x : Fin g → Fin g → K) (s : ℕ)
    (hxL : ∀ i, x i ∈ L) (hx : LinearIndependent K x) (hs : ¬ p ∣ s)
    (hspan : ∀ v ∈ L, (s : K) • v ∈ Submodule.span (𝓞 K) (Set.range x)) :
    ∑ k : Fin g, lnGrP p j L k = - Real.log ‖j (Matrix.of fun i k => x k i).det‖ := by
  set X : Matrix (Fin g) (Fin g) K := Matrix.of fun i k => x k i with hXdef
  have hXdet : X.det ≠ 0 := by
    have hu : IsUnit (Matrix.of x) := (Matrix.linearIndependent_rows_iff_isUnit).1 hx
    have : X = (Matrix.of x)ᵀ := rfl
    rw [this, det_transpose]
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).1 hu))
  set B : Matrix (Fin g) (Fin g) ℂ_[p] := j.mapMatrix X with hBdef
  have hBdet : B.det = j X.det := (RingHom.map_det j X).symm
  have hBu : IsUnit B.det := by rw [hBdet]; exact isUnit_iff_ne_zero.2 ((map_ne_zero j).2 hXdet)
  set H := B⁻¹ with hHdef
  have hHB : H * B = 1 := nonsing_inv_mul B hBu
  have hBH : B * H = 1 := mul_nonsing_inv B hBu
  have hsC : ‖(s : ℂ_[p])‖ = 1 := norm_natCast_of_not_dvd p hs
  have hv : ∀ v ∈ L, ∀ i, ‖(H *ᵥ fun i => j (v i)) i‖ ≤ 1 := by
    intro v hvL i
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hspan v hvL)
    have hBb : B *ᵥ (fun k => j (b k : K)) = (s : ℂ_[p]) • fun i => j (v i) := by
      ext i'
      have := congrFun hb i'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [B, mulVec, dotProduct, RingHom.mapMatrix_apply, map_apply, X, of_apply, Pi.smul_apply, smul_eq_mul]
      rw [← map_natCast j s, ← map_mul, ← this, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def, ← map_mul, mul_comm]
    have h2 : (s : ℂ_[p]) • (H *ᵥ fun i => j (v i)) = fun k => j (b k : K) := by
      rw [← mulVec_smul, ← hBb, mulVec_mulVec, hHB, one_mulVec]
    have h3 := congrFun h2 i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    have h4 : ‖j (b i : K)‖ ≤ 1 :=
      norm_le_one_of_isIntegral_int (map_isIntegral_int j (RingOfIntegers.isIntegral_coe (b i)))
    rw [← h3, norm_mul, hsC, one_mul] at h4
    exact h4
  have hM : ∀ c : Fin g → ℂ_[p], (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧
      (∀ m, v m ∈ L) ∧ c = ∑ m, a m • fun i => j (v m i)) ↔ ∀ i, ‖(H *ᵥ c) i‖ ≤ 1 := by
    intro c
    constructor
    · rintro ⟨n, a, v, ha, hvL, rfl⟩ i
      rw [mulVec_sum]
      simp only [mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro m _
      rw [norm_mul]
      exact mul_le_one₀ (ha m) (norm_nonneg _) (hv _ (hvL m) i)
    · intro hc
      refine ⟨g, H *ᵥ c, x, hc, hxL, ?_⟩
      have : B *ᵥ (H *ᵥ c) = c := by rw [mulVec_mulVec, hBH, one_mulVec]
      conv_lhs => rw [← this]
      ext i
      simp [B, X, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hh : ∀ c : Fin g → ℂ_[p], (∀ jj, ∑ i, H jj i * c i = 0) → c = 0 := by
    intro c hc
    have h0 : H *ᵥ c = 0 := funext hc
    have : c = B *ᵥ (H *ᵥ c) := by rw [mulVec_mulVec, hBH, one_mulVec]
    rw [this, h0, mulVec_zero]
  set N : Fin g → ℝ := fun l => sInf {r : ℝ | ∃ c : Fin g → ℂ_[p], c l ≠ 0 ∧ (∀ i, l < i → c i = 0) ∧
    (∃ (n : ℕ) (a : Fin n → ℂ_[p]) (v : Fin n → Fin g → K), (∀ m, ‖a m‖ ≤ 1) ∧ (∀ m, v m ∈ L) ∧
      c = ∑ m, a m • fun i => j (v m i)) ∧ r = ‖c l‖⁻¹} with hNdef
  have hlnN : ∀ l, lnGrP p j L l = Real.log (N l) := fun l => rfl
  have hstd : ∀ (cf : Fin g → ℂ_[p]) i, ∑ l', cf l' * (Pi.single l' (1 : ℂ_[p]) : Fin g → ℂ_[p]) i = cf i := by
    intro cf i
    simp [Pi.single_apply]
  have hN : ∀ l, N l = sInf {r | ∃ cf : Fin g → ℂ_[p], cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      (∀ jj, ‖∑ i, H jj i * ∑ l', cf l' * (Pi.single l' (1 : ℂ_[p]) : Fin g → ℂ_[p]) i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := by
    intro l
    simp only [hNdef, hM, hstd]
    rfl
  have hli : LinearIndependent ℂ_[p] (fun l : Fin g => (Pi.single l (1 : ℂ_[p]) : Fin g → ℂ_[p])) := by
    convert (Pi.basisFun ℂ_[p] (Fin g)).linearIndependent using 1
    funext l
    exact (Pi.basisFun_apply ℂ_[p] (Fin g) l).symm
  obtain ⟨hpos, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor ℂ_[p] g (Fin g) (fun jj i => H jj i) hh g
    (fun l => (Pi.single l (1 : ℂ_[p]) : Fin g → ℂ_[p])) hli N hN
  have h1 := hprod g le_rfl
  have hsup : ∀ σ : Fin g → Fin g, ∑ s : Fin g → Fin g, (∏ i, H (σ i) (s i)) *
      GlobalTheory.LineNorm.minor (fun l => (Pi.single l (1 : ℂ_[p]) : Fin g → ℂ_[p])) le_rfl s = (H.submatrix σ id).det := by
    intro σ
    rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => H (σ i)) _ le_rfl, ← det_transpose]
    congr 1
    ext a b
    simp [Pi.single_apply]
  simp only [hsup] at h1
  rw [iSup_norm_det_submatrix] at h1
  have hprodN : ∏ l, N l = ‖H.det‖ := by rw [← h1]; rfl
  simp only [hlnN]
  rw [← Real.log_prod (fun l _ => (hpos l).ne'), hprodN, hHdef, det_nonsing_inv, Ring.inverse_eq_inv',
    norm_inv, Real.log_inv, hBdet]

end GlobalTheory.LieRead.CovolBasis
