import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInversePolynomialBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

lemma fmul_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) :
    fmul k r z 1 b = fvec k r z b := by
  simp [fmul, Matrix.one_apply]

lemma frame_mulVec_fmul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {σ : B.Mat k r}
    {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (h : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (c : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) :
    σ *ᵥ fmul k r z c b = fmul k r z (v * c) b := by
  show σ *ᵥ (∑ a, c a b • fvec k r z a) = ∑ a, (v * c) a b • fvec k r z a
  rw [← Matrix.mulVecLin_apply, map_sum]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_smul, h, fmul, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (c a b)]

lemma ut_det {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v.det = 1 := by
  rw [Matrix.det_of_upperTriangular hv.1]
  simp [hv.2]

lemma ut_mul_inv {m : ℕ} {v : Matrix (Fin m) (Fin m) ℂ} (hv : v ∈ UTset m) : v * v⁻¹ = 1 := Matrix.mul_nonsing_inv v (by rw [ut_det hv]; exact isUnit_one)

lemma mx_nonneg {m : ℕ} (v : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ mx v := norm_nonneg _

lemma real_sq_bound {C CA m n x : ℝ} {e : ℕ} (hm : 0 ≤ m) (hmx : m ≤ CA * x ^ e) (hx : 1 ≤ x)
    (hn : n ≤ C * m ^ 2) : n ≤ |C| * CA ^ 2 * x ^ (2 * e) := by
  have h1 : m ^ 2 ≤ (CA * x ^ e) ^ 2 := pow_le_pow_left₀ hm hmx 2
  have h2 : C * m ^ 2 ≤ |C| * m ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg m)
  calc n ≤ C * m ^ 2 := hn
    _ ≤ |C| * m ^ 2 := h2
    _ ≤ |C| * (CA * x ^ e) ^ 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * CA ^ 2 * x ^ (2 * e) := by ring

lemma add_le_mul_pow_of_sq_le_of_le_mul {Cc D a s sp x : ℝ} {e N : ℕ} (hD : 0 ≤ D) (ha : 0 ≤ a) (hs1 : 1 ≤ s) (hx : 1 ≤ x)
    (hs : s ^ 2 ≤ Cc * (1 + D * x ^ (2 * e + 2)) ^ 2) (hsp : sp ≤ a * s * x) (hN : 4 * e + 5 ≤ N) :
    s + sp ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ s := by linarith
  set K := 2 * e + 2 with hK
  have hxK : 1 ≤ x ^ K := one_le_pow₀ hx
  have hA : 1 + D * x ^ K ≤ (1 + D) * x ^ K := by nlinarith
  have hA0 : 0 ≤ 1 + D * x ^ K := by nlinarith
  have hs_le : s ≤ s ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 := by
    calc s ^ 2 ≤ Cc * (1 + D * x ^ K) ^ 2 := hs
      _ ≤ |Cc| * (1 + D * x ^ K) ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |Cc| * ((1 + D) * x ^ K) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA0 hA 2) (abs_nonneg _)
  have hsx : s ≤ |Cc| * (1 + D) ^ 2 * x ^ (2 * K) := by
    have e2 : ((1 + D) * x ^ K) ^ 2 = (1 + D) ^ 2 * x ^ (2 * K) := by ring
    rw [e2] at hs2
    nlinarith
  have hxN : x ^ (2 * K + 1) ≤ x ^ N := pow_le_pow_right₀ hx (by omega)
  have hB0 : 0 ≤ |Cc| * (1 + D) ^ 2 := by positivity
  calc s + sp ≤ s + a * s * x := by linarith
    _ ≤ (1 + a) * x * s := by nlinarith
    _ ≤ (1 + a) * x * (|Cc| * (1 + D) ^ 2 * x ^ (2 * K)) :=
        mul_le_mul_of_nonneg_left hsx (mul_nonneg (by linarith) hx0)
    _ = (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ (2 * K + 1) := by ring
    _ ≤ (1 + a) * (|Cc| * (1 + D) ^ 2) * x ^ N :=
        mul_le_mul_of_nonneg_left hxN (mul_nonneg (by linarith) hB0)

theorem bound_core (hG : GVGroup) (hN : NormInv) (hNF : GNFacts)
    {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {γ : B.Mat k r} (hγ : γ ∈ B.GV k r)
    {Cf Cf' CA Cc : ℝ}
    (hCf : ∀ c b, nsq (fmul k r z c b) ≤ Cf * mx c ^ 2)
    (hCf' : ∀ c b, nsq (fmul k r z' c b) ≤ Cf' * mx c ^ 2)
    (hCc : ∀ s ∈ B.GV k r, ∀ K : ℝ, 0 ≤ K → (∀ i, nsq (s *ᵥ gramVec k r z z' γ i) ≤ K) →
      B.gN s ^ 2 ≤ Cc * (1 + K) ^ 2)
    (σ s' : B.Mat k r) (v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hσ : σ ∈ B.GV k r) (hs' : s' ∈ B.GV k r) (hv : v ∈ UTset (r + 1)) (hu : u' ∈ UTset (r + 1))
    (hσf : ∀ b, σ *ᵥ fvec k r z b = fmul k r z v b)
    (hsf : ∀ b, s' *ᵥ fvec k r z' b = fmul k r z' u' b)
    (hbv : mx v⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1)))
    (hbu : mx u'⁻¹ ≤ CA * B.gN (σ⁻¹ * γ * s') ^ (r * (r + 1))) :
    B.gN σ + B.gN s' ≤ (1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2) *
      B.gN (σ⁻¹ * γ * s') ^ (5 * (r + 1) ^ 2) := by
  obtain ⟨hmul, hinv⟩ := hG k r
  obtain ⟨hnn, hsub, hvec, -⟩ := hNF k r
  have hσi := hinv σ hσ
  have hγi := hinv γ hγ
  have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ hσi.2.1 _ hγ) _ hs'
  have hx1 : 1 ≤ B.gN (σ⁻¹ * γ * s') := (hN k r _ hg).2

  have hσinv_f : ∀ b, σ⁻¹ *ᵥ fvec k r z b = fmul k r z v⁻¹ b := by
    intro b
    have h1 : σ *ᵥ fmul k r z v⁻¹ b = fvec k r z b := by
      rw [frame_mulVec_fmul hσf, ut_mul_inv hv, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, hσi.2.2.2, Matrix.one_mulVec]

  have hσinv_f' : ∀ b, σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b) =
      (σ⁻¹ * γ * s') *ᵥ fmul k r z' u'⁻¹ b := by
    intro b
    have h1 : s' *ᵥ fmul k r z' u'⁻¹ b = fvec k r z' b := by
      rw [frame_mulVec_fmul hsf, ut_mul_inv hu, fmul_one]
    rw [← h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hgv : ∀ i, nsq (σ⁻¹ *ᵥ gramVec k r z z' γ i) ≤
      (|Cf| + |Cf'|) * CA ^ 2 * B.gN (σ⁻¹ * γ * s') ^ (2 * (r * (r + 1)) + 2) := by
    intro i
    generalize hxg : B.gN (σ⁻¹ * γ * s') = x at hx1 hbv hbu
    have hx0 : 0 ≤ x := by linarith
    have hxp : x ^ (2 * (r * (r + 1))) ≤ x ^ (2 * (r * (r + 1)) + 2) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hc0 : 0 ≤ CA ^ 2 := sq_nonneg _
    cases i with
    | inl a =>
      show nsq (σ⁻¹ *ᵥ fvec k r z a) ≤ _
      rw [hσinv_f]
      have h1 := real_sq_bound (mx_nonneg _) hbv hx1 (hCf v⁻¹ a)
      have h2 : |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1))) ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) :=
        mul_le_mul_of_nonneg_left hxp (by positivity)
      have h3 : 0 ≤ |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
    | inr b =>
      show nsq (σ⁻¹ *ᵥ (γ *ᵥ fvec k r z' b)) ≤ _
      rw [hσinv_f']
      have h0 := hvec (σ⁻¹ * γ * s') (fmul k r z' u'⁻¹ b)
      rw [hxg] at h0
      have h1 := real_sq_bound (mx_nonneg _) hbu hx1 (hCf' u'⁻¹ b)
      have h2 : x ^ 2 * nsq (fmul k r z' u'⁻¹ b) ≤ x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : x ^ 2 * (|Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)))) =
          |Cf'| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by ring
      have h4 : 0 ≤ |Cf| * CA ^ 2 * x ^ (2 * (r * (r + 1)) + 2) := by positivity
      linarith
  have hD : 0 ≤ (|Cf| + |Cf'|) * CA ^ 2 := by positivity
  have hcore := hCc σ⁻¹ hσi.2.1 _ (by positivity) hgv
  have hNσ := hN k r σ hσ
  rw [hNσ.1] at hcore
  have hs'eq : s' = γ⁻¹ * σ * (σ⁻¹ * γ * s') := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc γ⁻¹ σ σ⁻¹, hσi.2.2.1,
      Matrix.mul_one, hγi.2.2.2, Matrix.one_mul]
  have hs'b : B.gN s' ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') := by
    conv_lhs => rw [hs'eq]
    calc B.gN (γ⁻¹ * σ * (σ⁻¹ * γ * s')) ≤ B.gN (γ⁻¹ * σ) * B.gN (σ⁻¹ * γ * s') := hsub _ _
      _ ≤ B.gN γ⁻¹ * B.gN σ * B.gN (σ⁻¹ * γ * s') :=
        mul_le_mul_of_nonneg_right (hsub _ _) (hnn _)
  have hN5 : 4 * (r * (r + 1)) + 5 ≤ 5 * (r + 1) ^ 2 := by nlinarith
  exact add_le_mul_pow_of_sq_le_of_le_mul hD (hnn γ⁻¹) hNσ.2 hx1 hcore hs'b hN5

theorem polyProper_of_steps (hG : GVGroup) (hN : NormInv) (hNF : GNFacts) (hF : FmulBound)
    (hZ : ZhatMove) (hS : FrameS) (hSg : FrameSg) (hSg' : FrameSg') (hA : UnitriangularInversePolynomialBound)
    (hC : CoreInst) : PolyProper := by
  refine ⟨5, fun k r z z' γ hstd hpos hmono => ?_⟩
  obtain ⟨CA, hA1, hA2⟩ := hA k r z z' γ hmono
  obtain ⟨Cc, hCc⟩ := hC k r z z' γ hstd hpos
  obtain ⟨Cf, hCf⟩ := hF k r z
  obtain ⟨Cf', hCf'⟩ := hF k r z'
  have hγ : γ ∈ B.GV k r := hpos.1
  obtain ⟨hmul, hinv⟩ := hG k r
  refine ⟨(1 + B.gN γ⁻¹) * (|Cc| * (1 + (|Cf| + |Cf'|) * CA ^ 2) ^ 2), ?_, ?_⟩
  · intro σ hσ s' hs'
    obtain ⟨hσG, v, hv, hvL, hσf⟩ := hSg k r z z' γ hstd σ hσ
    obtain ⟨hs'G, u', hu, hsf⟩ := hS k r z' hstd.2.2 s' hs'
    have hg : σ⁻¹ * γ * s' ∈ B.GV k r := hmul _ (hmul _ (hinv σ hσG).2.1 _ hγ) _ hs'G
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ σ s' v u' hσG hs'G hσf hsf
    obtain ⟨hbv, hbu⟩ := hA1 v hv hvL u' hu _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc σ s' v u' hσG hs'G hv hu hσf hsf hbv hbu
  · intro s hs σ' hσ'
    obtain ⟨hsG, u, hu, hsf⟩ := hS k r z hstd.2.1 s hs
    obtain ⟨hσG, v', hv', hPv, hσf⟩ := hSg' k r z z' γ hstd σ' hσ'
    have hg : s⁻¹ * γ * σ' ∈ B.GV k r := hmul _ (hmul _ (hinv s hsG).2.1 _ hγ) _ hσG
    have hg1 := (hN k r _ hg).2
    have hZg := hZ k r z z' γ s σ' u v' hsG hσG hsf hσf
    obtain ⟨hbu, hbv⟩ := hA2 u hu v' hv' hPv _ hg1 hZg
    exact bound_core hG hN hNF hγ hCf hCf' hCc s σ' u v' hsG hσG hu hv' hsf hσf hbu hbv

end PI.PolynomialProperness
