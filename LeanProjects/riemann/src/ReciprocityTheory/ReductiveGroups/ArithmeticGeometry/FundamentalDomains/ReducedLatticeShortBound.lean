import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsPerpHermitianReduction
import ReciprocityTheory.SemistableReduction.LatAll
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCombinations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem jForm_swap_eq_conj (p : ℕ) {n : ℕ} (x y : Fin n → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.jForm p y x = conj (ReciprocityTheory.MultiplicativeHeights.jForm p x y) := by
  unfold ReciprocityTheory.MultiplicativeHeights.jForm ReciprocityTheory.MultiplicativeHeights.sgn
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [mul_comm]

private theorem linearIndependent_mulVec_embVec {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* ℂ)
    (A : Matrix (Fin n) (Fin n) K) (Q : Matrix (Fin n) (Fin n) ℂ) (hA : LinearIndependent K A)
    (hQ : Q.det ≠ 0) : LinearIndependent ℂ (fun j => Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) := by
  have hdet : Matrix.det A ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hA)).ne_zero
  have hMe : (Matrix.of fun j k => (Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) k) =
      σ.mapMatrix A * Q.transpose := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.mulVec, dotProduct, ReciprocityTheory.MultiplicativeHeights.embVec]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hU : IsUnit (Matrix.of fun j k => (Q *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec σ (A j)) k) := by
    rw [hMe, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_transpose,
      ← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero ((map_ne_zero σ).mpr hdet) hQ)
  exact Matrix.linearIndependent_rows_iff_isUnit.mpr hU

theorem reducedLattice_short_bound (hD5 : CoveringRadiusStatement) (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) (β : Fin (r - 2) → Fin r → E) (S : ReciprocityTheory.MultiplicativeHeights.HermForm E (r - 2))
    (LB : Submodule (𝓞 E) (Fin (r - 2) → E)) (Q : X.Ψ → Matrix (Fin (r - 2)) (Fin (r - 2)) ℂ) (ep rh : ℝ)
    (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hβ : ∀ k, herm X.Gm (β k) ξ = 0)
    (hβind : LinearIndependent E (Fin.cons ξ β : Fin (r - 2 + 1) → Fin r → E))
    (hβspan : ∀ x : Fin r → E, herm X.Gm x ξ = 0 → ∃ (c : Fin (r - 2) → E) (e : E), x = ∑ k, c k • β k + e • ξ)
    (hS : ∀ c c' : Fin (r - 2) → E, S.h c c' = herm X.Gm (∑ k, c' k • β k) (∑ k, c k • β k))
    (hLB : ∀ c : Fin (r - 2) → E, c ∈ LB ↔ ∃ e : E, ∑ k, c k • β k + e • ξ ∈ X.L')
    (hLat : ReciprocityTheory.MultiplicativeHeights.IsLattice LB) (hSD : ReciprocityTheory.MultiplicativeHeights.IsSelfDual S LB)
    (hQ : ∀ τ, (Q τ).det ≠ 0)
    (hSQ : ∀ τ (c c' : Fin (r - 2) → E), τ.1 (S.h c c') =
      ReciprocityTheory.MultiplicativeHeights.jForm (X.p0 - 1) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c'))
    (hQf : ∀ τ (c : Fin (r - 2) → E), X.ucomp z0 ξ (X.embV (∑ k, c k • β k)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 c) k • f τ k)
    (hep : 0 < ep) (hep1 : ep ≤ 1) (hrh : 0 < rh) (hrh1 : rh ≤ 1)
    (hD4 : ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, ep ≤ X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)) :
    ∃ lam : Fin (r - 2) → Fin r → E,
      (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
      (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → ∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
      (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
      (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ d6La r X.p0 (fdeg E) (dE E) ep rh ^ 2) ∧
      (∀ τ, LinearIndependent ℂ fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) ∧
      (∀ τ j, X.ucomp z0 ξ (X.embV (lam j)) τ ∈ Submodule.span ℂ (Set.range (f τ))) ∧
      (∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
        hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV (lam j)) τ) (X.ucomp z0 ξ (X.embV (lam k)) τ) = 0) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
        0 < (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re) ∧
      (∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
        (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)
          (∑ j, w j • X.ucomp z0 ξ (X.embV (lam j)) τ)).re < 0) ∧
      (∀ τ (c : Fin (r - 2) → ℂ), (∑ k, c k • f τ k) ∈ Submodule.span ℂ
          ((fun j => X.ucomp z0 ξ (X.embV (lam j)) τ) '' {j | (j : ℕ) < X.p0 - 1}) →
        (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
          (rh / 120) ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0) := by
  classical
  obtain ⟨hξΛ, hξξ, hξ0⟩ := hξ
  have hcardpos : 0 < Fintype.card X.Ψ := by
    apply QuadraticCoefficientForms.card_Psi_pos <;> assumption
  have hcard : Fintype.card X.Ψ = fdeg E := by
    apply QuadraticCoefficientForms.card_Psi <;> assumption
  haveI : Nonempty X.Ψ := Fintype.card_pos_iff.mp hcardpos
  obtain ⟨τ0⟩ := (inferInstance : Nonempty X.Ψ)
  have hpb : 1 ≤ X.p0 ∧ X.p0 < r := by
    apply IsotropicIndexSums.isotropicIndex_bounds (hξ := hξξ) (hne := hξ0) (τ := τ0) <;> assumption
  obtain ⟨hp1, hpr0⟩ := hpb
  have hON : ∀ τ : X.Ψ, ∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0 := fun τ => (hf τ).2.2.1
  have hSsym : ∀ x y : Fin (r - 2) → E, S.h x y = 0 → S.h y x = 0 := by
    intro x y hxy
    apply (map_eq_zero τ0.1).mp
    rw [hSQ, jForm_swap_eq_conj, ← hSQ, hxy]
    simp
  rcases Nat.eq_zero_or_pos (r - 2) with hn | hn
  · haveI : IsEmpty (Fin (r - 2)) := by rw [hn]; infer_instance
    refine ⟨fun j => ∑ k, (0 : E) • β k + (0 : E) • ξ, fun j => isEmptyElim j, ?_,
      fun j => isEmptyElim j, fun j => isEmptyElim j, fun j => isEmptyElim j,
      fun j => isEmptyElim j, fun _ => linearIndependent_empty_type, fun _ j => isEmptyElim j,
      fun _ j => isEmptyElim j, fun _ w _ hw => absurd (Subsingleton.elim w 0) hw,
      fun _ w _ hw => absurd (Subsingleton.elim w 0) hw, fun _ c _ => by simp⟩
    apply IsotropicCombinations.cons_li (hli := hβind) (hla := linearIndependent_empty_type) <;> assumption
  have hlamξ : ∀ (c : Fin (r - 2) → E) (e : E), herm X.Gm (∑ k, c k • β k + e • ξ) ξ = 0 := by
    intro c e
    apply IsotropicCombinations.herm_lam_ξ <;> assumption
  have hpr : X.p0 - 1 ≤ r - 2 := by omega
  have h_inj : Function.Injective (fun τ : X.Ψ => τ.1) := Subtype.val_injective
  have h_cm : ∀ τ : E →+* ℂ, (∃ i : X.Ψ, (fun τ : X.Ψ => τ.1) i = τ) ↔
      ¬ ∃ i : X.Ψ, (fun τ : X.Ψ => τ.1) i = ComplexEmbedding.conjugate τ := by
    intro τ
    have h := X.cmType τ
    constructor
    · rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hτ : τ ∈ X.Ψ := by rw [← hi]; exact i.2
      have hc : ComplexEmbedding.conjugate τ ∈ X.Ψ := by rw [← hj]; exact j.2
      exact (h.mp hτ) hc
    · intro hn'
      exact ⟨⟨τ, h.mpr fun hc => hn' ⟨⟨_, hc⟩, rfl⟩⟩, rfl⟩
  have h_short : ∀ v ∈ LB, v ≠ 0 → ∃ i : X.Ψ, Real.sqrt ep ^ 2 ≤
      ReciprocityTheory.MultiplicativeHeights.normSq (Q i *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec i.1 v) := by
    intro v hv hv0
    obtain ⟨e, he⟩ := (hLB v).mp hv
    have hne : ∀ e' : E, ∑ k, v k • β k + e • ξ ≠ e' • ξ := by
      intro e'
      apply IsotropicCombinations.ne_smul_ξ (hli := hβind) (hc := hv0) <;> assumption
    obtain ⟨τ, hτ⟩ := hD4 _ he (hlamξ v e) hne
    refine ⟨τ, ?_⟩
    rw [IsotropicIndexSums.ucomp_drop (hx := hz) (hne := hξ0), hQf, (hf τ).2.2.2.1] at hτ
    rw [Real.sq_sqrt hep.le]
    exact hτ
  have hD := hD5 E X.Ψ (r - 2) (X.p0 - 1) S (fun τ : X.Ψ => τ.1) Q LB (Real.sqrt ep) h_inj h_cm
    hpr (Real.sqrt_pos.mpr hep) hQ hSQ hLat hSD h_short
  obtain ⟨hcov, v, hvL, hvli, hvmaj⟩ := hD
  rw [hcard] at hcov hvmaj
  have hf1 : (1 : ℝ) ≤ (fdeg E : ℝ) := by
    rw [← hcard]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hcardpos.ne'
  have hnR : (1 : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn.ne'
  have hd1 : (1 : ℝ) ≤ dE E := by
    unfold dE
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero (K := E))
  have hs : 0 < Real.sqrt ep := Real.sqrt_pos.mpr hep
  have hs1 : Real.sqrt ep ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hep1
  have hX : 1 ≤ ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hf1 hnR)
  have hXd : 1 ≤ ((fdeg E : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ 3 * dE E := by
    have h := mul_le_mul hX hd1 zero_le_one (by linarith)
    linarith
  have hμpos : 0 < (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) := by
    unfold d5mu
    apply div_pos _ hs
    linarith
  have hμ4 : 4 ≤ (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) := by
    unfold d5mu
    rw [le_div_iff₀ hs]
    linarith
  have hA : 1 ≤ Real.sqrt ((r - 2 : ℕ) : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hnR
  have e1 : 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) =
      320 * (Real.sqrt ((r - 2 : ℕ) : ℝ) * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) / rh := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR
    rw [div_div_eq_mul_div]
    ring
  have hT320 : 320 * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) := by
    rw [e1, le_div_iff₀ hrh]
    nlinarith [mul_le_mul_of_nonneg_left hrh1 hμpos.le, mul_le_mul_of_nonneg_right hA hμpos.le]
  have hT1 : 1 ≤ 2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) := by linarith
  have hTμ : 2 * (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep)) ^ 2 ≤ (2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40)) ^ 2 := by
    nlinarith [mul_le_mul hT320 hT320 (by linarith) (by linarith), sq_nonneg (d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))]
  obtain ⟨la, hlaL, hlali, hlaorth, hlapos, hlaneg, hlab1, hlab2⟩ :=
    ReciprocityTheory.MultiplicativeHeights.Closed.approx E X.Ψ (r - 2) (X.p0 - 1) S (fun τ : X.Ψ => τ.1) Q LB v
      ((d5mu (fdeg E) (r - 2) (dE E) (Real.sqrt ep))) (rh / 40) hpr hμpos (div_pos hrh (by norm_num)) (by linarith) hQ hSQ hSD.1
      hcov hvL hvli hvmaj
  choose ec hec using fun j => (hLB (la j)).mp (hlaL j)
  have hu : ∀ (τ : X.Ψ) (j : Fin (r - 2)), X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ =
      ∑ k, (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) k • f τ k := by
    intro τ j
    rw [IsotropicIndexSums.ucomp_drop (hx := hz) (hne := hξ0), hQf]
  have hcomb : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ),
      ∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ =
        ∑ k, (Q τ *ᵥ ∑ j, w j • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) k • f τ k := by
    intro τ w
    simp_rw [hu τ]
    rw [IsotropicCombinations.comb_swap]
    simp_rw [IsotropicCombinations.qcomb]
  have hone : ∀ (τ : X.Ψ) (j : Fin (r - 2)),
      Q τ *ᵥ ∑ i, (Pi.single j (1 : ℂ) : Fin (r - 2) → ℂ) i • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la i) =
        Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j) := by
    intro τ j
    congr 1
    simp [Pi.single_apply]
  have hsn : ∀ j : Fin (r - 2), (Pi.single j (1 : ℂ) : Fin (r - 2) → ℂ) ≠ 0 :=
    fun j h => by simpa using congrFun h j
  have hll : ∀ j1 j2 : Fin (r - 2), herm X.Gm (∑ i, la j1 i • β i + ec j1 • ξ) (∑ i, la j2 i • β i + ec j2 • ξ) = S.h (la j2) (la j1) := by
    intro j1 j2
    rw [hS (la j2) (la j1)]
    apply IsotropicCombinations.herm_lam_lam <;> first | assumption | exact X.Gm_herm
  have hM : ∀ τ : X.Ψ, LinearIndependent ℂ (fun j => Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) :=
    fun τ => linearIndependent_mulVec_embVec τ.1 la (Q τ) hlali (hQ τ)
  have F2 : LinearIndependent E (Fin.cons ξ (fun j => (∑ i, la j i • β i + ec j • ξ)) : Fin (r - 2 + 1) → Fin r → E) := by
    apply IsotropicCombinations.cons_li (hli := hβind) (hla := hlali) <;> assumption
  have F3 : ∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la k i • β i + ec k • ξ) = 0 := by
    intro j k hj hk
    rw [hll, hSsym _ _ (hlaorth j k hj hk)]
  have F4 : ∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → ∀ τ : X.Ψ,
      0 < (τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))).re := by
    intro j hj τ
    rw [hll, hSQ, ← hone τ j]
    exact (hlapos τ (Pi.single j (1 : ℂ))
      (fun i hi => by rw [Pi.single_apply, if_neg]; rintro rfl; omega)).2 (hsn j)
  have F5 : ∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → ∀ τ : X.Ψ,
      (τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))).re < 0 := by
    intro j hj τ
    rw [hll, hSQ, ← hone τ j]
    exact hlaneg τ (Pi.single j (1 : ℂ))
      (fun i hi => by rw [Pi.single_apply, if_neg]; rintro rfl; omega) (hsn j)
  have F6 : ∀ (j : Fin (r - 2)) (τ : X.Ψ),
      ‖τ.1 (herm X.Gm (∑ i, la j i • β i + ec j • ξ) (∑ i, la j i • β i + ec j • ξ))‖ ≤ d6La r X.p0 (fdeg E) (dE E) ep rh ^ 2 := by
    intro j τ
    rw [hll]
    apply IsotropicCombinations.la_bound (hT := hT1) (hμ := hTμ) (hp0 := hp1)
    by_cases hj : (j : ℕ) < X.p0 - 1
    · exact Or.inl (hlab1 τ j hj)
    · exact Or.inr (hlab2 τ j (not_lt.mp hj))
  have F7 : ∀ τ : X.Ψ, LinearIndependent ℂ fun j => X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ := by
    intro τ
    rw [Fintype.linearIndependent_iff]
    intro w hw
    rw [hcomb τ w] at hw
    have h0 : Q τ *ᵥ ∑ j, w j • ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j) = 0 :=
      IsotropicIndexSums.coeff_unique (f := f τ) (hf := hON τ)
        (h := hw.trans (by simp : (0 : Fin r → ℂ) = ∑ k, (0 : Fin (r - 2) → ℂ) k • f τ k))
    have h1 : ∑ j, w j • (Q τ *ᵥ ReciprocityTheory.MultiplicativeHeights.embVec τ.1 (la j)) = 0 := by
      funext k
      have h2 := congrFun h0 k
      rw [IsotropicCombinations.qcomb] at h2
      simpa [Finset.sum_apply] using h2
    exact Fintype.linearIndependent_iff.mp (hM τ) w h1
  have F8 : ∀ (τ : X.Ψ) (j : Fin (r - 2)),
      X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ j
    rw [hu τ j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have F9 : ∀ (τ : X.Ψ) (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ) (X.ucomp z0 ξ (X.embV (∑ i, la k i • β i + ec k • ξ)) τ) = 0 := by
    intro τ j k hj hk
    rw [hu τ j, hu τ k, IsotropicCombinations.hC_comb2_ortho (hf := hON τ), ← hSQ,
      hSsym _ _ (hlaorth j k hj hk), map_zero]
  have WorkedExample : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) →
      w ≠ 0 → 0 < (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)
        (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)).re := by
    intro τ w hw hw0
    rw [hcomb τ w, IsotropicIndexSums.hC_comb_ortho (hf := hON τ)]
    exact (hlapos τ w hw).2 hw0
  have LargeParameterEstimates : ∀ (τ : X.Ψ) (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) →
      w ≠ 0 → (hermC τ.1 X.Gm (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)
        (∑ j, w j • X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ)).re < 0 := by
    intro τ w hw hw0
    rw [hcomb τ w, IsotropicIndexSums.hC_comb_ortho (hf := hON τ)]
    exact hlaneg τ w hw hw0
  have F12 : ∀ (τ : X.Ψ) (c : Fin (r - 2) → ℂ), (∑ k, c k • f τ k) ∈ Submodule.span ℂ
      ((fun j => X.ucomp z0 ξ (X.embV (∑ i, la j i • β i + ec j • ξ)) τ) '' {j | (j : ℕ) < X.p0 - 1}) →
      (∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then 0 else ‖c k‖ ^ 2) ≤
        (rh / 120) ^ 2 * ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖c k‖ ^ 2 else 0 := by
    intro τ c hc
    rw [Finsupp.mem_span_image_iff_linearCombination] at hc
    obtain ⟨l, hl, hlc⟩ := hc
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype l
      (fun i a => a • X.ucomp z0 ξ (X.embV (∑ k, la i k • β k + ec i • ξ)) τ) (fun _ => zero_smul ℂ _)] at hlc
    rw [hcomb τ l] at hlc
    have hcq := IsotropicIndexSums.coeff_unique (f := f τ) (hf := hON τ) (h := hlc)
    have hws : ∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → l j = 0 := by
      intro j hj
      rw [Finsupp.mem_supported'] at hl
      exact hl j (by simp only [Set.mem_setOf_eq, not_lt]; exact hj)
    have h3 := (hlapos τ l hws).1
    simp only [hcq] at h3
    rw [show rh / 40 / 3 = rh / 120 by ring] at h3
    exact h3
  exact ⟨fun j => (∑ i, la j i • β i + ec j • ξ), fun j => ⟨hec j, hlamξ _ _⟩, F2, F3, F4, F5, F6, F7, F8, F9, WorkedExample, LargeParameterEstimates, F12⟩

end

end ReciprocityTheory.ChartRestriction.G.FD
