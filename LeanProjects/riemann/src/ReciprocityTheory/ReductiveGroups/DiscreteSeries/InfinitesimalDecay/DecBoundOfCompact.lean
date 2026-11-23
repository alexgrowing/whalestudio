import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PmInduction
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.PsiForPosGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.HsPowMulLe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.SumFlatMapMap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.ExistsNearSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundJOfSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecSmOfDecBoundJ
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiGelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.HaarPolar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefIntCpt

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.DecInf

theorem hs_eq_of_compact {n : ℕ} {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : S7.hs g = n := by
  have h2 : inUJ ε g := hg
  delta inUJ Jm at h2
  delta pOf qOf at hpq
  have hU : g.conjTranspose * g = 1 := by
    rcases hpq with hp | hq
    · have hall : ∀ a, ε a = false := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hp) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = -1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
    · have hall : ∀ a, ε a = true := by
        intro a
        have h0 := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hq) (Finset.mem_univ a)
        simpa using h0
      have hd : (Matrix.diagonal fun a => if ε a = true then (1 : ℂ) else -1) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hall, h]
      rw [hd] at h2
      simpa using h2
  delta S7.hs
  rw [Finset.sum_comm]
  have key : ∀ j, ∑ i, ‖g i j‖ ^ 2 = (1 : ℝ) := by
    intro j
    have hjj := congrFun (congrFun hU j) j
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at hjj
    have hc : ∀ i, g.conjTranspose j i * g i j = ((‖g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_mul']
      norm_cast
    simp only [hc] at hjj
    exact_mod_cast hjj
  simp [key]

theorem decBound_of_compact {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hpq : pOf ε = 0 ∨ qOf ε = 0) (m N : ℕ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m N := by
  obtain ⟨_, _, hU, _⟩ := hσ
  refine ⟨Real.sqrt (n : ℝ) ^ m, [[]], ?_, ?_⟩
  · intro w hw
    simp only [List.mem_singleton] at hw
    subst hw
    simp
  · intro u v _ _ g hg
    have hn : S7.hs g = n := hs_eq_of_compact hpq hg
    have hnorm : ‖σ g u‖ = ‖u‖ := hU.2.1 g hg u
    simp only [nuJ, dSW, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hn, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
    calc ‖inner ℂ v (σ g u)‖ ≤ ‖v‖ * ‖σ g u‖ := norm_inner_le_norm v (σ g u)
      _ = ‖u‖ * ‖v‖ := by rw [hnorm, mul_comm]

theorem decSmJ {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam) {h : ℝ}
    (hgap : GapAtLeast ε lam h) (m : ℕ) (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDS ε lam σ) :
    DecBoundJ ε σ m (m * (n - 1)) := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · exact decBound_of_compact hpq m _ hσ
  have hp : 1 ≤ pOf ε := by omega
  have hq : 1 ≤ qOf ε := by omega
  have hq0 : 1 ≤ S7.q0 ε := by unfold S7.q0; omega
  have hth : thrStar ε < h := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h8 : 8 * (n : ℝ) * S7.q0 ε < h := by
    have h1 : 16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ thrStar ε := le_max_right _ _
    have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
    have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
    linarith
  obtain ⟨T⟩ := HW.kType_exists ε lam hlam
  obtain ⟨Ψ, hP, -⟩ := exists_isPsiFor S7.psiExists T hlam hgap hq0 h8
  have hv₀ : T.w ≠ 0 := HW.KType.w_ne_zero T
  have hstd : StdGap ε lam := ⟨hlam.1, h, hgap, lt_of_le_of_lt (le_max_left _ _) hth⟩
  obtain ⟨C, hC⟩ := pm_induction hp hq m hlam hgap hm hP hv₀
  refine decBoundJ_of_sigLam hlam hgap hth hP hv₀ hσ m _ ?_
  refine decBoundJ_sigLam hlam hstd hP hv₀ m _ ⟨(n : ℝ) ^ (2 * m) * C, fun x hx y hy g hg => ?_⟩
  have := hs_pow_mul_le m g (norm_nonneg _) fun idx => hC x hx y hy g hg idx
  calc _ ≤ _ := this
    _ = _ := by ring

theorem decSm {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m : ℕ)
    (hm : thrStar ε + m < h)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
      (∀ w ∈ Ws, w.length ≤ m * (2 * r + k) ∧ ∀ X ∈ w, Formalism.MainNotions.S.InLieHpk k r X) ∧
      ∀ u ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
        ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
          Formalism.FourierDecayAlt.B.gN (k := k) (r := r) g ^ m * ‖inner ℂ v (σ g u)‖ ≤
            C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w u‖).sum *
              (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v‖).sum := by
  obtain ⟨P, hP, hDS⟩ := hσ
  have hJ := decSmJ ((mir_isHCParam_iff lam).1 hlam) ((mir_gapAtLeast_iff ε lam h).1 hgap) m hm hDS
  have hN : m * (2 * r + k + 1 - 1) = m * (2 * r + k) := by rw [Nat.add_sub_cancel]
  rw [hN] at hJ
  exact decSm_of_decBoundJ hP m _ hJ

end ReciprocityTheory.ChartRestriction.DS.DecInf
