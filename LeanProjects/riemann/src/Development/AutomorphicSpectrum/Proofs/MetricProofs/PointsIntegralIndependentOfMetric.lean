import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothWeightConstNearEmbeddings
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstantStatement
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

section FactorChange

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem snoc_update_comp_swap {D : ℕ} (W : Fin D → HermLine ι) (m : Fin D) (X B : HermLine ι) :
    (Fin.snoc (Function.update W m X) B : Fin (D + 1) → HermLine ι) ∘
        Equiv.swap m.castSucc (Fin.last D) =
      Fin.snoc (Function.update W m B) X := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_right, Fin.snoc_castSucc, Function.update_self, Fin.snoc_last]
  · by_cases hi : i = m
    · subst hi
      rw [Function.comp_apply, Equiv.swap_apply_left, Fin.snoc_last, Fin.snoc_castSucc, Function.update_self]
    · have h1 : i.castSucc ≠ m.castSucc := fun h => hi (Fin.castSucc_injective _ h)
      have h2 : i.castSucc ≠ Fin.last D := (Fin.castSucc_lt_last i).ne
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Function.update_of_ne hi, Function.update_of_ne hi]

theorem smooth_update {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D)
    {X : HermLine ι} (hX : IsSmoothHerm X) (j : Fin D) : IsSmoothHerm (Function.update W m X j) := by
  by_cases hj : j = m
  · subst hj
    simpa using hX
  · simpa [Function.update_of_ne hj] using hW j

theorem smooth_snoc {D : ℕ} {W : Fin D → HermLine ι} (hW : ∀ j, IsSmoothHerm (W j)) {X : HermLine ι}
    (hX : IsSmoothHerm X) (j : Fin (D + 1)) :
    IsSmoothHerm ((Fin.snoc W X : Fin (D + 1) → HermLine ι) j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    exact hX
  · rw [Fin.snoc_castSucc]
    exact hW i

theorem position_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (W : Fin D → HermLine ι) (hW : ∀ j, IsSmoothHerm (W j)) (m : Fin D) (A A' B : HermLine ι)
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hB : IsSmoothHerm B) (hab : A'.a = A.a)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc (Function.update W m A) B) =
      I P (D + 1) (Fin.snoc (Function.update W m A') B) := by
  have hM := smooth_update hW m hB
  have hswap : ∀ X : HermLine ι, IsSmoothHerm X →
      I P (D + 1) (Fin.snoc (Function.update W m X) B) = I P (D + 1) (Fin.snoc (Function.update W m B) X) := by
    intro X hX
    rw [← snoc_update_comp_swap W m X B]
    exact (hI.1 P (D + 1) _ _ hP (smooth_snoc (smooth_update hW m hX) hB)).symm
  rw [hswap A hA, hswap A' hA',
    GlobalTheory.CompanionTheory.Ar.Tele.step GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full I hI P D _ A A' hP hM hA hA' hab,
    GlobalTheory.T.points_integral_zero_of_locally_constant K ι P D (pot (Function.update W m B)) _ m ?_, sub_zero]
  intro z hz
  obtain ⟨c, hc⟩ := hloc z hz
  refine ⟨Real.log c, ?_⟩
  filter_upwards [hc] with x hx
  simp [pot, hx]

theorem word_change (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) {D : ℕ} (hP : IsArithVar P (D + 1))
    (L L' : Fin D → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j))
    (ha : ∀ j, (L j).a = (L' j).a) (B : HermLine ι) (hB : IsSmoothHerm B)
    (hloc : ∀ z ∈ mcPts P, ∃ c : ℝ, B.h =ᶠ[𝓝 z] fun _ => c) :
    I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc L' B) := by
  let Wd : ℕ → Fin D → HermLine ι := fun m j => if (j : ℕ) < m then L' j else L j
  have hWd : ∀ m j, IsSmoothHerm (Wd m j) := by
    intro m j
    by_cases h : (j : ℕ) < m
    · simpa [Wd, h] using hL' j
    · simpa [Wd, h] using hL j
  have key : ∀ m, m ≤ D → I P (D + 1) (Fin.snoc L B) = I P (D + 1) (Fin.snoc (Wd m) B) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : Wd 0 = L := by
        funext j
        simp [Wd]
      rw [this]
    | succ m ih =>
      intro hm
      let i : Fin D := ⟨m, hm⟩
      have e0 : Function.update (Wd m) i (L i) = Wd m := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · simp [Function.update_of_ne hj]
      have e1 : Function.update (Wd m) i (L' i) = Wd (m + 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [Wd, i]
        · have hne : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
          have hiff : (j : ℕ) < m + 1 ↔ (j : ℕ) < m := by omega
          simp [Function.update_of_ne hj, Wd, hiff]
      rw [ih (by omega), ← e1]
      conv_lhs => rw [← e0]
      exact position_change I hI P hP (Wd m) (hWd m) i (L i) (L' i) B (hL i) (hL' i) hB (ha i).symm hloc
  have hD : Wd D = L' := by
    funext j
    simp [Wd]
  rw [key D le_rfl, hD]

end FactorChange

theorem mass_eq_of_degrees : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L L' : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, (L j).a = (L' j).a) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L') ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hA hInt K _ ι _ Ω _ F _ _ _ y D L L' sg hP hL hL' ha hex
  classical
  obtain ⟨II, hII, -⟩ := hA
  let Λ : (F →+* ℂ) → ℝ := fun s => if s = sg then Real.exp 1 else 1
  have hΛ : ∀ s, 0 < Λ s := by
    intro s
    by_cases h : s = sg
    · simp [Λ, h, Real.exp_pos]
    · simp [Λ, h]
  obtain ⟨B, hB0, hBs, hBloc⟩ :=
    exists_smooth_weight_const_near_embeddings K ι Ω F y Λ hΛ hex
  have mass : ∀ M : Fin D → HermLine ι, (∀ j, IsSmoothHerm (M j)) →
      II K ι (mCoordIdeal y) (D + 1) (Fin.snoc M B) =
        ptsIntegral (mCoordIdeal y) (pot M) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
    intro M hM
    rw [intersection_locConst_trivial hInt K ι Ω F y D M B Λ II hII hP hM hB0 hBs hex hBloc,
      Finset.sum_eq_single sg]
    · simp [Λ]
    · intro s _ hs
      simp [Λ, hs]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [← mass L hL, ← mass L' hL']
  refine word_change (II K ι) (hII K ι) _ hP L L' hL hL' ha B hBs ?_
  intro z hz
  obtain ⟨s, hs, -⟩ := hex z hz
  exact ⟨Λ s, hBloc z hz s hs⟩

end GlobalTheory.CompanionTheory.Ar.Giv
