import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
import GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAddFirst
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsRegLimit
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsMonoSemiPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRegCurvBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.StHorizNotMem
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pot_cons {e : ℕ} (M : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons M L : Fin (e + 1) → HermLine ι) = Fin.cons (fun z => Real.log (M.h z)) (pot L) := by
  funext j z
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [pot]

theorem forall_cons {m : ℕ} {p : HermLine ι → Prop} {M : HermLine ι} {N : Fin m → HermLine ι}
    (hM : p M) (hN : ∀ j, p (N j)) : ∀ j, p ((Fin.cons M N : Fin (m + 1) → HermLine ι) j) :=
  fun j => Fin.cases (by simpa using hM) (fun i => by simpa using hN i) j

theorem ptsIntegral_neg {e : ℕ} (Q : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (f : ((Σ k, ι k) → ℂ) → ℝ) : ptsIntegral Q φ (fun z => -f z) = -ptsIntegral Q φ f := by
  have key : ∀ (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) y w,
      sheetDensity Q Ψ φ (fun z => -f z) y w = -sheetDensity Q Ψ φ f y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · simp only [key, finsum_neg_distrib, MeasureTheory.integral_neg]
  · simp

theorem log_h_eq_neg_logNorm_one (D : HermLine ι) :
    (fun z => Real.log (D.h z)) = fun z => -logNorm D 1 z := by
  funext z
  simp [logNorm, Real.log_inv]

theorem isSectionOn_one {Q : Ideal (MRing ι)} {d : ℕ} (hQ : IsArithVar Q d) {D : HermLine ι}
    (hDa : D.a = 0) : IsSectionOn Q D 1 := by
  refine ⟨0, fun k => by simp [hDa], fun m hm k => ?_,
    fun h => hQ.2.1.1.ne_top ((Ideal.eq_top_iff_one Q).2 h)⟩
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem ptsIntegral_add_first_log (hAdd : PtsAddFirst.Statement) {Q : Ideal (MRing ι)} {e : ℕ}
    {L : Fin e → HermLine ι} {M N D : HermLine ι} (hQ : IsArithVar Q (e + 2))
    (hL : ∀ j, IsSmoothHerm (L j)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N) (hD : IsSmoothHerm D)
    (hDa : D.a = 0) :
    ptsIntegral Q (Fin.cons (fun z => Real.log ((M.tensor N).h z)) (pot L)) (fun z => Real.log (D.h z)) =
      ptsIntegral Q (Fin.cons (fun z => Real.log (M.h z)) (pot L)) (fun z => Real.log (D.h z)) +
        ptsIntegral Q (Fin.cons (fun z => Real.log (N.h z)) (pot L)) (fun z => Real.log (D.h z)) := by
  rw [log_h_eq_neg_logNorm_one D, ptsIntegral_neg, ptsIntegral_neg, ptsIntegral_neg,
    hAdd K ι Q e L M N D 1 hQ hL hM hN hD (isSectionOn_one hQ hDa)]
  ring

theorem tendsto_finsum_of_finite {α : Type*} {p : α → Prop} (hp : {W | p W}.Finite) {f : ℝ → α → ℝ}
    {g : α → ℝ} {l : Filter ℝ} (h : ∀ W, p W → Tendsto (fun ε => f ε W) l (𝓝 (g W))) :
    Tendsto (fun ε => ∑ᶠ (W) (_ : p W), f ε W) l (𝓝 (∑ᶠ (W) (_ : p W), g W)) := by
  have e : ∀ u : α → ℝ, ∑ᶠ (W) (_ : p W), u W = ∑ W ∈ hp.toFinset, u W :=
    fun u => finsum_mem_eq_finite_toFinset_sum u hp
  have e1 : (fun ε => ∑ᶠ (W) (_ : p W), f ε W) = fun ε => ∑ W ∈ hp.toFinset, f ε W :=
    funext fun ε => e (f ε)
  rw [e1, e g]
  exact tendsto_finsetSum _ fun W hW => h W (hp.mem_toFinset.mp hW)

theorem DeLeSemiPos.proof (hPL1 : ArithmeticPoincareLelongFormula) (hSt : StokesStatement) (hAdd : PtsAddFirst.Statement)
    (hLim : PtsRegLimit.Statement) (hMono : PtsMonoSemiPos.Statement) (hCurv : RegCurvBound.Statement)
    (hNot : HorizNotMem.Statement) : DeLeSemiPos.Statement := by
  intro K _ ι _ P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  obtain ⟨a, haA, hsa, hsP⟩ := id hs
  obtain ⟨a', haA', hsa', hs'P⟩ := id hs'
  have ht : ∃ b : K → ℕ, (∀ k, A.a k = b k) ∧ IsMultiHomog s b := ⟨a, haA, hsa⟩
  have ht' : ∃ b : K → ℕ, (∀ k, A'.a k = b k) ∧ IsMultiHomog s' b := ⟨a', haA', hsa'⟩
  obtain ⟨C, hC⟩ := hCurv K ι A' s' ht' hA'
  have hT := isSmoothHerm_ofMetrics_fs (ι := ι) (fun _ => (C : ℤ))
  generalize HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (C : ℤ)) = T at hC hT
  have hfin : ∀ t : MRing ι, {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
    fun t => (divSupp_finite P t).subset fun W h => h.1

  have e1 : ∀ ε : ℝ, 0 < ε →
      ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s) =
        ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A' s' ht' ε).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) := by
    intro ε hε
    have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
    rw [pot_cons, hAdd K ι P n L _ T A s hP hL (isSmoothHerm_tensor hA' hB) hT hA hs,
      hAdd K ι P n L A' _ A s hP hL hA' hB hA hs, hPL1 K ι P n L A _ s hP hL hA hB rfl hs]
  have h1 : Tendsto
      (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L)) (logNorm A s))
      (𝓝[>] 0)
      (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => (e1 ε hε).symm
    refine Tendsto.congr' ev ((tendsto_const_nhds.add
      ((tendsto_finsum_of_finite (hfin s) fun W hW => ?_).sub ?_)).add tendsto_const_nhds)
    · exact (hLim K ι W n L A' s' ht' ((divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2) hL hA'
        (hNot K ι P (n + 2) s s' W hP hsP hs'P hnc hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons A L) A' s' ht' hP (forall_cons hA hL) hA' hs'P
      rwa [pot_cons] at h

  have h2 : ∀ δ : ℝ, 0 < δ →
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) +
        ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
            ptsIntegral W (pot L) (logNorm A' s')) -
          ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s) ≤
      (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z)) := by
    intro δ hδ
    have hD : IsSmoothHerm (regLine A s ht δ) := isSmoothHerm_regLine hA hδ
    have hlimD := hLim K ι P (n + 1) (Fin.cons (regLine A s ht δ) L) A' s' ht' hP (forall_cons hD hL) hA'
      hs'P
    rw [pot_cons, hPL1 K ι P n L A' _ s' hP hL hA' hD rfl hs'] at hlimD
    have hR : Tendsto
        (fun ε => ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)) +
          ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
              ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) -
            ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z))) +
          ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
            (fun z => Real.log ((regLine A s ht δ).h z)))) := by
      have eR : ∀ ε : ℝ, 0 < ε →
          ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log ((regLine A s ht δ).h z)) (pot L))
              (fun z => Real.log ((regLine A' s' ht' ε).h z)) +
            ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
              (fun z => Real.log ((regLine A s ht δ).h z)) =
          ptsIntegral P (pot (Fin.cons ((A'.tensor (regLine A' s' ht' ε)).tensor T) L))
            (fun z => Real.log ((regLine A s ht δ).h z)) := by
        intro ε hε
        have hB : IsSmoothHerm (regLine A' s' ht' ε) := isSmoothHerm_regLine hA' hε
        rw [pot_cons, ptsIntegral_add_first_log hAdd hP hL (isSmoothHerm_tensor hA' hB) hT hD rfl,
          ptsIntegral_add_first_log hAdd hP hL hA' hB hD rfl,
          hSt K ι P n L (regLine A s ht δ) (regLine A' s' ht' ε) hP hL hD hB rfl rfl]
      have ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), _ := eventually_mem_nhdsWithin.mono fun ε hε => eR ε hε
      exact Tendsto.congr' ev ((tendsto_const_nhds.add hlimD).add tendsto_const_nhds)
    have hle := le_of_tendsto_of_tendsto h1 hR (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMono K ι P (n + 1) _ A (regLine A s ht δ) s hP
        (forall_cons (isSmoothHerm_tensor (isSmoothHerm_tensor hA' (isSmoothHerm_regLine hA' hε)) hT) hL)
        (forall_cons (hC ε hε) hLp) hA hs hD rfl
        (fun z hz h0 => logNorm_le_log_regLine_h hδ.le hz.1 h0))
    linarith

  have h3 : Tendsto
      (fun δ => (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (fun z => Real.log ((regLine A s ht δ).h z))) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L))
          (fun z => Real.log ((regLine A s ht δ).h z))) (𝓝[>] 0)
      (𝓝 ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s'}) W : ℝ) *
          ptsIntegral W (pot L) (logNorm A s)) +
        ptsIntegral P (Fin.cons (fun z => Real.log (T.h z)) (pot L)) (logNorm A s))) := by
    refine (tendsto_finsum_of_finite (hfin s') fun W hW => ?_).add ?_
    · exact (hLim K ι W n L A s ht ((divSuppArith K ι P (n + 1) A' s' W hP hs' hW.1).1 hW.2) hL hA
        (hNot K ι P (n + 2) s' s W hP hs'P hsP (fun W h h' => hnc W h' h) hW.1 hW.2)).const_mul _
    · have h := hLim K ι P (n + 1) (Fin.cons T L) A s ht hP (forall_cons hT hL) hA hsP
      rwa [pot_cons] at h
  have h4 := ge_of_tendsto h3 (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact h2 δ hδ)
  unfold De
  linarith

end GroundTheory.Heights₂.Heights.Inter
