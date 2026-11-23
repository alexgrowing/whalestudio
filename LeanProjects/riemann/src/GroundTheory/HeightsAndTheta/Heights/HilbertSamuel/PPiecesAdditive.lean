import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPiecesAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set MeasureTheory Manifold EmbeddingWeight

noncomputable section

namespace PiecesAdditiveAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_weight {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {J : Type} [Fintype J]
    {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    ∃ u : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
      (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) ∧
      ∀ z ∈ mcPts P, u z = (S i).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let T : J → Set ((Σ k, ι k) → ℂ) := fun j => mcPts P ∩ S j ∩ {z | ∀ k, blockNormSq z k = 1}
  let C : J → Set ((Σ k, ι k × ι k) → ℂ) := fun j => projPt '' T j
  have hT : ∀ j, IsCompact (T j) := by
    intro j
    refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
    have : T j = ({z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ S j) ∩
        {z | ∀ k, blockNormSq z k = 1} := by
      ext z
      simp only [T, mcPts, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
        by_contra hcon
        push Not at hcon
        have := h3 k
        simp [blockNormSq, hcon] at this
    rw [this]
    exact ((isClosed_zeros P).inter (hS j)).inter isCompact_sphere.isClosed
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (hT j).image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hmem : ∀ j, ∀ z ∈ mcPts P, z ∈ S j → projPt z ∈ C j := by
    intro j z hz hzj
    obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1
    exact ⟨_, ⟨⟨mcPts_smul hP c hc hz, hsm j c z hc hzj⟩, hc1⟩, projPt_smul c hc z⟩
  have hdisj : ∀ j j', j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨⟨hzP, hzs⟩, -⟩, rfl⟩ ⟨w, ⟨⟨hwP, hwt⟩, -⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (hsm j c z hc hzs) hwt)
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
    (isClosed_biUnion_finset fun j _ => (hC j).isClosed) (hC i).isClosed
    (Set.disjoint_iUnion₂_left.2 fun j hj => hdisj j i (Finset.ne_of_mem_erase hj))
  refine ⟨fun z => f (projPt z), ?_, fun c z hc => by simp only [projPt_smul c hc], ?_⟩
  · exact (contMDiff_iff_contDiff.mp f.contMDiff).comp_contDiffOn contDiffOn_projPt
  · intro z hz
    obtain ⟨j, hj, -⟩ := huniq z hz
    by_cases hji : j = i
    · subst hji
      rw [Set.indicator_of_mem hj]
      exact h1.self_of_nhdsSet _ (hmem j z hz hj)
    · have hzi : z ∉ S i := fun h => hji ((huniq z hz).unique hj h)
      rw [Set.indicator_of_notMem hzi]
      exact h0.self_of_nhdsSet _
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hmem j z hz hj⟩)

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_sum (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {J : Type} [Fintype J] (c : J → ℝ) (g : J → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ i, c i * g i z) y w = ∑ i, c i * sheetDensity P Ψ φ (g i) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem integrable_piece (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    {J : Type} [Fintype J] {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y,
      sheetDensity P Ψ (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w) := by
  obtain ⟨u, hus, hui, hu⟩ := exists_weight hP.2.1.2.1 hS hsm huniq i
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.ofWeight u hui
  have hB : IsSmoothHerm B := Real.contDiff_exp.comp_contDiffOn hus.neg
  have hlog : ∀ z, logNorm B 1 z = u z := by
    intro z
    simp [logNorm, B, HermLine.ofWeight]
  have hhom : IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec : IsSectionOn P B 1 := ⟨0, fun k => by simp [B, HermLine.ofWeight], hhom, hnot⟩
  refine (hInt K ι P e Ψ L B 1 hP hΨ hL hB hsec).congr (Eventually.of_forall fun y => ?_)
  refine finsum_mem_congr rfl fun w _ => ?_
  exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.sheetDensity_congr_mcPts P Ψ (fun _ _ _ => rfl)
    (fun z hz => (hlog z).trans (hu z hz)) y w

end PiecesAdditiveAlt

open PiecesAdditiveAlt in

theorem PiecesAdditive.proof (hInt : PtsIntegrableStatement) : PiecesAdditive.Statement := by
  intro K _ ι _ P e L J _ S c hP hL hS hsm huniq
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hlin : ∀ y, (∑ᶠ w ∈ fibre P hΨ.choose y, sheetDensity P hΨ.choose (pot L)
        (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) y w) =
        ∑ i, c i * ∑ᶠ w ∈ fibre P hΨ.choose y,
          sheetDensity P hΨ.choose (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w := by
      intro y
      have hfin := fibreFinite K ι P e _ hP hΨ.choose_spec y
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, sheetDensity_sum, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [hlin]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_piece hInt hP hΨ.choose_spec hL hS hsm huniq i).const_mul (c i)]
    simp only [integral_const_mul]
  · simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
