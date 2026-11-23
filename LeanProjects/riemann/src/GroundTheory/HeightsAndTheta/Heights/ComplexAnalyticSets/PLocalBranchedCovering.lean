import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalBranchedCovering
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDiscriminantSheetCover
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PManifoldZerosComplementConnected
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IrreducibleConnected.BasicOpenSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Matrix

namespace LocalBranchedCovering

theorem isolated_of_finite {E : Type*} [TopologicalSpace E] [T1Space E] {F : Set E} (hF : F.Finite) (z : E) :
    ∃ N ∈ 𝓝 z, ∀ z' ∈ N, z' ∈ F → z' = z := by
  refine ⟨(F \ {z})ᶜ, (hF.subset Set.sdiff_subset).isClosed.compl_mem_nhds (fun h => h.2 rfl),
    fun z' h1 h2 => ?_⟩
  by_contra hne
  exact h1 ⟨h2, hne⟩

theorem of_sheets {σ : Type} [Fintype σ] {k : ℕ} (Z : Set (σ → ℂ)) (hZ : IsClosed Z)
    (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (P : MvPolynomial (Fin k) ℂ) (hP : P ≠ 0)
    (hfin : ∀ y, {z | z ∈ Z ∧ A z = y}.Finite)
    (hsheet : ∀ y, eval y P ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (N : ℕ) (s : Fin N → (Fin k → ℂ) → σ → ℂ),
      IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
      ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∧ A (s j y') = y') ∧ Function.Injective (fun j => s j y') ∧
        ∀ z ∈ Z, A z = y' → z ∈ Set.range (fun j => s j y'))
    (hopen : ∀ z ∈ Z, (∃ N ∈ 𝓝 z, ∀ z' ∈ N, z' ∈ Z → A z' = A z → z' = z) →
      ∀ W' ∈ 𝓝 z, A '' (Z ∩ W') ∈ 𝓝 (A z))
    (w : σ → ℂ) (U : Set (σ → ℂ)) (hU : U ∈ 𝓝 w) :
    ∃ (W : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ) (δ : (Fin k → ℂ) → ℂ),
      IsOpen W ∧ w ∈ W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ Z ∩ W, A z = A w → z = w) ∧
      (∀ z ∈ Z ∩ closure W, A z ∈ D → z ∈ W) ∧
      DifferentiableOn ℂ δ D ∧
      (∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ D → V.Nonempty → ∃ t ∈ V, δ t ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (s : Fin m → (Fin k → ℂ) → σ → ℂ),
        IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
        ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∩ W ∧ A (s j y') = y') ∧
          Function.Injective (fun j => s j y') ∧
          ∀ z ∈ Z ∩ W, A z = y' → z ∈ Set.range (fun j => s j y')) ∧
      ∀ z ∈ Z ∩ W, ∀ ε > 0, A '' (Z ∩ Metric.ball z ε) ∈ 𝓝 (A z) := by
  classical

  obtain ⟨N₀, hN₀, hN₀w⟩ := isolated_of_finite (hfin (A w)) w
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem hU hN₀)
  have hfib : ∀ z ∈ Metric.closedBall w r, z ∈ Z → A z = A w → z = w :=
    fun z hz hzZ hzA => hN₀w z (hrU hz).2 ⟨hzZ, hzA⟩
  have hclos : closure (Metric.ball w r) = Metric.closedBall w r := closure_ball w hr.ne'

  have hKc : IsCompact (A '' (Z ∩ Metric.sphere w r)) :=
    ((isCompact_sphere w r).inter_left hZ).image A.continuous
  have hwK : A w ∉ A '' (Z ∩ Metric.sphere w r) := by
    rintro ⟨z, ⟨hzZ, hzs⟩, hzA⟩
    have hzw := hfib z (Metric.sphere_subset_closedBall hzs) hzZ hzA
    rw [hzw, Metric.mem_sphere, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isClosed.isOpen_compl (A w) hwK

  have hprop : ∀ z ∈ Z ∩ Metric.closedBall w r, A z ∈ Metric.ball (A w) ρ → z ∈ Metric.ball w r := by
    rintro z ⟨hzZ, hzb⟩ hzD
    by_contra hzW
    have hzs : z ∈ Metric.sphere w r :=
      le_antisymm (Metric.mem_closedBall.1 hzb) (not_lt.1 (fun h => hzW (Metric.mem_ball.2 h)))
    exact hρK hzD ⟨z, ⟨hzZ, hzs⟩, rfl⟩

  have hδa : AnalyticOnNhd ℂ (fun y : Fin k → ℂ => eval y P) Set.univ := AnalyticOnNhd.eval_mvPolynomial P
  have hdense := HilbertSamuel.IrreducibleBasicOpenConnected.dense_ne_zero hP
  have hδV : ∀ V : Set (Fin k → ℂ), IsOpen V → V ⊆ Metric.ball (A w) ρ → V.Nonempty →
      ∃ t ∈ V, eval t P ≠ 0 := by
    intro V hV _ hVn
    obtain ⟨t, ht⟩ := hdense.inter_open_nonempty V hV hVn
    exact ⟨t, ht.1, ht.2⟩

  have hloc : ∀ y ∈ Metric.ball (A w) ρ, eval y P ≠ 0 → ∃ (O : Set (Fin k → ℂ)) (N : ℕ)
      (s : Fin N → (Fin k → ℂ) → σ → ℂ) (S : Finset (Fin N)),
      IsOpen O ∧ y ∈ O ∧ O ⊆ Metric.ball (A w) ρ ∧ (∀ j, DifferentiableOn ℂ (s j) O) ∧
      ∀ y' ∈ O, (∀ j, s j y' ∈ Z ∧ A (s j y') = y') ∧ Function.Injective (fun j => s j y') ∧
        {z | z ∈ Z ∩ Metric.ball w r ∧ A z = y'} = (fun j => s j y') '' S := by
    intro y hyD hy
    obtain ⟨O₁, N, s, hO₁, hyO₁, hsd, hs⟩ := hsheet y hy
    have hcont : ∀ j, ContinuousAt (s j) y := fun j =>
      ((hsd j).differentiableAt (hO₁.mem_nhds hyO₁)).continuousAt
    let S : Finset (Fin N) := Finset.univ.filter (fun j => s j y ∈ Metric.ball w r)
    have hT : ∀ j, ∀ᶠ y' in 𝓝 y, (s j y' ∈ Metric.ball w r ↔ j ∈ S) := by
      intro j
      by_cases hj : s j y ∈ Metric.ball w r
      · filter_upwards [hcont j (Metric.isOpen_ball.mem_nhds hj)] with y' hy'
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_of_true hy' hj
      · have hnc : s j y ∉ Metric.closedBall w r := fun h =>
          hj (hprop _ ⟨((hs y hyO₁).1 j).1, h⟩ (by rw [((hs y hyO₁).1 j).2]; exact hyD))
        filter_upwards [hcont j (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hnc)] with y' hy'
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_of_false (fun h => hy' (Metric.ball_subset_closedBall h)) hj
    have hev : ∀ᶠ y' in 𝓝 y, y' ∈ O₁ ∧ y' ∈ Metric.ball (A w) ρ ∧
        ∀ j, (s j y' ∈ Metric.ball w r ↔ j ∈ S) :=
      Filter.Eventually.and (hO₁.mem_nhds hyO₁)
        (Filter.Eventually.and (Metric.isOpen_ball.mem_nhds hyD) (Filter.eventually_all.2 hT))
    obtain ⟨O, hOsub, hO, hyO⟩ := mem_nhds_iff.1 hev
    refine ⟨O, N, s, S, hO, hyO, fun y' h => (hOsub h).2.1,
      fun j => (hsd j).mono fun y' h => (hOsub h).1, ?_⟩
    intro y' hy'
    obtain ⟨h1, -, h3⟩ := hOsub hy'
    obtain ⟨hsec, hinj, hall⟩ := hs y' h1
    refine ⟨hsec, hinj, ?_⟩
    ext z
    constructor
    · rintro ⟨⟨hzZ, hzW⟩, hzA⟩
      obtain ⟨j, rfl⟩ := hall z hzZ hzA
      exact ⟨j, (h3 j).1 hzW, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨(hsec j).1, (h3 j).2 hj⟩, (hsec j).2⟩

  obtain ⟨c, hc⟩ : ∃ c : (Fin k → ℂ) → ℕ, ∀ y, c y = {z | z ∈ Z ∩ Metric.ball w r ∧ A z = y}.ncard :=
    ⟨_, fun _ => rfl⟩
  have hcount : ∀ {N : ℕ} (s : Fin N → (Fin k → ℂ) → σ → ℂ) (S : Finset (Fin N)) (y' : Fin k → ℂ),
      Function.Injective (fun j => s j y') →
      {z | z ∈ Z ∩ Metric.ball w r ∧ A z = y'} = (fun j => s j y') '' S → c y' = S.card := by
    intro N s S y' hinj heq
    rw [hc, heq, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset]

  have hccont : ContinuousOn c (Metric.ball (A w) ρ ∩ {y | eval y P ≠ 0}) := by
    rintro y ⟨hyD, hy⟩
    obtain ⟨O, N, s, S, hO, hyO, -, -, hOs⟩ := hloc y hyD hy
    have hev : c =ᶠ[𝓝 y] fun _ => S.card := by
      filter_upwards [hO.mem_nhds hyO] with y' hy'
      exact hcount s S y' (hOs y' hy').2.1 (hOs y' hy').2.2
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have hpre : IsPreconnected (Metric.ball (A w) ρ ∩ {y | eval y P ≠ 0}) :=
    ManifoldZerosComplementConnected.isPreconnected_convex_inter_ne_zero Metric.isOpen_ball
      (convex_ball _ _) (hδa.mono (Set.subset_univ _))
  obtain ⟨y₀, hy₀⟩ : (Metric.ball (A w) ρ ∩ {y | eval y P ≠ 0}).Nonempty :=
    hdense.inter_open_nonempty _ Metric.isOpen_ball ⟨A w, Metric.mem_ball_self hρ⟩
  refine ⟨Metric.ball w r, Metric.ball (A w) ρ, c y₀, fun y => eval y P, Metric.isOpen_ball,
    Metric.mem_ball_self hr, ?_, ?_, Metric.isOpen_ball, Metric.mem_ball_self hρ, ?_, ?_, ?_, hδV, ?_, ?_⟩
  · rw [hclos]
    exact isCompact_closedBall w r
  · rw [hclos]
    exact fun z hz => (hrU hz).1
  · rintro z ⟨hzZ, hzW⟩ hzA
    exact hfib z (Metric.ball_subset_closedBall hzW) hzZ hzA
  · rintro z ⟨hzZ, hzW⟩ hzD
    rw [hclos] at hzW
    exact hprop z ⟨hzZ, hzW⟩ hzD
  · exact hδa.differentiableOn.mono (Set.subset_univ _)
  · intro y hyD hy
    obtain ⟨O, N, s, S, hO, hyO, -, hsd, hOs⟩ := hloc y hyD hy
    have hSc : S.card = c y₀ := by
      rw [← hcount s S y (hOs y hyO).2.1 (hOs y hyO).2.2]
      exact hpre.constant hccont ⟨hyD, hy⟩ hy₀
    let e : Fin (c y₀) ≃ S := (S.equivFin.trans (finCongr hSc)).symm
    refine ⟨O, fun i => s (e i : Fin N), hO, hyO, fun i => hsd _, fun y' hy' => ?_⟩
    obtain ⟨-, hinj, heq⟩ := hOs y' hy'
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have hi : s (e i : Fin N) y' ∈ {z | z ∈ Z ∩ Metric.ball w r ∧ A z = y'} := by
        rw [heq]
        exact ⟨_, (e i).2, rfl⟩
      exact hi
    · intro i₁ i₂ h
      exact e.injective (Subtype.ext (hinj h))
    · intro z hz hzA
      have hz' : z ∈ (fun j => s j y') '' S := by
        rw [← heq]
        exact ⟨hz, hzA⟩
      obtain ⟨j, hj, rfl⟩ := hz'
      exact ⟨e.symm ⟨j, hj⟩, by simp⟩
  · rintro z ⟨hzZ, -⟩ ε hε
    obtain ⟨N, hN, hNz⟩ := isolated_of_finite (hfin (A z)) z
    exact hopen z hzZ ⟨N, hN, fun z' h1 h2 h3 => hNz z' h1 ⟨h2, h3⟩⟩ _ (Metric.ball_mem_nhds z hε)

end LocalBranchedCovering

theorem LocalBranchedCovering.proof (hdsc : GroundTheory.Heights₂.Heights.DiscriminantSheetCover.Statement)
    (hiso : IsolatedFibreOpen.Statement) : LocalBranchedCovering.Statement := by
  intro σ _ I w U hI _ hU
  classical

  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap (rename e.symm)
  have hJ : J.IsPrime := Ideal.comap_isPrime _ _
  let Φ : (σ → ℂ) → Fin (Fintype.card σ) → ℂ := fun z j => z (e.symm j)
  let Ψ : (Fin (Fintype.card σ) → ℂ) → σ → ℂ := fun x i => x (e i)
  have hΨΦ : ∀ z, Ψ (Φ z) = z := fun z => funext fun i => by simp [Φ, Ψ]
  have hΦΨ : ∀ x, Φ (Ψ x) = x := fun x => funext fun j => by simp [Φ, Ψ]
  have hΨc : Continuous Ψ := continuous_pi fun i => continuous_apply (e i)
  have hZJ : ∀ x : Fin (Fintype.card σ) → ℂ, (∀ q ∈ J, eval x q = 0) ↔ Ψ x ∈ zeroSetIn I := by
    intro x
    constructor
    · intro hx q hq
      have h1 : rename e q ∈ J := by
        show rename e.symm (rename e q) ∈ I
        rwa [rename_rename, e.symm_comp_self, rename_id_apply]
      have h2 := hx _ h1
      rwa [eval_rename] at h2
    · intro hx q hq
      have h1 := hx _ (Ideal.mem_comap.1 hq)
      have h2 : eval (Ψ x) (rename e.symm q) = eval x q := by
        have h3 : Ψ x ∘ e.symm = x := funext fun j => by simp [Ψ]
        rw [eval_rename, h3]
      rwa [h2] at h1

  obtain ⟨d, hd⟩ := HilbertSamuel.IrreducibleBasicOpenConnected.exists_dim hJ
  obtain ⟨A₀, hA₀⟩ := ComplexSets.LinearNoetherNormalization.proof _ d J hd
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap
    ((Matrix.toLin' A₀).comp (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toLinearMap)
  have hA : ∀ z, A z = A₀ *ᵥ Φ z := fun z => by
    simp [A, Matrix.toLin'_apply, LinearEquiv.funCongrLeft_apply]
    rfl
  have hZc : IsClosed (zeroSetIn I) := by
    have : zeroSetIn I = ⋂ q ∈ I, {z : σ → ℂ | eval z q = 0} := by
      ext z
      simp [zeroSetIn]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

  have hfin : ∀ y, {z | z ∈ zeroSetIn I ∧ A z = y}.Finite := by
    intro y
    refine ((BranchOffHypersurface.fibre_finite J A₀ hA₀ y).image Ψ).subset ?_
    rintro z ⟨hz, hzA⟩
    refine ⟨Φ z, ⟨(hZJ (Φ z)).2 (by rwa [hΨΦ]), by rw [← hA]; exact hzA⟩, hΨΦ z⟩

  obtain ⟨P, Uk, Dk, Nk, s, hP, hUD, -, hcov, -, hfib⟩ := hdsc _ d J A₀ hJ hd hA₀
  have hsheet : ∀ y, eval y P ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (N : ℕ) (t : Fin N → (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ y ∈ O ∧ (∀ j, DifferentiableOn ℂ (t j) O) ∧
      ∀ y' ∈ O, (∀ j, t j y' ∈ zeroSetIn I ∧ A (t j y') = y') ∧ Function.Injective (fun j => t j y') ∧
        ∀ z ∈ zeroSetIn I, A z = y' → z ∈ Set.range (fun j => t j y') := by
    intro y hy
    have hyD : y ∈ ⋃ k, Dk k := by
      by_contra h
      exact hy (hcov h)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hyD
    refine ⟨Uk k, Nk k, fun j y' => Ψ (s k j y'), (hUD k).1, (hUD k).2.2.1 hk, fun j => ?_, ?_⟩
    · exact differentiableOn_pi.2 fun i => differentiableOn_pi.1 ((hUD k).2.2.2 j) (e i)
    intro y' hy'
    obtain ⟨hfe, hinj, -⟩ := hfib k y' hy'
    have hmem : ∀ j, s k j y' ∈ _root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A₀ y' := fun j => by rw [hfe]; exact ⟨j, rfl⟩
    refine ⟨fun j => ⟨(hZJ _).1 (hmem j).1, by rw [hA, hΦΨ]; exact (hmem j).2⟩, ?_, ?_⟩
    · intro j₁ j₂ h
      apply hinj
      have := congrArg Φ h
      simpa only [hΦΨ] using this
    · intro z hz hzA
      have hzf : Φ z ∈ _root_.GroundTheory.Heights₂.Heights.ComplexSets.fibre J A₀ y' :=
        ⟨(hZJ (Φ z)).2 (by rwa [hΨΦ]), by rw [← hA]; exact hzA⟩
      rw [hfe] at hzf
      obtain ⟨j, hj⟩ := hzf
      exact ⟨j, by simp only [hj, hΨΦ]⟩

  have hopen : ∀ z ∈ zeroSetIn I, (∃ N ∈ 𝓝 z, ∀ z' ∈ N, z' ∈ zeroSetIn I → A z' = A z → z' = z) →
      ∀ W' ∈ 𝓝 z, A '' (zeroSetIn I ∩ W') ∈ 𝓝 (A z) := by
    rintro z hz ⟨N, hN, hNz⟩ W' hW'
    have hpre : ∀ T ∈ 𝓝 z, Ψ ⁻¹' T ∈ 𝓝 (Φ z) := fun T hT =>
      hΨc.continuousAt.preimage_mem_nhds (by rw [hΨΦ]; exact hT)
    have hx : Φ z ∈ zeroLocus J := (hZJ (Φ z)).2 (by rwa [hΨΦ])
    have himg := hiso _ d J A₀ (Φ z) ⟨hJ, hd⟩ hx
      ⟨Ψ ⁻¹' N, hpre N hN, fun z' hz'N hz'J hz'A => by
        have h1 := hNz (Ψ z') hz'N ((hZJ z').1 hz'J) (by rw [hA, hA, hΦΨ]; exact hz'A)
        rw [← hΦΨ z', h1]⟩
      (Ψ ⁻¹' W') (hpre W' hW')
    rw [hA]
    refine Filter.mem_of_superset himg ?_
    rintro _ ⟨x', ⟨hx'J, hx'W⟩, rfl⟩
    exact ⟨Ψ x', ⟨(hZJ x').1 hx'J, hx'W⟩, by rw [hA, hΦΨ]⟩
  obtain ⟨W, D, m, δ, h⟩ := LocalBranchedCovering.of_sheets (zeroSetIn I) hZc A P hP hfin hsheet hopen w U hU
  exact ⟨d, A, W, D, m, δ, h⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
