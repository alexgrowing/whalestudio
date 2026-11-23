import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.IsolatedPointsCountPrime
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchNormalisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchInComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeBranchDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurveBranchOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCurvePointDVR
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMinimalPrimePlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceHasBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaceBranchExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimePlaceBranchExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelPointOfPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalisationModelLocalization
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PModelLocalizationMaximalPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalizationAtPrimeQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProjectionLocallyInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchInOneBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchImageNhdOffCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPuncturedBranchSameOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveResidueDegree
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.POrdFiniteNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrderBranchesMeet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeBranchPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveCoordinateGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCurveDiscInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveRegularPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchProperAtPoint
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegBallMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongMono
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.BranchNorm

open MvPolynomial Filter Topology GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

theorem coordinateGraphNear_of_chart {n : ℕ} {X : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ)
    (hO : IsOpen O) (hV : IsOpen V) (hxV : x ∈ V) (hxX : x ∈ X) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hXV : X ∩ V = g '' O) : IsCoordinateGraphNear X x := by
  obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXV ▸ ⟨hxX, hxV⟩

  have hAd : ∀ y ∈ O, A (deriv g y) = 1 := by
    intro y hy
    have h1 : HasDerivAt (fun t ↦ A (g t)) (A (deriv g y)) y :=
      A.hasFDerivAt.comp_hasDerivAt y (hg y hy).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t ↦ A (g t)) 1 y :=
      (hasDerivAt_id' y).congr_of_eventuallyEq (eventually_of_mem (hO.mem_nhds hy) hAg)
    exact h1.unique h2

  obtain ⟨i, hi⟩ : ∃ i, deriv g y₀ i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : deriv g y₀ = 0 := funext h
    simpa [h0] using hAd y₀ hy₀O
  set φ : ℂ → ℂ := fun y ↦ g y i with hφdef
  have hφ : AnalyticOnNhd ℂ φ O := fun y hy ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt (g y)).comp (hg y hy)
  have hφd : ∀ y ∈ O, HasDerivAt φ (deriv g y i) y := fun y hy ↦
    hasDerivAt_pi.1 (hg y hy).differentiableAt.hasDerivAt i

  set U : Set ℂ := O ∩ deriv φ ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := hφ.deriv.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hy₀U : y₀ ∈ U := ⟨hy₀O, by simpa [(hφd y₀ hy₀O).deriv] using hi⟩
  have hs : HasStrictDerivAt φ (deriv g y₀ i) y₀ := by
    simpa [(hφd y₀ hy₀O).deriv] using (hφ y₀ hy₀O).hasStrictDerivAt
  set e := ((hs.hasStrictFDerivAt_equiv hi).toOpenPartialHomeomorph φ).restrOpen U hU with hedef
  have he : ∀ y, e y = φ y := fun _ ↦ rfl
  have hsrc : ∀ {y}, y ∈ e.source → y ∈ U := fun hy ↦ hy.2
  have hy₀e : y₀ ∈ e.source := ⟨(hs.hasStrictFDerivAt_equiv hi).mem_toOpenPartialHomeomorph_source, hy₀U⟩
  refine ⟨hxX, V ∩ A ⁻¹' e.source ∩ (fun z ↦ z i) ⁻¹' e.target,
    (hV.inter (e.open_source.preimage A.continuous)).inter (e.open_target.preimage (continuous_apply i)),
    ⟨⟨hxV, ?_⟩, ?_⟩, i, e.target, fun t ↦ g (e.symm t), e.open_target, ?_, ?_, ?_⟩
  · show A x ∈ e.source
    rw [← hgy₀, hAg y₀ hy₀O]
    exact hy₀e
  · show x i ∈ e.target
    rw [← hgy₀, show g y₀ i = e y₀ from rfl]
    exact e.map_source hy₀e
  · intro t ht
    have hyt := hsrc (e.map_target ht)
    have hder : HasDerivAt e (deriv φ (e.symm t)) (e.symm t) :=
      (hφ _ hyt.1).differentiableAt.hasDerivAt
    exact ((hg _ hyt.1).differentiableAt.comp t
      (e.hasDerivAt_symm ht hyt.2 hder).differentiableAt).differentiableWithinAt
  · intro t ht
    exact e.right_inv ht
  · rintro z ⟨⟨hzV, hzA⟩, hzi⟩
    constructor
    · intro hzX
      obtain ⟨y, hyO, rfl⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
      have hye : y ∈ e.source := by simpa [hAg y hyO] using hzA
      refine ⟨hzi, ?_⟩
      show g (e.symm (e y)) = g y
      rw [e.left_inv hye]
    · rintro ⟨ht, hgz⟩
      have hyO := (hsrc (e.map_target ht)).1
      have : z ∈ X ∩ V := hXV ▸ ⟨_, hyO, hgz⟩
      exact this.1

theorem curveCoordinateGraph : CurveCoordinateGraph.Statement := by
  intro n I q _ hdim
  obtain ⟨N, hN, hNx⟩ := GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre n I q hdim
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun x hxZ hxb hxq ↦ ?_⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hZV⟩ := hNx x ⟨hxZ, hball hxb⟩ hxq
  exact coordinateGraphNear_of_chart A O V g hO hV hxV hxZ hg hAg hZV

theorem puncturedCurveDiscInverse : PuncturedCurveDiscInverse.Statement := by
  have hG := curveCoordinateGraph
  have hD := InjectiveHolomorphicDerivNeZero.proof
  intro n I q hrad hdim
  obtain ⟨ε, hε, hgraph⟩ := hG n I q hrad hdim
  refine ⟨ε, hε, fun φ σ₀ δ hδ hφd hφi hφZ hφε hφq ↦ ?_⟩
  have hσ₀ : σ₀ ∈ Metric.ball σ₀ δ := Metric.mem_ball_self hδ
  obtain ⟨-, W, hWo, hxW, i, V, g, -, -, -, hW⟩ := hgraph (φ σ₀) (hφZ hσ₀) hφε hφq
  set f : ℂ → ℂ := fun σ ↦ φ σ i with hf
  set D : Set ℂ := Metric.ball σ₀ δ ∩ φ ⁻¹' W with hDdef
  have hDo : IsOpen D := hφd.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hWo
  have hσD : σ₀ ∈ D := ⟨hσ₀, hxW⟩
  have hφg : ∀ σ ∈ D, g (f σ) = φ σ := fun σ hσ ↦ ((hW _ hσ.2).1 (hφZ hσ.1)).2
  have hfd : DifferentiableOn ℂ f D := (differentiableOn_pi.1 hφd i).mono Set.inter_subset_left
  have hfi : Set.InjOn f D := fun s hs t ht h ↦ hφi hs.1 ht.1 (by rw [← hφg s hs, ← hφg t ht, h])
  have hfa : AnalyticAt ℂ f σ₀ := hfd.analyticAt (hDo.mem_nhds hσD)
  have hf' : deriv f σ₀ ≠ 0 := hD D f hDo hfd hfi σ₀ hσD
  set h := hfa.hasStrictDerivAt.localInverse f (deriv f σ₀) σ₀ hf' with hhdef
  have hha : AnalyticAt ℂ h (f σ₀) := hfa.analyticAt_localInverse hf'
  have hh0 : h (f σ₀) = σ₀ := HasStrictFDerivAt.localInverse_apply_image ..
  have hev : ∀ᶠ y in 𝓝 (f σ₀), AnalyticAt ℂ h y ∧ f (h y) = y ∧ h y ∈ D :=
    hha.eventually_analyticAt.and ((hfa.hasStrictDerivAt.eventually_right_inverse hf').and
      (hha.continuousAt.preimage_mem_nhds (by rw [hh0]; exact hDo.mem_nhds hσD)))
  obtain ⟨T, hTsub, hTo, hT⟩ := mem_nhds_iff.1 hev
  refine ⟨W ∩ (fun z ↦ z i) ⁻¹' T, hWo.inter (hTo.preimage (continuous_apply i)), ⟨hxW, hT⟩,
    fun z ↦ h (z i), fun z hz ↦ ?_, fun z ⟨hzZ, hzW, hzT⟩ ↦ ?_⟩
  · exact ((hTsub hz.2).1.differentiableAt.comp z (differentiableAt_apply i z)).differentiableWithinAt
  · obtain ⟨-, hfh, hhD⟩ := hTsub hzT
    refine ⟨h (z i), hhD.1, ?_, rfl⟩
    rw [← hφg _ hhD, hfh]
    exact ((hW z hzW).1 hzZ).2

theorem normalCurveBranchOrder : NormalCurveBranchOrder.Statement :=
  NormalCurveBranchOrder.proof NormalCurvePointDVR.proof GroundTheory.Heights₂.Heights.AutoClose.UniformiserBranchSimpleZero

theorem normalModelOpenMappingCurve (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (U : Set (Fin 1 → ℂ)) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ)
    (_hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ))
    (hU : IsOpen U) (hφd : DifferentiableOn ℂ φ U) (hφi : Set.InjOn φ U)
    (hφZ : Set.MapsTo φ U (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal)) :
    ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ φ '' U = IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ O := by
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have key : ∀ τ ∈ U, ∃ W : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen W ∧ φ τ ∈ W ∧
      IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ W ⊆ φ '' U := by
    intro τ hτ
    obtain ⟨A, O, V, g, hO, hV, hwV, hg, hAg, hZV⟩ :=
      GroundTheory.Heights₂.Heights.AutoClose.NormalCurveRegularPoint (Fin n ⊕ Fin M.m) M.ideal (φ τ) M.isPrime
        M.isIntegrallyClosed hdim' (hφZ hτ)
    set D : Set (Fin 1 → ℂ) := U ∩ φ ⁻¹' V with hD
    have hDo : IsOpen D := hφd.continuousOn.isOpen_inter_preimage hU hV
    have hφg : ∀ σ ∈ D, ∃ y ∈ O, g y = φ σ := fun σ hσ ↦ by
      have : φ σ ∈ g '' O := hZV ▸ ⟨hφZ hσ.1, hσ.2⟩
      exact this
    have hgA : ∀ σ ∈ D, g (A (φ σ)) = φ σ := fun σ hσ ↦ by
      obtain ⟨y, hy, hyφ⟩ := hφg σ hσ
      rw [← hyφ, hAg y hy]
    have hhd : DifferentiableOn ℂ (fun σ ↦ A (φ σ)) D :=
      A.differentiable.comp_differentiableOn (hφd.mono Set.inter_subset_left)
    have hhi : Set.InjOn (fun σ ↦ A (φ σ)) D := fun s hs t ht h ↦
      hφi hs.1 ht.1 (by rw [← hgA s hs, ← hgA t ht]; exact congrArg g h)
    have hopen : IsOpen ((fun σ ↦ A (φ σ)) '' D) :=
      GroundTheory.Heights₂.Heights.AutoClose.injective_holomorphic_open_holds 1 D _ hDo hhd hhi
    refine ⟨V ∩ A ⁻¹' ((fun σ ↦ A (φ σ)) '' D), hV.inter (hopen.preimage A.continuous),
      ⟨hwV, τ, ⟨hτ, hwV⟩, rfl⟩, ?_⟩
    rintro z ⟨hzZ, hzV, σ, hσ, hσz⟩
    obtain ⟨y, hy, rfl⟩ : z ∈ g '' O := hZV ▸ ⟨hzZ, hzV⟩
    refine ⟨σ, hσ.1, ?_⟩
    rw [← hgA σ hσ]
    have : A (φ σ) = y := hσz.trans (hAg y hy)
    rw [this]
  choose! W hWo hWm hWs using key
  refine ⟨⋃ τ ∈ U, W τ, isOpen_biUnion fun τ hτ ↦ hWo τ hτ, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact ⟨hφZ hτ, Set.mem_biUnion hτ (hWm τ hτ)⟩
  · rintro z ⟨hzZ, hz⟩
    obtain ⟨τ, hτ, hzW⟩ := Set.mem_iUnion₂.1 hz
    exact hWs τ hτ ⟨hzZ, hzW⟩

def BranchLiftCurve : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (γ : VarBranch J 1 p),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    ∃ Γ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
      DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) ∧
      (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords (Γ τ) = γ.toFun τ) ∧
      ∀ V ⊆ Metric.ball 0 γ.radius, IsOpen V →
        ∃ O : Set (Fin n ⊕ Fin M.m → ℂ), IsOpen O ∧ Γ '' V = IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ O

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets in
theorem branchLiftCurve : BranchLiftCurve := by
  have hR := RiemannExtensionAnalytic.proof
  have hB := GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds
  have hP := NormalModelProper.proof
  have hO := normalModelOpenMappingCurve
  intro n J p M γ hJ hdim
  set Δ := Metric.ball (0 : Fin 1 → ℂ) γ.radius with hΔ
  have hγd : DifferentiableOn ℂ γ.toFun Δ := γ.differentiableOn
  have hγZ : ∀ τ ∈ Δ, γ.toFun τ ∈ zeroSetIn J := fun τ hτ => γ.mapsTo hτ
  choose a b hbJ hab using M.birational
  have hpoly : ∀ q : MvPolynomial (Fin n) ℂ, Differentiable ℂ (fun z : Fin n → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq =>
      simp only [eval_add]
      exact hp.add hq
    | mul_X p i hp =>
      simp only [eval_mul, eval_X]
      exact hp.mul (differentiable_apply i)
  have hcomp : ∀ q, DifferentiableOn ℂ (fun τ => eval (γ.toFun τ) q) Δ := fun q =>
    (hpoly q).comp_differentiableOn hγd
  set g : (Fin 1 → ℂ) → ℂ := fun τ => eval (γ.toFun τ) (∏ i, b i) with hg
  have hBJ : (∏ i, b i) ∉ J := fun h => by
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hJ)).1 h
    exact hbJ i hi
  have hgne : ∀ V, IsOpen V → V ⊆ Δ → V.Nonempty → ∃ t ∈ V, g t ≠ 0 := fun V hV hVΔ hne =>
    hB n 1 J _ V γ.toFun hJ hdim hBJ hV hne (hγd.mono hVΔ) (γ.injOn.mono hVΔ)
      fun τ hτ => hγZ τ (hVΔ hτ)
  have hbne : ∀ τ, g τ ≠ 0 → ∀ i, eval (γ.toFun τ) (b i) ≠ 0 := fun τ hτ i h =>
    hτ (by simp only [hg, map_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
  set f : Fin M.m → (Fin 1 → ℂ) → ℂ := fun i τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)
  have hgraph : ∀ τ ∈ Δ, g τ ≠ 0 → (Sum.elim (γ.toFun τ) fun i => f i τ) ∈ zeroSetIn M.ideal :=
    fun τ hτ hgτ => M.graph_mem_zeroSetIn a b hab _ (hγZ τ hτ) (hbne τ hgτ)
  have hfd : ∀ i, DifferentiableOn ℂ (f i) (Δ ∩ {t | g t ≠ 0}) := fun i τ hτ => by
    have h1 := (hcomp (a i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    have h2 := (hcomp (b i) τ hτ.1).mono (Set.inter_subset_left (t := {t | g t ≠ 0}))
    show DifferentiableWithinAt ℂ (fun τ => eval (γ.toFun τ) (a i) / eval (γ.toFun τ) (b i)) _ τ
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv (hbne τ hτ.2 i))
  have hbdd : ∀ i, ∀ τ ∈ Δ, ∃ N ∈ 𝓝 τ, Bornology.IsBounded (f i '' (N ∩ Δ ∩ {t | g t ≠ 0})) := by
    intro i τ hτ
    obtain ⟨ε, hε, hεΔ⟩ := Metric.isOpen_iff.1 Metric.isOpen_ball τ hτ
    have hsub : Metric.closedBall τ (ε / 2) ⊆ Δ :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεΔ
    have hK : Bornology.IsBounded (γ.toFun '' Metric.closedBall τ (ε / 2)) :=
      ((isCompact_closedBall τ (ε / 2)).image_of_continuousOn (hγd.continuousOn.mono hsub)).isBounded
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hP n J M _ hK)
    refine ⟨Metric.closedBall τ (ε / 2), Metric.closedBall_mem_nhds τ (by linarith),
      isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩⟩
    rintro _ ⟨t, ⟨⟨ht, htΔ⟩, hgt⟩, rfl⟩
    have hw := hC _ ⟨hgraph t htΔ hgt, ⟨t, ht, rfl⟩⟩
    exact (norm_le_pi_norm (Sum.elim (γ.toFun t) fun i => f i t) (Sum.inr i)).trans hw
  choose F hFd hFeq using fun i => hR 1 Δ g (f i) Metric.isOpen_ball
    ((hpoly _).comp_differentiableOn hγd) hgne (hfd i) (hbdd i)
  set Γ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ := fun τ => Sum.elim (γ.toFun τ) fun i => F i τ with hΓ
  have hΓd : DifferentiableOn ℂ Γ Δ := by
    refine differentiableOn_pi.2 fun s => ?_
    rcases s with j | i
    · simpa [hΓ] using differentiableOn_pi.1 hγd j
    · simpa [hΓ] using hFd i
  have hdense : Δ ⊆ closure (Δ ∩ {t | g t ≠ 0}) := by
    intro τ hτ
    rw [mem_closure_iff]
    intro o ho hτo
    obtain ⟨t, ⟨hto, htΔ⟩, hgt⟩ := hgne (o ∩ Δ) (ho.inter Metric.isOpen_ball)
      Set.inter_subset_right ⟨τ, hτo, hτ⟩
    exact ⟨t, hto, htΔ, hgt⟩
  have hΓZ : ∀ τ ∈ Δ, Γ τ ∈ zeroSetIn M.ideal := by
    intro τ hτ q hq
    have heq : Set.EqOn (fun t => eval (Γ t) q) (fun _ => (0 : ℂ)) (Δ ∩ {t | g t ≠ 0}) := by
      intro t ht
      have hΓt : Γ t = Sum.elim (γ.toFun t) fun i => f i t := by
        simp only [hΓ]
        congr 1
        funext i
        exact hFeq i ht
      simp only [hΓt]
      exact hgraph t ht.1 ht.2 q hq
    exact heq.of_subset_closure ((MvPolynomial.continuous_eval q).comp_continuousOn hΓd.continuousOn)
      continuousOn_const Set.inter_subset_left hdense hτ
  have hΓinj : Set.InjOn Γ Δ := fun s hs t ht hst =>
    γ.injOn hs ht (by
      have := congrArg firstCoords hst
      exact this)
  refine ⟨Γ, hΓd, fun τ hτ => ⟨hΓZ τ hτ, rfl⟩, fun V hV hVo => ?_⟩
  exact hO n J M V Γ hJ hdim hVo (hΓd.mono hV) (hΓinj.mono hV) fun τ hτ => hΓZ τ (hV hτ)

theorem primeBranchPlace : PrimeBranchPlace.Statement := by
  have hD := PrimeBranchDimOne.proof
  have hL := branchLiftCurve
  have hA := NormalModelPlace.proof
  have hO := normalCurveBranchOrder
  intro n J q c hJ hdim
  have hdim1 := hD n J q c hJ hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n J q M c hJ hdim1
  have hr := c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 c.radius := Metric.mem_ball_self hr

  have hinj : Set.InjOn Γ (Metric.ball 0 c.radius) := fun a ha b hb hab ↦
    c.injOn ha hb (by rw [← (hΓ a ha).2, ← (hΓ b hb).2, hab])
  obtain ⟨P, hP⟩ := hA n J q M (Γ 0) hJ (hΓ 0 h0).1 ((hΓ 0 h0).2.trans c.map_zero)
  refine ⟨P, fun f ↦ ?_⟩
  rw [hP f, hO n J M (Γ 0) c.radius Γ hJ hdim1 hr hΓd hinj (fun τ hτ ↦ (hΓ τ hτ).1) rfl]

  unfold branchOrder
  apply analyticOrderAt_congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    rw [mem_ball_zero_iff] at hτ ⊢
    exact (pi_norm_const_le τ).trans_lt hτ
  rw [eval_rename, ← (hΓ _ hτ').2]
  rfl

theorem sameOrderBranchesMeet : SameOrderBranchesMeet.Statement := by
  have hC := GroundTheory.Heights₂.Heights.AutoClose.BranchInCurveComponent
  have hO := GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre
  have hL := branchLiftCurve
  intro n I q c c' _ hdim hord
  obtain ⟨J, hJmin, hJdim, hev⟩ := hC n I q c hdim
  have hJ : J.IsPrime := hJmin.1.1
  have htop : ∀ f ∈ J, branchOrder c f = ⊤ := fun f hf ↦ by
    refine analyticOrderAt_eq_top.2 ?_
    have hι : Tendsto (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (𝓝 0) (𝓝 0) :=
      (continuous_pi fun _ ↦ continuous_id).tendsto' _ _ rfl
    filter_upwards [hι.eventually hev] with τ hτ using hτ f hf
  have hev' := c'.eventually_mem_zeroSet J fun f hf ↦ (hord f).symm.trans (htop f hf)
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', hεJ'⟩ := Metric.eventually_nhds_iff_ball.1 hev'
  let γ := c.restrictInto J ε hε hεJ
  let γ' := c'.restrictInto J ε' hε' hεJ'
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n J q M γ hJ hJdim
  obtain ⟨Γ', hΓ'd, hΓ', hΓ'o⟩ := hL n J q M γ' hJ hJdim
  have hw : Γ 0 = Γ' 0 := hO n J q M γ γ' Γ Γ' hJ hJdim hΓd hΓ hΓ'd hΓ' hord
  obtain ⟨U, hUo, hU⟩ := hΓ'o _ subset_rfl Metric.isOpen_ball
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 γ.radius := Metric.mem_ball_self γ.radius_pos
  have hΓ0U : Γ 0 ∈ U := by
    rw [hw]
    exact (hU ▸ Set.mem_image_of_mem Γ' (Metric.mem_ball_self γ'.radius_pos)).2
  have hcont : ContinuousAt Γ 0 := hΓd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 γ.radius_pos)
  have hnear : ∀ᶠ τ in 𝓝[≠] (0 : Fin 1 → ℂ), τ ≠ 0 ∧ τ ∈ Metric.ball 0 γ.radius ∧ Γ τ ∈ U := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 γ.radius_pos),
      nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hUo.mem_nhds hΓ0U))] with τ h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨τ, hτ0, hτ, hτU⟩ := hnear.exists
  obtain ⟨τ', hτ', hτ'eq⟩ : Γ τ ∈ Γ' '' Metric.ball 0 γ'.radius := hU ▸ ⟨(hΓ τ hτ).1, hτU⟩
  have hτc : τ ∈ Metric.ball 0 c.radius := Metric.ball_subset_ball (min_le_right _ _) hτ
  refine ⟨c.toFun τ, ⟨⟨τ, hτc, rfl⟩, ⟨τ', Metric.ball_subset_ball (min_le_right _ _) hτ', ?_⟩⟩, fun hq ↦ hτ0 ?_⟩
  · have e1 := (hΓ' τ' hτ').2
    have e2 := (hΓ τ hτ).2
    rw [hτ'eq] at e1
    exact e1.symm.trans e2
  · exact c.injOn hτc (Metric.mem_ball_self c.radius_pos) (hq.trans c.map_zero.symm)

theorem primePlaceBranchExists : PrimePlaceBranchExists.Statement :=
  PrimePlaceBranchExists.proof
    (NormalModelPointOfPlace.proof NormalisationModelLocalization.full ModelLocalizationMaximalPoint.proof
      LocalizationAtPrimeQuotient.proof)
    GroundTheory.Heights₂.Heights.AutoClose.NormalModelDisc NormalModelProjectionLocallyInjective.proof normalCurveBranchOrder

theorem placeHasBranch : PlaceHasBranch.Statement :=
  PlaceHasBranch.proof
    (PlaceBranchExists.proof GroundTheory.Heights₂.Heights.AutoClose.PlaceOnComponent primePlaceBranchExists)
    (PuncturedBranchInOneBranch.proof
      (BranchImageNhdOffCentre.proof GroundTheory.Heights₂.Heights.AutoClose.CurveRegularOffCentre))
    (PuncturedBranchSameOrder.proof puncturedCurveDiscInverse)

theorem branchNormalisation : BranchNormalisation.Statement :=
  BranchNormalisation.proof GroundTheory.Heights₂.Heights.AutoClose.BranchGermDimOne
    (BranchPlace.proof BranchInComponent.proof primeBranchPlace MinimalPrimePlace.proof)
    sameOrderBranchesMeet placeHasBranch GroundTheory.Heights₂.Heights.AutoClose.OrdDeterminesPlace
    CurveResidueDegree.proof OrdFiniteNonZeroDivisor.proof

end

end GlobalTheory.CompanionTheory.BranchNorm
