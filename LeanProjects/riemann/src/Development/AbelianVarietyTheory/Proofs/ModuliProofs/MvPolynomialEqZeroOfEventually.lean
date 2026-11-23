import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open Filter Topology

namespace GlobalTheory.CountableFibres

open Filter Topology in

theorem _root_.GlobalTheory.CountableFibres.exists_injective_fderiv {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) {f : E → F}
    (hf : ∀ z ∈ U, ContDiffAt ℂ 1 f z) (hc : ∀ z ∈ U, {z' ∈ U | f z' = f z}.Countable) :
    ∃ z ∈ U, Function.Injective (fderiv ℂ f z) := by
  haveI := FiniteDimensional.complete ℂ E
  set rk : E → ℕ := fun z => Module.finrank ℂ (LinearMap.range (fderiv ℂ f z : E →ₗ[ℂ] F))
  have hbdd : BddAbove (rk '' U) := ⟨Module.finrank ℂ F, by
    rintro _ ⟨z, -, rfl⟩; exact Submodule.finrank_le _⟩
  obtain ⟨z₀, hz₀, hr⟩ : sSup (rk '' U) ∈ rk '' U := Nat.sSup_mem (hne.image _) hbdd
  have hmax : ∀ z ∈ U, rk z ≤ rk z₀ := fun z hz => hr ▸ le_csSup hbdd ⟨z, hz, rfl⟩
  refine ⟨z₀, hz₀, ?_⟩
  by_contra hinj
  set L := fderiv ℂ f z₀
  set W := LinearMap.range (L : E →ₗ[ℂ] F)
  haveI := FiniteDimensional.complete ℂ W
  obtain ⟨P₀, hP₀⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  set P : F →L[ℂ] W := LinearMap.toContinuousLinearMap P₀
  have hPL : ∀ x, P (L x) = ⟨L x, x, rfl⟩ := fun x => by
    have := congrArg (fun φ => φ ⟨L x, x, rfl⟩) hP₀
    simpa [P] using this
  have hsurj : LinearMap.range ((P.comp L : E →L[ℂ] W) : E →ₗ[ℂ] W) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨w, x, rfl⟩
    exact ⟨x, by simp [hPL]⟩
  have hg : HasStrictFDerivAt (fun x => P (f x)) (P.comp L) z₀ :=
    P.hasStrictFDerivAt.comp z₀ ((hf z₀ hz₀).hasStrictFDerivAt one_ne_zero)

  obtain ⟨R₀, hR₀⟩ := LinearMap.exists_rightInverse_of_surjective _ hsurj
  set R : W →L[ℂ] E := LinearMap.toContinuousLinearMap R₀
  have hΦ : ContinuousAt (fun z => (P.comp (fderiv ℂ f z)).comp R) z₀ :=
    (continuousAt_const.clm_comp ((hf z₀ hz₀).continuousAt_fderiv one_ne_zero)).clm_comp
      continuousAt_const
  have hΦ₀ : (P.comp L).comp R = 1 := by
    ext1 w
    exact congrArg (fun φ => φ w) hR₀
  have hunit : ∀ᶠ z in 𝓝 z₀, IsUnit ((P.comp (fderiv ℂ f z)).comp R) :=
    hΦ.eventually (Units.isOpen.mem_nhds (by
      show IsUnit ((P.comp L).comp R)
      rw [hΦ₀]; exact isUnit_one))
  have hW : Module.finrank ℂ W = rk z₀ := rfl
  have hker : ∀ᶠ z in 𝓝 z₀, ∀ v, P (fderiv ℂ f z v) = 0 → fderiv ℂ f z v = 0 := by
    filter_upwards [hunit, hU.mem_nhds hz₀] with z hz hzU
    obtain ⟨b, hb⟩ := hz.exists_right_inv
    have hran : LinearMap.range ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro w
      refine ⟨R (b w), ?_⟩
      have := congrArg (fun φ : W →L[ℂ] W => φ w) hb
      simpa using this
    have h1 := LinearMap.finrank_range_add_finrank_ker
      ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W)
    have h2 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ f z : E →ₗ[ℂ] F)
    rw [hran, finrank_top, hW] at h1
    have h3 := hmax z hzU
    have hle : LinearMap.ker (fderiv ℂ f z : E →ₗ[ℂ] F) ≤
        LinearMap.ker ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) := fun v hv => by
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
      simp [hv]
    have heq := Submodule.eq_of_le_of_finrank_le hle (by simp only [rk] at h1 h3; omega)
    intro v hv
    have hv' : v ∈ LinearMap.ker ((P.comp (fderiv ℂ f z) : E →L[ℂ] W) : E →ₗ[ℂ] W) := by
      simpa using hv
    rw [← heq] at hv'
    simpa using hv'

  set K := LinearMap.ker ((P.comp L : E →L[ℂ] W) : E →ₗ[ℂ] W)
  haveI : Nontrivial K := by
    rw [Submodule.nontrivial_iff_ne_bot]
    intro hK
    apply hinj
    intro x y hxy
    have : x - y ∈ K := by
      simp only [K, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        map_sub, hxy, sub_self, map_zero]
    rw [hK, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  set Ψ := hg.implicitToOpenPartialHomeomorph _ _ hsurj
  set ψ : K → E := fun t => Ψ.symm (P (f z₀), t)
  have hψ0 : ψ 0 = z₀ := hg.implicitFunction_apply_image hsurj
  have hψc : ContinuousAt ψ 0 := (hg.to_implicitFunction hsurj).continuousAt
  have htend : Tendsto (fun t : K => (P (f z₀), t)) (𝓝 0) (𝓝 (P (f z₀), 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hlev : ∀ᶠ t in 𝓝 (0 : K), P (f (ψ t)) = P (f z₀) :=
    htend.eventually (hg.map_implicitFunction_eq hsurj)
  have hinv : ∀ᶠ t in 𝓝 (0 : K), (Ψ (ψ t)).2 = t := by
    have h := Ψ.open_target.mem_nhds (hg.mem_implicitToOpenPartialHomeomorph_target hsurj)
    filter_upwards [htend h] with t ht
    simp only [ψ]
    rw [Ψ.right_inv (by exact ht)]
  have hdiff : ∀ᶠ t in 𝓝 (0 : K), DifferentiableAt ℂ ψ t := by
    have hcc : K.ClosedComplemented :=
      ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range (P.comp L)
    let D := hg.implicitFunctionDataOfComplemented _ _ hsurj hcc
    have hl : ContDiffAt ℂ 1 D.leftFun D.pt :=
      (P.contDiff.contDiffAt).comp z₀ (hf z₀ hz₀)
    have hr : ContDiffAt ℂ 1 D.rightFun D.pt := by
      show ContDiffAt ℂ 1 (fun x => (Classical.choose hcc) (x - z₀)) z₀
      exact ((Classical.choose hcc).contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
    have hp : D.prodFun D.pt = (P (f z₀), 0) := by
      rw [ImplicitFunctionData.prodFun_apply]
      show (P (f z₀), (Classical.choose hcc) (z₀ - z₀)) = _
      rw [sub_self, map_zero]
    have hcd := (D.contDiffAt_implicitFunction hl hr one_ne_zero).eventually (by simp)
    rw [hp] at hcd
    filter_upwards [htend.eventually hcd] with t ht
    exact (ht.differentiableAt one_ne_zero).comp t
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hnear : ∀ᶠ t in 𝓝 (0 : K), ψ t ∈ U ∧
      (∀ v, P (fderiv ℂ f (ψ t) v) = 0 → fderiv ℂ f (ψ t) v = 0) := by
    have h := (hU.eventually_mem hz₀).and hker
    rw [← hψ0] at h
    exact hψc.eventually h
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlev.and (hinv.and (hdiff.and hnear)))
  set S := Metric.ball (0 : K) ε
  have hderiv : ∀ t ∈ S, fderiv ℂ (fun s => f (ψ s)) t = 0 := by
    intro t ht
    obtain ⟨-, -, hdt, htU, hkt⟩ := hball t ht
    have hft : DifferentiableAt ℂ f (ψ t) := (hf _ htU).differentiableAt one_ne_zero
    have hloc : (fun s => P (f (ψ s))) =ᶠ[𝓝 t] fun _ => P (f z₀) :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ht) fun s hs => (hball s hs).1
    have hcomp : HasFDerivAt (fun s => f (ψ s)) ((fderiv ℂ f (ψ t)).comp (fderiv ℂ ψ t)) t :=
      hft.hasFDerivAt.comp t hdt.hasFDerivAt
    have hcompP : HasFDerivAt (fun s => P (f (ψ s)))
        (P.comp ((fderiv ℂ f (ψ t)).comp (fderiv ℂ ψ t))) t := P.hasFDerivAt.comp t hcomp
    have hzero : HasFDerivAt (fun s => P (f (ψ s))) (0 : K →L[ℂ] W) t :=
      (hasFDerivAt_const (P (f z₀)) t).congr_of_eventuallyEq hloc
    have h0 := hcompP.unique hzero
    rw [hcomp.fderiv]
    ext1 v
    apply hkt
    have := congrArg (fun φ : K →L[ℂ] W => φ v) h0
    simpa using this
  have hconst : ∀ t ∈ S, f (ψ t) = f z₀ := by
    intro t ht
    have hdon : DifferentiableOn ℂ (fun s => f (ψ s)) S := fun s hs =>
      (((hf _ (hball s hs).2.2.2.1).differentiableAt one_ne_zero).comp s
        (hball s hs).2.2.1).differentiableWithinAt
    have := Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball (0 : K) ε).isPreconnected
      hdon (fun s hs => hderiv s hs) ht (Metric.mem_ball_self hε)
    rwa [hψ0] at this
  have hcount : S.Countable := by
    refine Set.MapsTo.countable_of_injOn (f := ψ) (t := {z' ∈ U | f z' = f z₀}) (fun t ht => ⟨(hball t ht).2.2.2.1, hconst t ht⟩)
      ?_ (hc z₀ hz₀)
    intro s hs t ht hst
    rw [← (hball s hs).2.1, ← (hball t ht).2.1]
    simp only [ψ] at hst ⊢
    rw [hst]
  obtain ⟨x, hx, hxS⟩ := (hcount.dense_compl ℂ).inter_open_nonempty S Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  exact hxS hx

theorem exists_rows {d : ℕ} {I : Type} (L : (Fin d → ℂ) →ₗ[ℂ] (I → ℂ))
    (hL : Function.Injective L) :
    ∃ a : Fin d → I, ∀ x, (∀ i, L x (a i) = 0) → x = 0 := by
  let φ : I → Module.Dual ℂ (Fin d → ℂ) := fun b => (LinearMap.proj b) ∘ₗ L
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ φ
  have : Finite κ := hli.finite
  let _ : Fintype κ := Fintype.ofFinite κ
  have hker : ∀ x, (∀ k, L x (a k) = 0) → x = 0 := by
    intro x hx
    apply hL
    rw [map_zero]
    funext b
    have hb : φ b ∈ Submodule.span ℂ (Set.range (φ ∘ a)) := by
      rw [hspan]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hle : Submodule.span ℂ (Set.range (φ ∘ a)) ≤
        LinearMap.ker (Module.Dual.eval ℂ (Fin d → ℂ) x) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hx k
    exact hle hb
  have h1 : Fintype.card κ ≤ d := by
    simpa using hli.fintype_card_le_finrank
  have h2 : d ≤ Fintype.card κ := by
    have : Function.Injective (LinearMap.funLeft ℂ ℂ a ∘ₗ L) := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      exact hker x fun k => congrFun hx k
    simpa using LinearMap.finrank_le_finrank_of_injective this
  let e : Fin d ≃ κ := (Fintype.equivFinOfCardEq (le_antisymm h1 h2)).symm
  refine ⟨a ∘ e, fun x hx => hker x fun k => ?_⟩
  simpa using hx (e.symm k)

open Filter Topology in

theorem _root_.GlobalTheory.CountableFibres.exists_independent_ratios :
    ∀ (d : ℕ) (I : Type) [Finite I] (B : Set (Fin d → ℂ)) (θ : (Fin d → ℂ) → I → ℂ), IsOpen B →
      IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) →
      (∀ z ∈ B, θ z ≠ 0 ∧ {z' ∈ B | ∃ c : ℂ, θ z' = c • θ z}.Countable) →
      ∃ (a₀ : I) (a : Fin d → I), (∃ z ∈ B, θ z a₀ ≠ 0) ∧ ∀ F : MvPolynomial (Fin d) ℂ,
        (∀ z ∈ B, θ z a₀ ≠ 0 → MvPolynomial.eval (fun i => θ z (a i) / θ z a₀) F = 0) → F = 0 := by
  intro d I _ B θ hB _ hBne hdiff hfib
  haveI := Fintype.ofFinite I
  have hO : _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement := _root_.ReciprocityTheory.AnForm.Osgood.osgood
  unfold _root_.ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
  have hAn : ∀ a, AnalyticOnNhd ℂ (fun z => θ z a) B := fun a => hO d B _ hB (hdiff a)
  obtain ⟨z₁, hz₁⟩ := hBne
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, θ z₁ a₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact (hfib z₁ hz₁).1 (funext h)
  set U := B ∩ (fun z => θ z a₀) ⁻¹' {0}ᶜ
  have hUo : IsOpen U := (hAn a₀).continuousOn.isOpen_inter_preimage hB isOpen_compl_singleton
  have hUB : ∀ z ∈ U, z ∈ B ∧ θ z a₀ ≠ 0 := fun z hz => hz
  set ρ : (Fin d → ℂ) → I → ℂ := fun z b => θ z b / θ z a₀
  have hρ : ∀ z ∈ U, ContDiffAt ℂ 1 ρ z := fun z hz =>
    contDiffAt_pi.2 fun b => ((hAn b z hz.1).contDiffAt).div ((hAn a₀ z hz.1).contDiffAt) hz.2
  have hρc : ∀ z ∈ U, {z' ∈ U | ρ z' = ρ z}.Countable := by
    intro z hz
    refine (hfib z hz.1).2.mono ?_
    rintro z' ⟨hz'U, hz'⟩
    refine ⟨hz'U.1, θ z' a₀ / θ z a₀, funext fun b => ?_⟩
    have h := congrFun hz' b
    simp only [ρ] at h
    have h1 := hz.2
    have h2 := hz'U.2
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at h1 h2
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp at h ⊢
    linear_combination h
  obtain ⟨z₂, hz₂, hinj⟩ := _root_.GlobalTheory.CountableFibres.exists_injective_fderiv hUo ⟨z₁, hz₁, ha₀⟩ hρ hρc
  set D := fderiv ℂ ρ z₂

  set v : I → Module.Dual ℂ (Fin d → ℂ) := fun b => (LinearMap.proj b).comp (D : (Fin d → ℂ) →ₗ[ℂ] I → ℂ)
  obtain ⟨κ, c, hc, hspan, hli⟩ := exists_linearIndependent' ℂ v
  haveI : Finite κ := Finite.of_injective c hc
  haveI := Fintype.ofFinite κ
  have hkill : ∀ y, (∀ k, v (c k) y = 0) → y = 0 := by
    intro y hy
    have hle : Submodule.span ℂ (Set.range (v ∘ c)) ≤ LinearMap.ker (Module.Dual.eval ℂ _ y) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hy k
    rw [hspan] at hle
    apply hinj
    rw [map_zero]
    funext b
    exact hle (Submodule.subset_span ⟨b, rfl⟩)
  have hcard : Fintype.card κ = d := by
    apply le_antisymm
    · have := hli.fintype_card_le_finrank
      rwa [Subspace.dual_finrank_eq, Module.finrank_fin_fun] at this
    · let T : (Fin d → ℂ) →ₗ[ℂ] κ → ℂ := LinearMap.pi fun k => v (c k)
      have hT : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro y hy
        exact hkill y fun k => congrFun hy k
      have := LinearMap.finrank_le_finrank_of_injective hT
      rwa [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at this
  set e := Fintype.equivFinOfCardEq hcard
  set a : Fin d → I := fun i => c (e.symm i)
  refine ⟨a₀, a, ⟨z₁, hz₁, ha₀⟩, fun F hF => ?_⟩
  set π : (I → ℂ) →L[ℂ] Fin d → ℂ := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a i)
  have hG : HasStrictFDerivAt (fun z => π (ρ z)) (π.comp D) z₂ :=
    π.hasStrictFDerivAt.comp z₂ ((hρ z₂ hz₂).hasStrictFDerivAt one_ne_zero)
  have hsurj : LinearMap.range ((π.comp D : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) :
      (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = ⊤ := by
    rw [LinearMap.range_eq_top, ← LinearMap.injective_iff_surjective, ← LinearMap.ker_eq_bot,
      Submodule.eq_bot_iff]
    intro y hy
    apply hkill y
    intro k
    have := congrFun hy (e k)
    simpa [π, a, v] using this
  have hN : (fun z => π (ρ z)) '' U ∈ 𝓝 (π (ρ z₂)) := by
    rw [← hG.map_nhds_eq_of_surj hsurj]
    exact Filter.image_mem_map (hUo.mem_nhds hz₂)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hinf : ∀ i, (Metric.ball (π (ρ z₂) i) ε).Infinite := fun i hfin => by
    obtain ⟨x, hx, hxc⟩ := (hfin.countable.dense_compl ℝ).inter_open_nonempty _ Metric.isOpen_ball
      ⟨_, Metric.mem_ball_self hε⟩
    exact hxc hx
  choose S hS hScard using fun i => (hinf i).exists_subset_card_eq (MvPolynomial.degreeOf i F + 1)
  refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset F S (fun i => by rw [hScard i]; omega) fun x hx => ?_
  have hxb : x ∈ Metric.ball (π (ρ z₂)) ε := by
    rw [ball_pi _ hε]
    exact fun i _ => hS i (hx i)
  obtain ⟨z, hzU, rfl⟩ := hball hxb
  exact hF z hzU.1 hzU.2

end GlobalTheory.CountableFibres
