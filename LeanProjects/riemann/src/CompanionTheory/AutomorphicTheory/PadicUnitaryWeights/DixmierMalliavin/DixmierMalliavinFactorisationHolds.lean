import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.DixmierMalliavin.DecompDirection
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlueSmoothOfCompactSupportStatement

namespace CompanionTheory.DM

open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra GlobalTheory.Orb
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Filter

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem exists_lie (H : Subgroup 𝔸ˣ) (hH : IsClosed (H : Set 𝔸ˣ)) : ∃ 𝔤 : Submodule ℝ 𝔸, IsExpLieAlgebra H 𝔤 := by
  let M : Submonoid 𝔸 := (H.toSubmonoid.map (Units.coeHom 𝔸)).topologicalClosure
  have hc : IsClosed (M : Set 𝔸) := isClosed_closure
  have hsub : ∀ u ∈ H, (u : 𝔸) ∈ (M : Set 𝔸) := fun u hu => subset_closure ⟨u, hu, rfl⟩
  have hcl : ∀ u : 𝔸ˣ, (u : 𝔸) ∈ (M : Set 𝔸) → u ∈ H := fun u hu => by
    have : u ∈ closure (H : Set 𝔸ˣ) := by
      rw [Units.isOpenEmbedding_val.isInducing.closure_eq_preimage_closure_image]
      exact hu
    rwa [hH.closure_eq] at this
  have hm : ∀ a ∈ (M : Set 𝔸), ∀ b ∈ (M : Set 𝔸), a * b ∈ (M : Set 𝔸) := fun a ha b hb => M.mul_mem ha hb
  have hi : ∀ Z : 𝔸, exp Z ∈ (M : Set 𝔸) → exp (-Z) ∈ (M : Set 𝔸) := fun Z hZ =>
    hsub _ (H.inv_mem (hcl (expUnit ℝ 𝔸 Z) hZ))
  refine ⟨GlobalTheory.ClosedMatGroup.lieSub M hc M.one_mem hm, fun X hX => hcl _ (by simpa using hX 1), ?_⟩
  have hs := (expPartialHomeomorph ℝ 𝔸).open_source.mem_nhds (zero_mem_expPartialHomeomorph_source ℝ 𝔸)
  have h1 := GlobalTheory.ClosedMatGroup.eventually_exists_exp hc M.one_mem hm hi hs
  have h2 : Tendsto (exp : 𝔸 → 𝔸) (𝓝 0) (𝓝 1) := by
    simpa using (contDiff_exp ℝ 𝔸 (n := 0)).continuous.tendsto 0
  obtain ⟨U, hU, hUo, h0⟩ := mem_nhds_iff.1 ((h2.eventually h1).and hs)
  refine ⟨U, hUo, h0, fun X hX => (hU hX).2, fun X hX hG => ?_⟩
  obtain ⟨Y, hY, hY', e⟩ := (hU hX).1 (hsub _ hG)
  obtain rfl : Y = X := (expPartialHomeomorph ℝ 𝔸).injOn hY (hU hX).2 e
  exact hY'

theorem mem_ccSmooth_iff {H : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra H 𝔤) (f : H → ℂ) :
    f ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) ↔
      (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) ∧ HasCompactSupport f := by
  letI := h.chartedSpace
  constructor
  · rintro ⟨hc, Φ, hΦ, e⟩
    refine ⟨?_, hc⟩
    rw [show f = Φ ∘ fun x : H => ((x : 𝔸ˣ) : 𝔸) from funext e]
    exact hΦ.contMDiff.comp (h.contMDiff_val ∞)
  · rintro ⟨hf, hc⟩
    refine ⟨hc, GlobalTheory.T.exists_contDiff_comp_of_locally_smooth_compactSupport H 𝔸 _ f (continuous_val_val H) hc fun a => ?_⟩
    have h1 : ContDiff ℝ ∞ fun Y : 𝔤 => f (a * h.expG Y) := by
      have := (h.contDiff_comp_expG_smul_mul_mul_expG hf 0 a).comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))
      simpa [Function.comp_def, h.expG_zero] using this
    let L : 𝔸 → 𝔸 := fun y => ((a⁻¹ : H) : 𝔸ˣ) * y
    have hL : ContDiff ℝ ∞ L := contDiff_const.mul contDiff_id
    refine ⟨L ⁻¹' h.nhdOne, h.isOpen_nhdOne.preimage hL.continuous, ?_,
      fun y => f (a * h.expG (subspaceProj 𝔤 ((expPartialHomeomorph ℝ 𝔸).symm (L y)))), ?_, fun g hg => ?_⟩
    · simpa [L] using h.one_mem_nhdOne
    · exact (h1.comp (subspaceProj 𝔤).contDiff).comp_contDiffOn
        ((contDiffOn_expPartialHomeomorph_symm ℝ 𝔸).comp hL.contDiffOn fun y hy => h.nhdOne_subset_target hy)
    · exact congrArg f (h.chart_symm_chart (g := a) (x := g) hg).symm

theorem factor_abs {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ι : G →* 𝔸) (hι : Topology.IsClosedEmbedding (ι.toHomUnits : G → 𝔸ˣ)) (μ : Measure G) [μ.IsHaarMeasure]
    {V : Set G} (hV : V ∈ 𝓝 1) {f : G → ℂ} (hf : f ∈ CcSmooth fun g => ι g) :
    ∃ (N : ℕ) (g k : Fin N → G → ℂ),
      (∀ i, g i ∈ CcSmooth (fun g => ι g) ∧ k i ∈ CcSmooth (fun g => ι g) ∧ tsupport (g i) ⊆ V ∧
        tsupport (k i) ⊆ tsupport f) ∧ f = ∑ i, GlobalTheory.AutomorphicL2Unitary.conv μ (g i) (k i) := by
  let H := ι.toHomUnits.range
  obtain ⟨𝔤, h⟩ := exists_lie H hι.isClosed_range
  let e : G ≃* H := MonoidHom.ofInjective hι.injective
  have he : ∀ g, (((e g : H) : 𝔸ˣ) : 𝔸) = ι g := fun g => rfl
  have c1 : Continuous e := hι.continuous.subtype_mk _
  have c2 : Continuous e.symm := hι.isEmbedding.continuous_iff.2 (continuous_subtype_val.congr fun x =>
    (congrArg Subtype.val (e.apply_symm_apply x)).symm)
  let E : G ≃ₜ H := ⟨e.toEquiv, c1, c2⟩
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  haveI := e.isHaarMeasure_map μ c1 c2
  have hf' : f ∘ E.symm ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) := by
    obtain ⟨hc, Φ, hΦ, e'⟩ := hf
    refine ⟨hc.comp_homeomorph E.symm, Φ, hΦ, fun x => ?_⟩
    rw [Function.comp_apply, e']
    exact congrArg (fun y : H => Φ ((y : 𝔸ˣ) : 𝔸)) (e.apply_symm_apply x)
  have back : ∀ φ : H → ℂ, φ ∈ CcSmooth (fun x : H => ((x : 𝔸ˣ) : 𝔸)) → φ ∘ E ∈ CcSmooth fun g => ι g :=
    fun φ ⟨hc, Φ, hΦ, e'⟩ => ⟨hc.comp_homeomorph E, Φ, hΦ, fun g => e' _⟩
  obtain ⟨hs, hc⟩ := (mem_ccSmooth_iff h _).1 hf'
  obtain ⟨N, φ, ψ, hp, hsum⟩ := factor h (μ.map e) (V := E.symm ⁻¹' V)
    (E.symm.continuous.continuousAt.preimage_mem_nhds (by rwa [show E.symm 1 = 1 from map_one e.symm])) _ hs hc
  refine ⟨N, fun i => φ i ∘ E, fun i => ψ i ∘ E, fun i => ⟨back _ ((mem_ccSmooth_iff h _).2 ⟨(hp i).1, (hp i).2.1⟩),
    back _ ((mem_ccSmooth_iff h _).2 ⟨(hp i).2.2.1, hc.of_isClosed_subset (isClosed_tsupport _) (hp i).2.2.2.2⟩),
    fun x hx => ?_, fun x hx => ?_⟩, funext fun x => ?_⟩
  · simpa using (hp i).2.2.2.1 (tsupport_comp_subset_preimage _ E.continuous hx)
  · simpa using tsupport_comp_subset_preimage _ E.symm.continuous
      ((hp i).2.2.2.2 (tsupport_comp_subset_preimage _ E.continuous hx))
  · have := congrFun hsum (E x)
    rw [Function.comp_apply, E.symm_apply_apply, Finset.sum_apply] at this
    rw [this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (E.measurableEmbedding.integral_map _).trans (integral_congr_ae (.of_forall fun y => ?_))
    show φ i (e y) * ψ i ((e y)⁻¹ * e x) = φ i (e y) * ψ i (e (y⁻¹ * x))
    rw [map_mul, map_inv]

end CompanionTheory.DM

open GlobalTheory.Orb in
theorem CompanionTheory.DM.dixmierMalliavinFactorisation_holds : GlobalTheory.Published.DixmierMalliavinFactorisation := by
  intro G _ _ _ _ _ n _ _ ι hι μ _ V hV f hf
  letI := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := n) (α := ℂ)
  haveI : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℝ _
  let T : (n → n → ℂ) ≃L[ℝ] Matrix n n ℂ := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have e : CcMat ι = CcSmooth fun g => ι g :=
    le_antisymm (ccSmooth_le (p := T.symm) T.symm.contDiff fun _ => rfl) (ccSmooth_le (p := T) T.contDiff fun _ => rfl)
  rw [e] at hf ⊢
  exact CompanionTheory.DM.factor_abs ι hι μ hV hf
