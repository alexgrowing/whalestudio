import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.C1FDetMetricEqChernOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BcUnique

open Filter Topology GlobalTheory.HermFrame

theorem bcFld_isPull : ∀ {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' r s : ℕ} (A : HolAtlas M n) (A' : HolAtlas M' n') (T : HermSeq A r s) (T' : HermSeq A' r s) (f : M' → M), A.IsHolo A' f → T'.IsPull T f → bcFld T' = A.pullback A' f (bcFld T) := by
  intro M M' _ _ n n' r s A A' T T' f hf hT
  obtain ⟨φ, hφh, hφ⟩ := hT
  funext x
  obtain ⟨hb, hc, ha⟩ : x.pt ∈ T'.U (T'.cover x.pt).choose ∧ f x.pt ∈ (A.e (A.cover (f x.pt)).choose).source ∧
      f x.pt ∈ T.U (T.cover (f x.pt)).choose :=
    ⟨(T'.cover x.pt).choose_spec, (A.cover (f x.pt)).choose_spec, (T.cover (f x.pt)).choose_spec⟩
  set b := (T'.cover x.pt).choose with hbd
  set c := (A.cover (f x.pt)).choose with hcd
  set a := (T.cover (f x.pt)).choose with had
  set F : V n' → V n := A.e c ∘ f ∘ x.ch.symm with hFd
  set K : V n → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun w => T.mid a ((A.e c).symm w) with hKd
  set Φ : V n' → Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := fun v => φ a b (x.ch.symm v) with hΦd
  have hx0 : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have hFz : F x.crd = A.e c (f x.pt) := by simp only [hFd, Function.comp_apply, hx0]

  set W := x.ch.target ∩ x.ch.symm ⁻¹' (T'.U b ∩ f ⁻¹' (T.U a ∩ (A.e c).source)) with hWd
  have hWo : IsOpen W := x.ch.continuousOn_symm.isOpen_inter_preimage x.ch.open_target
    ((T'.isOpen b).inter (hf.1.isOpen_preimage _ ((T.isOpen a).inter (A.e c).open_source)))
  have hzW : x.crd ∈ W := ⟨x.ch.map_source x.2, by simp only [mem_preimage, hx0]; exact ⟨hb, ha, hc⟩⟩
  have hWn : W ∈ 𝓝 x.crd := hWo.mem_nhds hzW

  set Wc := (A.e c).target ∩ (A.e c).symm ⁻¹' T.U a with hWcd
  have hWco : IsOpen Wc := (A.e c).continuousOn_symm.isOpen_inter_preimage (A.e c).open_target (T.isOpen a)
  have hFWc : F x.crd ∈ Wc := by
    rw [hFz]; exact ⟨(A.e c).map_source hc, by simp only [mem_preimage, (A.e c).left_inv hc]; exact ha⟩
  have hWcn : Wc ∈ 𝓝 (F x.crd) := hWco.mem_nhds hFWc

  have hK1 : MContDiffAt 1 K (F x.crd) := fun i j =>
    ((((T.smooth a).2.1 i j c).contDiffAt hWcn).of_le (by norm_cast))
  have hKp : ∀ᶠ w in 𝓝 (F x.crd), (K w).PosDef :=
    Filter.eventually_of_mem hWcn fun w hw => (T.posDef a _ hw.2).2.1
  have hF : ContDiffAt ℂ 1 F x.crd :=
    GlobalTheory.SCV.contDiffAt_of_differentiableOn ((hf.2 x.1.1 c).mono fun v hv => ⟨hv.1, hv.2.2.2⟩) hWn 1
  have hΦh : ∀ i j, DifferentiableOn ℂ (fun v => Φ v i j) W := fun i j =>
    (hφh a b i j x.1.1).mono fun v hv => ⟨hv.1, hv.2.2.1, hv.2.1⟩
  have hΦ1 : MContDiffAt 1 Φ x.crd := fun i j =>
    (GlobalTheory.SCV.contDiffAt_of_differentiableOn (hΦh i j) hWn 1).restrict_scalars ℝ
  have hΦ0 : ∀ η, mdbar Φ x.crd η = 0 := fun η => Matrix.ext fun i j =>
    congr($(GlobalTheory.dbar_eq_zero ((hΦh i j).differentiableAt hWn)) η)
  have hΦt : ∀ᶠ v in 𝓝 x.crd, (Φ v).toBlocks₂₁ = 0 :=
    Filter.eventually_of_mem hWn fun v hv => (hφ a b _ hv.2.2.1 hv.2.1).1
  have hmid : ∀ᶠ v in 𝓝 x.crd, T'.mid b (x.ch.symm v) = chg (Φ v) (K (F v)) :=
    Filter.eventually_of_mem hWn fun v hv => by
      rw [(hφ a b _ hv.2.2.1 hv.2.1).2.2.2.2.1]
      simp only [hKd, hFd, hΦd, Function.comp_apply, (A.e c).left_inv hv.2.2.2]
  have hu : IsUnit (Φ x.crd).det := by
    have h1 := (T'.posDef b _ hb).2.1
    rw [← hx0, hmid.self_of_nhds] at h1
    have h2 := h1.det_pos.ne'
    rw [det_chg] at h2
    refine Ne.isUnit fun h0 => h2 ?_
    simp [h0]
  have hKF1 : MContDiffAt 1 (fun v => K (F v)) x.crd := fun i j => (hK1 i j).comp x.crd (hF.restrict_scalars ℝ)
  have hKFp : ∀ᶠ v in 𝓝 x.crd, (K (F v)).PosDef := hF.continuousAt.eventually hKp
  have key : extTrace (fun v => T'.mid b (x.ch.symm v)) x.crd = fun ξ η =>
      extTrace K (F x.crd) (fderiv ℂ F x.crd ξ) (fderiv ℂ F x.crd η) := by
    rw [extTrace_congr hmid, extTrace_chg hKF1 hKFp hΦ1 hu hΦ0 hΦt]
    funext ξ η
    exact extTrace_comp_holo hK1 hKp hF ξ η
  show (ofValues (extTrace (fun v => T'.mid b (x.ch.symm v)) x.crd) : Alt n') =
    pull (fderiv ℂ F x.crd) (ofValues (extTrace K (A.e c (f x.pt))) : Alt n)
  rw [key, ← hFz, GlobalTheory.FibTheta.pull_ofValues _ (GlobalTheory.LineForm.OmReal.isSesq_extTrace hK1 hKp)]

end GlobalTheory.BcUnique
