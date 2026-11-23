import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
import Development.AutomorphicArithmetic.DivisorFrames.ExistsLinearlyDisjointSpan
import Development.AutomorphicArithmetic.DivisorFrames.CuspFormWeightReduction
import Development.AutomorphicArithmetic.DivisorFrames.HolomorphicReductionSpan
import Development.AutomorphicArithmetic.DivisorFrames.VanishingSectionsToroidalFlagIndependent
import Development.AutomorphicArithmetic.DivisorFrames.UnfoldingComponentLinearIndependence

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open Filter Topology

namespace GlobalTheory.CuspSpan

theorem mem_cuspOn_of_comb (hP : Hypotheses2) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hG : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) {m : ℕ} {ε : Fin m → ℂ}
    (hε : ∀ a : Fin m → Y.d.c₂.F, ∑ i, σ (a i) * ε i = 0 → a = 0) {g : Fin m → Rul Y.d.Xo₂ Y.d.c₂}
    (hg : ∀ i, g i ∈ secZ Y.d.Xo₂ Y.d.c₂ (exOf (T.Q.Dw j) la 0)) (hZ : ∀ i, g i ∈ suppOn Z)
    (hs : (∑ i, ε i • rdU (Y.U σ) (g i)) ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0))) (i : Fin m) :
    g i ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) := by
  have h1 := (GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG).pos
  obtain ⟨M, hsm, hb, hk⟩ := hP.p1 _ _ _ h1 _ Y.d.Xo₂ Y.d.c₂
  obtain ⟨TF⟩ := GlobalTheory.CompHS.TorFlagEx.torFlag_of_model M hsm hb hk
    (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta M (GlobalTheory.ThetaNormal.hasTheta_of_smooth _ _ _ h1 _ _ _ M hsm))
  have ha := UpperTheory.holomorphic_reduction_span D T j Y e o hG Z TF la σ hσ m ε (fun i => ⟨g i, hg i⟩) hs
  obtain ⟨t, ht, hti⟩ := UpperTheory.vanishing_sections_toroidal_flag_independent _ _ _ _ _ _ TF Z la σ (GlobalTheory.T.flagSpace_component_smooth_projective_connected _ _ _ _ _ _ TF Z hG.geo) m ε hε _ ha i
  obtain ⟨f, hfs⟩ := GlobalTheory.HSApp.vanBd_le_space D T j Y e o hG hf Z TF la ht
  let g' : secZ Y.d.Xo₂ Y.d.c₂ (exOf (T.Q.Dw j) la 0) := ⟨g i, hg i⟩
  let f' : secZ Y.d.Xo₂ Y.d.c₂ (exOf (T.Q.Dw j) la 0) := ⟨f.1, GlobalTheory.CompHS.cusp_le_secZ Z Y.U la f.2⟩
  have h3 : GlobalTheory.CompHS.sec₀ TF.X Z _ f' = GlobalTheory.CompHS.sec₀ TF.X Z _ g' := hfs.trans hti
  have h4 : (g' - f').1 ∈ suppOn Z := sub_mem (hZ i) f.2.2
  have h0 : g' - f' = 0 := GlobalTheory.CompHS.eq_zero_of_sec₀ TF.X Z h4
    (((GlobalTheory.CompHS.sec₀ TF.X Z _).map_sub g' f').trans (sub_eq_zero.2 h3.symm))
  have h2 : g i = f.1 := congrArg Subtype.val (sub_eq_zero.1 h0)
  rw [h2]
  exact f.2

theorem exists_mem_span (hP : Hypotheses2) {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ}
    (hG : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)) {w : Rul Y.d.Xo₂ Y.d.c₂} (hw : w ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0))
    (hw0 : w ≠ 0) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) :
    ∀ P ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0)),
      ∃ Q ∈ Submodule.span ℂ (rdU (Y.U σ) '' (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0) : Set (Rul Y.d.Xo₂ Y.d.c₂))),
        ∀ z ∈ framesOn (Y.U σ) Z, P z.1 z.2 = Q z.1 z.2 := by
  intro P hPm
  have hL := GlobalTheory.FlatAnyLevel.neatUnf_of_good D T j Y e o hG
  obtain ⟨k, hk⟩ := GlobalTheory.FlatAnyLevel.framesOn_model _ _ _ _ _ _ _ Y.U hL Z σ hσ
  let P₀ : FDSec (Y.U σ).X := Pi.single k (((Y.U σ).X k).dom.indicator (P k))
  have hP₀ : P₀ ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0)) := by
    refine holCusp_mem_holSub _ _ fun k' => ?_
    by_cases h : k' = k
    · subst h
      simp only [P₀, Pi.single_eq_same]
      exact (GlobalTheory.DomCongr.bddSec_cusp_congr _ _ _ _ _ _ (fun x hx => (Set.indicator_of_mem hx _).symm)).2
        ((GlobalTheory.DegTop.mem_holSub_iff _ _ _).1 hPm k')
    · simp only [P₀, Pi.single_eq_of_ne h]
      exact GlobalTheory.FlatCore.MulSpan.zero_mem_SS' _ _
  have hoff : ∀ k' y, (⟨k', y⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∉ framesOn (Y.U σ) Z → P₀ k' y = 0 := by
    intro k' y hy
    by_cases h : k' = k
    · subst h
      simp only [P₀, Pi.single_eq_same]
      exact Set.indicator_of_notMem (fun hd => hy (by rw [hk]; exact ⟨rfl, hd⟩)) _
    · simp only [P₀, Pi.single_eq_of_ne h, Pi.zero_apply]
  have hon : ∀ z ∈ framesOn (Y.U σ) Z, P z.1 z.2 = P₀ z.1 z.2 := by
    rintro ⟨k', y⟩ hz
    rw [hk] at hz
    obtain ⟨rfl, hy⟩ : k' = k ∧ y ∈ ((Y.U σ).X k').dom := hz
    simp only [P₀, Pi.single_eq_same]
    exact (Set.indicator_of_mem hy _).symm
  refine ⟨P₀, ?_, hon⟩
  obtain ⟨G₀, h, hh, hh0, hmul⟩ := UpperTheory.cusp_form_weight_reduction _ _ _ _ _ _ _ Y.U hL Z la w hw hw0
  obtain ⟨m, ε, g, hε, hg, hsum⟩ := UpperTheory.exists_linearly_disjoint_span _ _ _ σ (rdU (Y.U σ)) _ _ (hmul σ hσ P₀ hP₀ hoff)
  have hcP : ∀ k', ContinuousOn (P₀ k') ((Y.U σ).X k').dom := fun k' =>
    (GlobalTheory.FlatCore.differentiableOn_of_mem_holSub hP₀ k').continuousOn
  have hsum' : ∀ k' y, ∑ i, ε i * rdU (Y.U σ) (g i) k' y = P₀ k' y * rdU (Y.U σ) h k' y := fun k' y => by
    have := congrFun (congrFun hsum k') y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at this
    exact this.symm
  choose s hs hsZ hsh using UpperTheory.unfolding_component_linear_independence _ _ _ _ _ _ _ σ (Y.U σ) hσ (hL.unf σ hσ) Z m ε hε _ _ h g
    (cuspW_le_secZ _ hh.1) hh.2 hh0 (fun i => cuspW_le_secZ _ (hg i).1) (fun i => (hg i).2) P₀ hcP
    (fun z _ => hsum' z.1 z.2)
  have hex : exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) la 0 + G₀) - exZ (T.Q.Dw j) G₀ = exOf (T.Q.Dw j) la 0 := by
    funext i; rw [Pi.sub_apply, exZ_add, exOf, add_sub_cancel_right]
  rw [hex] at hs
  have hex0 : exOf (T.Q.Dw j) la 0 none = 0 := rfl
  have hne : ∃ y ∈ ((Y.U σ).X k).dom, rdU (Y.U σ) h k y ≠ 0 := by
    obtain ⟨⟨k₀, y₀⟩, hz₀, hne⟩ := GlobalTheory.FlatAnyLevel.exists_frame_ne hL hσ hh hh0
    rw [hk] at hz₀
    obtain ⟨h1, hy₀⟩ := hz₀
    subst h1
    exact ⟨y₀, hy₀, hne⟩
  have hint := interior_closure_zero ((Y.U σ).X k)
    (GlobalTheory.FlatCore.differentiableOn_of_mem_holSub ((mem_cuspW.1 hh.1).2 σ hσ) k) hne
  have hcont : ContinuousOn (fun y => ∑ i, ε i * rdU (Y.U σ) (s i) k y - P₀ k y) ((Y.U σ).X k).dom :=
    (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul
      (GlobalTheory.FlatAnyLevel.contOn_rdU _ _ _ _ _ _ _ Y.U hL _ hex0 _ (hs i) σ hσ k)).sub (hcP k)
  have hO := FourierCoefficientDomain.isOpen_dom ((Y.U σ).X k)
  have key : ∀ y ∈ ((Y.U σ).X k).dom, ∑ i, ε i * rdU (Y.U σ) (s i) k y = P₀ k y := by
    intro y hy
    by_contra hn
    have hev : ∀ᶠ v in 𝓝 y, ∑ i, ε i * rdU (Y.U σ) (s i) k v - P₀ k v ≠ 0 ∧ v ∈ ((Y.U σ).X k).dom :=
      ((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hn)).and (hO.mem_nhds hy)
    have hsub : {v | ∑ i, ε i * rdU (Y.U σ) (s i) k v - P₀ k v ≠ 0 ∧ v ∈ ((Y.U σ).X k).dom} ⊆
        closure {v | v ∈ ((Y.U σ).X k).dom ∧ rdU (Y.U σ) h k v = 0} := by
      rintro v ⟨hv, hvd⟩
      refine subset_closure ⟨hvd, ?_⟩
      have h2 : (∑ i, ε i * rdU (Y.U σ) (s i) k v - P₀ k v) * rdU (Y.U σ) h k v = 0 := by
        rw [sub_mul, sub_eq_zero, ← hsum', Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hsh i, GlobalTheory.AllWt.rdU_mul (Y.U σ), Pi.mul_apply, Pi.mul_apply, mul_assoc]
      exact (mul_eq_zero.1 h2).resolve_left hv
    have hy' := interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)
    rw [hint] at hy'
    exact hy'
  have hall : ∑ i, ε i • rdU (Y.U σ) (s i) = P₀ := by
    funext k' y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hz : (⟨k', y⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ : k' = k ∧ y ∈ ((Y.U σ).X k').dom := hz
      exact key y hy
    · rw [hoff k' y hz]
      exact Finset.sum_eq_zero fun i _ => by rw [rdU_eq_zero (Y.U σ) (hsZ i) hz, mul_zero]
  have hc := mem_cuspOn_of_comb hP hG hf Z la hσ hε hs hsZ (hall.symm ▸ hP₀)
  rw [← hall]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s i, hc i, rfl⟩)

end GlobalTheory.CuspSpan
