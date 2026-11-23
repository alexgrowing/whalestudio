import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

private theorem level_term (h1 : ThetaFixedGlobalWeights) (h3 : LevTop) (h6 : ToYd) (h7 : LevelTr)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub E n)
    (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (lamE : (E →+* ℂ) → DomWeight n)
    (hlam : ∀ φ, π.HasInfChar φ (infOfWeight (lamE φ))) {S : Set (Pl E)} (hS : IsSection S)
    {Z : Finset (Pl E)} (hZ : SplitIn S Z) {B : Pl E → Multiset ℂˣ} {τ : ∀ w : Pl E, SmIrr (GLw n w)}
    (hB : ∀ w, Off Z w → (CG.mk π).HasSat w (B w)) (hτ : ∀ w ∈ Z, π.IsLocComp w (τ w))
    {u : GL (Fin n) E} (hu : IsTransl u) (μC : Measure (G n)) (μ : Measure (H E n 0))
    [μC.IsHaarMeasure] [μ.IsHaarMeasure] {N : ∀ w : Pl E, Subgroup (GLw n w)} (hN : Good Z N)
    (hfix : ∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) :
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
        (k : ∀ v : InfinitePlace E, Mat n → ((lefE n (lamE v.embedding).w).V →L[ℂ] (lefE n (lamE v.embedding).w).V))
        (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
        TEv S T e₂ → (∀ v : InfinitePlace E, IsMult μC (lefE n (lamE v.embedding).w) (k v) (vl v) R) →
        IsTwTr μ π (phiProd (fun v => (lamE v.embedding).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
          (c * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
            (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
  obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
  obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Lev S N : Set (GF E n)), hKc⟩, by
      show (interior (Lev S N : Set (GF E n))).Nonempty
      rw [hKo.interior_eq]
      exact ⟨1, (Lev S N).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
    h1 E n hn π hreg hd lamE hlam (Lev S N) hKo hKc hKθ hfix μC μf μ
  obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
  obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
  refine ⟨href, cK * v * d, mul_ne_zero (mul_ne_zero hcK hv) hd0, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
  obtain ⟨hHF, hTrY⟩ := hyv _ hH
  have key := htr k vl (fun _ => R) hM _ hHF
  rw [hTrY, hTr] at key
  have e : cK * (∏ w : InfinitePlace E, vl w (infOf (lamE w.embedding).w)) *
      (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
      cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) *
        (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
  rw [e] at key
  exact key

theorem piTerm_of_weights_levels :
    ThetaFixedGlobalWeights → WtEx → LevTop → LevFix → LcLevel → ToYd → LevelTr → TwUniq → PiTerm := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 E _ _ _ _ n hn π hreg hd
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  refine ⟨fun v => lamE v.embedding, fun v => hlam _, ?_⟩
  intro S hS Z hZ B τ hB hτ u hu μC μ _ _
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₀, hc₀, hlev₀⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN₀
    ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level_term h1 h3 h6 h7 hn π hreg hd lamE hlam hS hZ hB hτ hu μC μ hN
    ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (lamE v.embedding).w)) = 0
  · rw [hP] at main ⊢
    simpa using main

  have hcc : c = c₀ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
