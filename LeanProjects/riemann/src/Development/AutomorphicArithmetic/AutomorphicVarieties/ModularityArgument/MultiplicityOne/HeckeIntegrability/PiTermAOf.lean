import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LiftFactorization
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

namespace UpperTheory.V.Z.Mult.Pi

attribute [local instance] borelG borelF borelA borelH

private theorem lev_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    {N N' : ∀ w : Pl E, Subgroup (GLw n w)} (h : ∀ w, N w ≤ N' w) : Lev S N ≤ Lev S N' := by
  intro g hg
  simp only [Lev, Subgroup.mem_iInf] at hg ⊢
  exact fun i => h _ (hg i)

theorem piTermA_of (h1 : GlobalTwistedTraceBound) (hθ : ThetaFixOf) (h2 : WtEx) (h3 : LevTop) (h4 : LevFix) (h5 : LcLevel) (h6 : ToYdA)
    (h7 : LevelTrA) (h8 : TwUniq) (h9 : LevIdx) (h10 : VolIdx) (hK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
      IsOpen (Kf E n : Set (GF E n)) ∧ IsCompact (Kf E n : Set (GF E n))) : PiTermA := by
  intro E _ _ _ _ n hn l u hu μC μ _ _
  obtain ⟨hFo, hFc⟩ := hK E n
  let K₀ : TopologicalSpace.PositiveCompacts (GF E n) :=
    ⟨⟨(Kf E n : Set (GF E n)), hFc⟩, by
      show (interior (Kf E n : Set (GF E n))).Nonempty
      rw [hFo.interior_eq]
      exact ⟨1, (Kf E n).one_mem⟩⟩
  let μf : Measure (GF E n) := Measure.haarMeasure K₀
  haveI : μf.IsHaarMeasure := inferInstance
  have hμ1 : μf (Kf E n : Set (GF E n)) = 1 := Measure.haarMeasure_self (K₀ := K₀)
  obtain ⟨c₀, hc₀, hG⟩ := h1 E n μC μf μ
  refine ⟨c₀, hc₀, fun π hreg hd hl S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨lamE, hlam⟩ := h2 E n π hreg
  have hch : ∀ w : InfinitePlace E,
      HasInfCharGL π.V w.embedding (Multiset.map (infOf (l w).w true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding) (Multiset.map (infOf (l w).w false) Finset.univ.val) := fun w => ⟨by
    rw [map_infOf_true]
    exact hl w, by
    rw [map_infOf_false, ← GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E n π π hd w.embedding _ _ (hl w) (hlam _)]
    exact hlam _⟩
  have level : ∀ N : ∀ w : Pl E, Subgroup (GLw n w), Good Z N → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ Lev S N, finRep E n k ψ = ψ) →
      (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
        (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
      ∃ c : ℂ, ‖c‖ = c₀ ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
        ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
          (k : ∀ v, Mat n → ((lefE n (l v).w).V →L[ℂ] (lefE n (l v).w).V)) (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
          TEv S T e₂ → (∀ v, IsMult μC (lefE n (l v).w) (k v) (vl v) R) →
          IsTwTr μ π (phiProd (fun v => (l v).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
            (c * (∏ v, vl v (infOf (l v).w)) * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0) := by
    intro N hN hfix
    obtain ⟨hKo, hKc, -, -⟩ := h3 E n S Z N hS hZ hN
    obtain ⟨hKθ, hY⟩ := h6 E n S Z N hS hZ hN π u hu
    obtain ⟨Y, ρ, A, cK, hYπ, hfd, hne, hYfix, hact, hsimple, hsq, htw, hcK, htr⟩ :=
      hG hn π hreg (hθ E n hn π hd) (fun v => (l v).w) (fun v => (l v).anti) hch (Lev S N) hKo hKc hKθ hfix
    obtain ⟨y, v, hv, hyv⟩ := hY μf inferInstance Y ρ A hYπ hfd hne hYfix hact hsimple hsq htw
    obtain ⟨href, d, hd0, hdtr⟩ := h7 E n S Z N hS hZ hN π y B τ hB hτ
    obtain ⟨hle, hidx⟩ := h9 E n S Z N hS hZ hN
    have hvol := h10 (GF E n) μf (Kf E n) (Lev S N) hKo hFc hle
    rw [hμ1, hidx] at hvol
    refine ⟨href, cK * v * d, ?_, ?_⟩
    · rw [norm_mul, norm_mul, hcK, hv, hd0, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg, mul_assoc]
      push_cast at hvol
      rw [hvol]
      simp
    intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
    obtain ⟨hH, hTr⟩ := hdtr φ₁ φ₂ hφ T hT e₁ e₂ hE
    obtain ⟨hHF, hTrY⟩ := hyv _ hH
    have key := htr k vl (fun _ => R) hM _ hHF
    rw [hTrY, hTr] at key
    have e : cK * (∏ w : InfinitePlace E, vl w (infOf (l w).w)) *
        (v * (d * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)) =
        cK * v * d * (∏ v : InfinitePlace E, vl v (infOf (l v).w)) *
          (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0 := by ring
    rw [e] at key
    exact key
  obtain ⟨N₀, hN₀, ψ, hψ, hψ0, hψfix⟩ := h4 E n π S Z hS hZ fun w hw => ⟨B w, hB w hw⟩
  obtain ⟨⟨φr, hr, hrne⟩, c₁, hc₁, hlev₀⟩ := level N₀ hN₀ ⟨ψ, hψ, hψ0, hψfix⟩
  refine ⟨c₁, hc₁, ?_⟩
  intro φ₁ φ₂ hφ T hT e₁ e₂ k vl R hE hM
  obtain ⟨N, hN, hle, hHecke⟩ := h5 E n Z N₀ hN₀ φ₁ φ₂ hφ
  obtain ⟨-, c, -, hlev⟩ := level N hN ⟨ψ, hψ, hψ0, fun g hg => hψfix g (lev_mono S hle hg)⟩
  have main := hlev φ₁ φ₂ hHecke T hT e₁ e₂ k vl R hE hM
  by_cases hP : (∏ v : InfinitePlace E, vl v (infOf (l v).w)) = 0
  · rw [hP] at main ⊢
    simpa using main
  have hcc : c = c₁ := by
    let e : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)) := fun _ => Ex.one
    have hEe : TEv S (∅ : Finset (Pl E)) e := ⟨by simp, by simp⟩
    have a₀ := hlev₀ φr φr (fun w hw b => hr w hw (N₀ w) le_rfl b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have a₁ := hlev φr φr (fun w hw b => hr w hw (N w) (hle w) b) ∅ (Finset.disjoint_empty_left Z) e e k vl R hEe hM
    have heq := h8 E n μ π _ _ _ a₁ a₀
    simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, Finset.prod_empty, mul_one] at heq
    exact mul_right_cancel₀ hP (mul_right_cancel₀ hrne heq)
  rw [hcc] at main
  exact main

theorem kf_top (h0 : SlotBasic) (h3 : LevTop) (hP : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.Places) (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsOpen (Kf E n : Set (GF E n)) ∧ IsCompact (Kf E n : Set (GF E n)) := by
  obtain ⟨S, hS⟩ := (hP E).1
  have hG : Good (∅ : Finset (Pl E)) (fun w => KGL w n) := fun w =>
    ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl,
      fun k hk x hx => mul_mem (mul_mem hk hx) (inv_mem hk), fun _ => rfl⟩
  obtain ⟨ho, hc, -, -⟩ := h3 E n S ∅ _ hS (fun _ h => absurd h (Finset.notMem_empty _)) hG
  have e : Lev S (fun w => KGL w n) = Kf E n := Subgroup.ext (h0 E n S hS).2.2.2.2.2.2
  rw [e] at ho hc
  exact ⟨ho, hc⟩

end UpperTheory.V.Z.Mult.Pi

end
