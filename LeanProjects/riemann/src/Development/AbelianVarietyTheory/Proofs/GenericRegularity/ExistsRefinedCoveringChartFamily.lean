import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AdjoinRatiosOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReducedStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SpanEvalEqTopOfNoCommonZeroReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Reg

theorem adjoin_insert_union_image {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [DecidableEq Ω] (x : Ω)
    (G : Finset Ω) {m : ℕ} (r : Fin m → Ω) :
    Algebra.adjoin K (insert x ((G ∪ Finset.univ.image r : Finset Ω) : Set Ω)) =
      Algebra.adjoin K ((Algebra.adjoin K (insert x (G : Set Ω)) : Set Ω) ∪ Set.range r) := by
  apply le_antisymm
  · apply Algebra.adjoin_mono
    intro z hz
    rcases hz with rfl | hz
    · exact Or.inl (Algebra.subset_adjoin (Or.inl rfl))
    · rcases Finset.mem_union.1 hz with h | h
      · exact Or.inl (Algebra.subset_adjoin (Or.inr h))
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨i, rfl⟩
  · apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · refine Algebra.adjoin_mono ?_ hz
      apply Set.insert_subset_insert
      intro g hg
      exact Finset.mem_coe.2 (Finset.mem_union_left _ hg)
    · exact Algebra.subset_adjoin (Or.inr (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

set_option maxHeartbeats 800000 in

theorem PChart.exists_refine (hL : EvLaws Xo c) {O : Type} [CommRing O] {β : O →+* c.F} (P : PChart Xo c β)
    {m : ℕ} (ws : Fin m → Rul Xo c)
    (hw : ∀ e (he : e ∈ P.es) i, ((evR Xo c (ws i) (P.y e he) : P.R e) : P.Ω) = evR Xo c (ws i) P.yg)
    (hspan : ∀ e (he : e ∈ P.es), Ideal.span (Set.range fun i => (evR Xo c (ws i) (P.y e he) : P.R e)) = ⊤)
    (k : Fin m) (hk : evR Xo c (ws k) P.yg ≠ 0) :
    ∃ P' : PChart Xo c β, P'.Fam ws ∧
      ∀ (L : Type) [Field L] [Algebra c.F L] (W : ValuationSubring L) (y : FrPt Xo c L)
        (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ),
        (∀ g : P.R e, (g : P.Ω) ∈ P.gens → ψ g ∈ W) → FrMap ψ (P.y e he) z → FrBor t y z →
        ψ (evR Xo c (ws k) (P.y e he)) ≠ 0 →
        (∀ i, ψ (evR Xo c (ws i) (P.y e he)) / ψ (evR Xo c (ws k) (P.y e he)) ∈ W) → P'.Catches W y := by
  classical
  let G : Finset P.Ω := P.gens ∪ Finset.univ.image fun i => evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => Finset.mem_coe.2 (Finset.mem_union_left _ hg)
  have hGr : ∀ i, evR Xo c (ws i) P.yg / evR Xo c (ws k) P.yg ∈ G := fun i =>
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  have hblow := fun e (he : e ∈ P.es) =>
    GlobalTheory.adjoin_ratios_of_span_eq_top c.F P.Ω (P.R e) m (fun i => evR Xo c (ws i) (P.y e he)) k (hspan e he)
      (by rw [hw e he k]; exact hk) (Algebra.adjoin c.F (insert e⁻¹ (G : Set P.Ω)))
      (by simp only [hw e he]; exact adjoin_insert_union_image _ _ _)
  choose hle hinv hsm hext using hblow
  have hy := fun e (he : e ∈ P.es) => hL.bc _ _ (Subalgebra.inclusion (hle e he)) (P.y e he)
  choose y' hy' using hy
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := P.es
            es_ne := P.es_ne
            es_mem := fun e he => ⟨(P.es_mem e he).1, ?_⟩
            sm := fun e he => hsm e he (P.sm e he)
            yg := P.yg
            y := y'
            gen := fun e he => frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) _ (P.y e he) _ _ (hy' e he)
              (P.gen e he)
            int := ?_ }, ⟨k, hk, fun i => ?_, fun e he => ?_⟩, ?_⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · exact Subring.closure_mono (Set.union_subset_union_right _ hG) (P.es_mem e he).2
  · intro e he T io
    letI := io.toAlgebra
    intro ψ h1 h2 z hz
    refine P.int e he T io (ψ.comp (Subalgebra.inclusion (hle e he))) h1 (fun g hg => ?_) z
      (frMap_trans _ _ _ _ _ _ _ _ (hy' e he) hz)
    exact h2 (Subalgebra.inclusion (hle e he) g) (hG hg)
  · exact Subring.subset_closure (Or.inr (hGr i))
  · have := hinv e he
    rw [hw e he k] at this
    exact this
  · intro L _ _ W y e he ψ z t h1 hz hb hψ hW
    obtain ⟨ψ', hc, hr⟩ := hext e he L ψ hψ
    refine ⟨e, he, ψ', z, t, fun g hg => ?_, ?_, hb⟩
    · rcases Finset.mem_union.1 hg with h | h
      · have e1 : g = Subalgebra.inclusion (hle e he) ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ := Subtype.ext rfl
        have e2 := h1 ⟨g, Algebra.subset_adjoin (Or.inr h)⟩ h
        have e3 := DFunLike.congr_fun hc ⟨g, Algebra.subset_adjoin (Or.inr h)⟩
        rw [AlgHom.comp_apply] at e3
        have e4 := (congrArg ψ' e1).trans e3
        exact e4.symm ▸ e2
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        rw [← hw e he i, ← hw e he k] at hi
        have e1 := hr i (hi.symm ▸ g.2)
        have e2 : g = ⟨_, hi.symm ▸ g.2⟩ := Subtype.ext hi.symm
        have e4 := (congrArg ψ' e2).trans e1
        exact e4.symm ▸ hW i
    · refine frMap_cancel _ _ _ (Subalgebra.inclusion (hle e he)) ψ' (P.y e he) _ _ (hy' e he) ?_
      exact hc.symm ▸ hz

theorem exists_covers_fam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (J : Type) [Finite J] (P : J → PChart Xo c β), Covers P → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ (J' : Type) (_ : Finite J') (P' : J' → PChart Xo c β), Covers P' ∧ ∀ j, (P' j).Fam ws := by
  intro E _ _ _ H Dw l Xo c hL O _ β J _ P hP a n m ws hws hnc
  have hw : ∀ j e (he : e ∈ (P j).es) i,
      ((evR Xo c (ws i) ((P j).y e he) : (P j).R e) : (P j).Ω) = evR Xo c (ws i) (P j).yg := fun j e he i =>
    (GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n (ws i) (hws i) _ _ _ _ _ ((P j).gen e he)).symm
  have hspan : ∀ j e (he : e ∈ (P j).es),
      Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) = ⊤ := fun j e he =>
    GlobalTheory.T.span_eval_eq_top_of_noCommonZero_reduced E H Dw l Xo c hL a n m ws hws hnc _ _
  have h := fun p : {p : J × Fin m // evR Xo c (ws p.2) (P p.1).yg ≠ 0} =>
    PChart.exists_refine hL (P p.1.1) ws (hw p.1.1) (hspan p.1.1) p.1.2 p.2
  choose P' hF hC using h
  refine ⟨_, inferInstance, P', ?_, hF⟩
  intro L _ _ W hW y
  obtain ⟨j, e, he, ψ, z, t, h1, hz, hb⟩ := hP L W hW y
  have hex : ∃ i, ψ (evR Xo c (ws i) ((P j).y e he)) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hle : Ideal.span (Set.range fun i => (evR Xo c (ws i) ((P j).y e he) : (P j).R e)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hn i
    rw [hspan j e he] at hle
    have h1 : ψ 1 = 0 := hle (Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  obtain ⟨i₀, hi₀⟩ := hex
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun i => W.valuation (ψ (evR Xo c (ws i) ((P j).y e he)))) ⟨i₀, Finset.mem_univ _⟩
  have hk0 : ψ (evR Xo c (ws k) ((P j).y e he)) ≠ 0 := by
    intro h0
    have := hk i₀ (Finset.mem_univ _)
    simp only [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi₀ this
  have hk1 : evR Xo c (ws k) (P j).yg ≠ 0 := by
    intro h0
    rw [← hw j e he k] at h0
    apply hk0
    have h2 : (evR Xo c (ws k) ((P j).y e he) : (P j).R e) = 0 := Subtype.ext h0
    rw [h2, map_zero]
  refine ⟨⟨(j, k), hk1⟩, hC ⟨(j, k), hk1⟩ L W y e he ψ z t h1 hz hb hk0 fun i => ?_⟩
  rw [← W.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hk i (Finset.mem_univ _)) zero_le'

end GlobalTheory.Reg
