import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortGeneratorMemSpanSmallSupNormShortGeneratorsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_finset_span_top_of_span {O K R : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup R]
    [Module K R] [Module O R] [IsScalarTower O K R] (C : Submodule K R) [FiniteDimensional K C] (s A : Set R)
    (hA : A ⊆ C) (hs : ∀ g ∈ s, g ∈ Submodule.span K A)
    (htop : Submodule.span K
      (((Submodule.span O s).comap (C.subtype.restrictScalars O) : Submodule O C) : Set C) = ⊤) :
    ∃ Sh : Finset C, (∀ g ∈ Sh, (g : R) ∈ A) ∧ Submodule.span K (Sh : Set C) = ⊤ := by
  classical
  set A' : Set C := {x | (x : R) ∈ A} with hA'
  have hsub : ∀ x : C, (x : R) ∈ Submodule.span K A → x ∈ Submodule.span K A' := by
    intro x hx
    have himg : (C.subtype '' A') = A := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hA hy⟩, hy, rfl⟩
    rw [← himg, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have htop' : Submodule.span K A' = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    intro x hx
    apply hsub
    have hx' : (x : R) ∈ Submodule.span O s := hx
    exact (Submodule.span_le.mpr hs) (Submodule.span_le_restrictScalars O K s hx')
  obtain ⟨b, hbA, hbspan, hbli⟩ := exists_linearIndependent K A'
  have hbfin : b.Finite := hbli.setFinite
  refine ⟨hbfin.toFinset, ?_, ?_⟩
  · intro g hg
    exact hbA (hbfin.mem_toFinset.mp hg)
  · rw [hbfin.coe_toFinset, hbspan, htop']

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_short_family_small : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → ∃ Sh : Finset ((recB h.toLawsCore).Cusp j w), (∀ g ∈ Sh, g ∈ (recPJ h j hj).shortTh w ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ g) ≤ 400 * Zb D large₂ * w.size) ∧ Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j w)) = ⊤ := by
  intro hC D T h hG large₂ j hj w hP hL hn hw hS hA hsp
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hw
  have hdom := dom_wtA w
  have hshC : T.sh j w ⊆ T.C j w := hS.shCusp j hj (wtA w) w.n hdom hlp hdom hlp
  have hsmall := GlobalTheory.T.shortGenerator_mem_span_small_supNorm_shortGenerators hC D T h hG large₂ j hj w hP hL hn hw hS hA
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt at hsp
  simp only [recPJ, recB, mkX, mkB] at hsp ⊢
  unfold spanIn cutN cutR at *
  have hmemC : ∀ x, x ∈ T.C j w → x ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) := by
    intro x hx
    simp [hx, hj]
  have : FiniteDimensional T.Q.c.F (T.C j w) := h.toLawsCore.fd j hj w
  have : FiniteDimensional T.Q.c.F (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hs : ∀ g ∈ T.sh j w, g ∈ Submodule.span T.Q.c.F
      {g' | g' ∈ (T.C j w ⊓ ⨅ (_ : ¬InR D j), ⊥ : Submodule T.Q.c.F (T.R j)) ∧ g' ∈ T.sh j w ∧
        ∀ σ, Real.log (T.Ns j w σ g') ≤ 400 * Zb D large₂ * w.size} := by
    intro g hg
    refine Submodule.span_mono ?_ (hsmall g hg)
    rintro x ⟨hx1, hx2⟩
    exact ⟨hmemC x (hshC hx1), hx1, hx2⟩
  obtain ⟨Sh, hShA, hShspan⟩ := exists_finset_span_top_of_span (O := 𝓞 T.Q.c.F) _ _ _
    (fun x hx => hx.1) hs hsp
  refine ⟨Sh, fun g hg => ?_, hShspan⟩
  obtain ⟨_, hgs, hgb⟩ := hShA g hg
  refine ⟨Submodule.subset_span hgs, fun σ => ?_⟩
  rw [if_pos hj]
  exact hgb σ

end GlobalTheory.RunIn
