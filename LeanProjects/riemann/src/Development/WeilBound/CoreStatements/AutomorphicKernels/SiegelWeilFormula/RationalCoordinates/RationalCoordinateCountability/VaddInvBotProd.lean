import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousCA

noncomputable section

open scoped ENNReal Pointwise
open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

theorem fd_bot_univ {X : Type} [AddGroup X] [MeasurableSpace X] (μ : Measure X) :
    IsAddFundamentalDomain (⊥ : AddSubgroup X) Set.univ μ := by
  refine ⟨nullMeasurableSet_univ, Filter.Eventually.of_forall fun x => ⟨0, Set.mem_univ _⟩, ?_⟩
  intro g h hgh
  exact absurd (Subtype.ext ((AddSubgroup.mem_bot.1 g.2).trans (AddSubgroup.mem_bot.1 h.2).symm)) hgh

theorem fd_prod' {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    {Γ : AddSubgroup X} {Δ : AddSubgroup Y}
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] {s : Set X} {t : Set Y}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨⟨g, hg⟩, hgs⟩ := hp1
    obtain ⟨⟨d, hd⟩, hdt⟩ := hp2
    exact ⟨⟨(g, d), AddSubgroup.mem_prod.2 ⟨hg, hd⟩⟩, hgs, hdt⟩
  · intro g h hgh
    have key : (g : X × Y).1 ≠ (h : X × Y).1 ∨ (g : X × Y).2 ≠ (h : X × Y).2 := by
      by_contra hc
      push_neg at hc
      exact hgh (Subtype.ext (Prod.ext hc.1 hc.2))
    rcases key with h1 | h2
    · have hg : (g : X × Y).1 ∈ Γ := (AddSubgroup.mem_prod.1 g.2).1
      have hh : (h : X × Y).1 ∈ Γ := (AddSubgroup.mem_prod.1 h.2).1
      have hd : AEDisjoint μ ((⟨_, hg⟩ : Γ) +ᵥ s) ((⟨_, hh⟩ : Γ) +ᵥ s) :=
        hs.aedisjoint (fun e => h1 (congrArg Subtype.val e))
      refine (hd.preimage Measure.quasiMeasurePreserving_fst).mono ?_ ?_
      · rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
      · rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
    · have hg : (g : X × Y).2 ∈ Δ := (AddSubgroup.mem_prod.1 g.2).2
      have hh : (h : X × Y).2 ∈ Δ := (AddSubgroup.mem_prod.1 h.2).2
      have hd : AEDisjoint ν ((⟨_, hg⟩ : Δ) +ᵥ t) ((⟨_, hh⟩ : Δ) +ᵥ t) :=
        ht.aedisjoint (fun e => h2 (congrArg Subtype.val e))
      refine (hd.preimage Measure.quasiMeasurePreserving_snd).mono ?_ ?_
      · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy
      · rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
        exact Set.vadd_mem_vadd_set hy

theorem vaddInv_bot_prod {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableAdd Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (Δ : AddSubgroup Y)
    (hν : ∀ y ∈ Δ, MeasurePreserving (fun z => y + z) ν ν) :
    VAddInvariantMeasure ((⊥ : AddSubgroup X).prod Δ) (X × Y) (μ.prod ν) := by
  refine ⟨fun c u hu => ?_⟩
  obtain ⟨⟨a, d⟩, hc⟩ := c
  have ha : a = 0 := AddSubgroup.mem_bot.1 (AddSubgroup.mem_prod.1 hc).1
  have hd : d ∈ Δ := (AddSubgroup.mem_prod.1 hc).2
  subst ha
  have hmp : MeasurePreserving (Prod.map id (fun z => d + z)) (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).prod (hν d hd)
  have hfun : (fun x : X × Y => (⟨(0, d), hc⟩ : ((⊥ : AddSubgroup X).prod Δ)) +ᵥ x) =
      Prod.map id (fun z => d + z) := by
    funext x
    refine Prod.ext ?_ rfl
    show (0 : X) + x.1 = x.1
    exact zero_add _
  rw [hfun]
  exact hmp.measure_preimage hu.nullMeasurableSet

theorem mp_of_vaddInv {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] [MeasurableAdd Y] (ν : Measure Y) (Δ : AddSubgroup Y)
    [VAddInvariantMeasure Δ Y ν] (y : Y) (hy : y ∈ Δ) : MeasurePreserving (fun z => y + z) ν ν := by
  refine ⟨measurable_const_add y, ?_⟩
  ext u hu
  rw [Measure.map_apply (measurable_const_add y) hu]
  exact VAddInvariantMeasure.measure_preimage_vadd (⟨y, hy⟩ : Δ) hu

end PositivityTheory.SiegelWeilFormula.Act.C5.CoordK

end
