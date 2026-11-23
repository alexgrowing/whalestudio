import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory TopologicalSpace
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

def leftTranslateSet (W : Set G) (x : G) : Set G := (fun z => x⁻¹ * z) ⁻¹' W

theorem pj_sep_T_open {W : Set G} (hW : IsOpen W) (x : G) : IsOpen (leftTranslateSet W x) :=
  hW.preimage (continuous_const.mul continuous_id)

theorem pj_sep_cover (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [SFinite μ] (W : Set G)
    (hW : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ S : Set G, S.Countable ∧ ∀ y : G, ∃ x ∈ S, ∃ a ∈ W, ∃ b ∈ W, y * a = x * b := by
  obtain ⟨A, hA⟩ := zorn_subset {A : Set G | A.PairwiseDisjoint (leftTranslateSet W)} (fun c hc hch =>
    ⟨⋃₀ c, (Set.pairwiseDisjoint_sUnion hch.directedOn).2 (fun a ha => hc ha), fun s hs => Set.subset_sUnion_of_mem hs⟩)
  have hAd : A.PairwiseDisjoint (leftTranslateSet W) := hA.prop
  refine ⟨A, ?_, ?_⟩
  · have hc := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) (As := fun x : A => leftTranslateSet W (x : G))
      (fun i => (pj_sep_T_open hW _).measurableSet)
      (fun i j hij => hAd i.2 j.2 (fun h => hij (Subtype.ext h)))
    have hall : {i : A | 0 < μ (leftTranslateSet W (i : G))} = Set.univ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      unfold leftTranslateSet
      rw [measure_preimage_mul]
      exact hW.measure_pos μ ⟨1, h1⟩
    rw [hall] at hc
    exact Set.countable_coe_iff.1 (Set.countable_univ_iff.1 hc)
  · intro y
    by_contra hcon
    push Not at hcon
    have hins : (insert y A).PairwiseDisjoint (leftTranslateSet W) := by
      refine hAd.insert fun x hx _ => ?_
      rw [Set.disjoint_left]
      intro z hz1 hz2
      refine hcon x hx _ hz1 _ hz2 ?_
      group
    have hsub : insert y A ⊆ A := hA.le_of_ge hins (Set.subset_insert y A)
    exact hcon y (hsub (Set.mem_insert y A)) 1 h1 1 h1 rfl

theorem pj_sep_nbhd (U : ℕ → Set G) (hUb : ∀ V ∈ nhds (1 : G), ∃ n, U n ⊆ V) (V : Set G) (hV : V ∈ nhds (1 : G)) :
    ∃ n, ∀ a ∈ U n, ∀ b ∈ U n, a * b⁻¹ ∈ V ∧ a⁻¹ * b ∈ V := by
  have c1 : Filter.Tendsto (fun p : G × G => p.1 * p.2⁻¹) (nhds ((1 : G), (1 : G))) (nhds 1) := by
    have : Continuous (fun p : G × G => p.1 * p.2⁻¹) := continuous_fst.mul continuous_snd.inv
    simpa using this.tendsto ((1 : G), (1 : G))
  have c2 : Filter.Tendsto (fun p : G × G => p.1⁻¹ * p.2) (nhds ((1 : G), (1 : G))) (nhds 1) := by
    have : Continuous (fun p : G × G => p.1⁻¹ * p.2) := continuous_fst.inv.mul continuous_snd
    simpa using this.tendsto ((1 : G), (1 : G))
  have h : (fun p : G × G => p.1 * p.2⁻¹) ⁻¹' V ∩ (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' V ∈ nhds ((1 : G), (1 : G)) :=
    Filter.inter_mem (Filter.mem_map.1 (c1 hV)) (Filter.mem_map.1 (c2 hV))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 h
  obtain ⟨n, hn⟩ := hUb (u ∩ v) (Filter.inter_mem hu hv)
  refine ⟨n, fun a ha b hb => ?_⟩
  exact huv (Set.mk_mem_prod (hn ha).1 (hn hb).2)

theorem pj_sep_second (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] [SFinite μ] (U : ℕ → Set G)
    (hUo : ∀ n, IsOpen (U n)) (hU1 : ∀ n, (1 : G) ∈ U n) (hUb : ∀ V ∈ nhds (1 : G), ∃ n, U n ⊆ V) :
    SecondCountableTopology G := by
  choose S hSc hS using fun n => pj_sep_cover μ (U n) (hUo n) (hU1 n)
  set B : Set (Set G) := ⋃ n, ⋃ m, (fun x => leftTranslateSet (U m) x) '' (S n) with hB
  have hBc : B.Countable := Set.countable_iUnion fun n => Set.countable_iUnion fun m => (hSc n).image _
  refine IsTopologicalBasis.secondCountableTopology (b := B) ?_ hBc
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro u hu
    simp only [hB, Set.mem_iUnion, Set.mem_image] at hu
    obtain ⟨n, m, x, -, rfl⟩ := hu
    exact pj_sep_T_open (hUo m) x
  · intro y O hy hO
    have hV : (fun z => y * z) ⁻¹' O ∈ nhds (1 : G) :=
      (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using hy)
    obtain ⟨m, hm⟩ := pj_sep_nbhd U hUb _ hV
    have hV2 : (fun z : G => z⁻¹) ⁻¹' (U m) ∈ nhds (1 : G) :=
      ((hUo m).preimage continuous_inv).mem_nhds (by simpa using hU1 m)
    obtain ⟨n, hn⟩ := pj_sep_nbhd U hUb _ hV2
    obtain ⟨x, hx, a, ha, b, hb, hab⟩ := hS n y
    have hxy : x⁻¹ * y ∈ U m := by
      have h1 := (hn a ha b hb).1
      have h2 : (a * b⁻¹)⁻¹ = x⁻¹ * y := by
        have : y = x * b * a⁻¹ := by rw [← hab]; group
        rw [this]; group
      have h3 : (a * b⁻¹)⁻¹ ∈ U m := h1
      rwa [h2] at h3
    refine ⟨leftTranslateSet (U m) x, ?_, hxy, ?_⟩
    · simp only [hB, Set.mem_iUnion, Set.mem_image]
      exact ⟨n, m, x, hx, rfl⟩
    · intro z hz
      have h1 := (hm _ hxy _ hz).2
      have h2 : y * ((x⁻¹ * y)⁻¹ * (x⁻¹ * z)) = z := by group
      have h3 : y * ((x⁻¹ * y)⁻¹ * (x⁻¹ * z)) ∈ O := h1
      rwa [h2] at h3

end General

theorem pj_sepF (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A) : SepF X := by
  have : X.μf.IsHaarMeasure := hX.2.1.2.2.2.1
  unfold SepF
  refine pj_sep_second X.μf (fun n => _) (fun n => X.I.topf_open (n + 1) (Nat.succ_le_succ (Nat.zero_le n))) ?_ ?_
  · intro n
    refine ⟨one_mem _, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    simp
  · intro V hV
    obtain ⟨g, hg, hsub⟩ := X.I.topf_basis V hV
    refine ⟨g - 1, ?_⟩
    have : g - 1 + 1 = g := by omega
    simp only [this]
    exact hsub

end Formalism.MainNotions.LeviCoordinates

end
