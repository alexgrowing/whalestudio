import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactMapsPair

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal

noncomputable section
namespace GlobalTheory.LatPair.VolStep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_lat {n : Type} [Fintype n] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] :
    IsCompact (L : Set (n → k)) := by
  classical
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have h0 : IsCompact (stdLat k n : Set (n → k)) := by
    have := isCompact_univ_pi fun _ : n => isCompact_int k
    convert this using 1
    ext x
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  have h1 := h0.image (f := fun x : n → k => g.val *ᵥ x) (continuous_const.matrix_mulVec continuous_id)
  convert h1 using 1
  ext x
  simp only [SetLike.mem_coe, mem_smul_iff, Set.mem_image]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    show g • (g⁻¹ • x) = x
    simp
  · rintro ⟨y, hy, rfl⟩
    show g⁻¹ • (g • y) ∈ _
    simpa using hy

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_flagIn {n : Type} (c i : ℕ) : Continuous (flagIn (k := k) (n := n) c i) := by
  refine continuous_pi fun j => ?_
  rcases j with r | l
  · exact continuous_apply _
  · by_cases h : l.val < i
    · simp only [flagIn, Sum.elim_inr, dif_pos h]
      exact continuous_apply _
    · simp only [flagIn, Sum.elim_inr, dif_neg h]
      exact continuous_const

theorem region_eq {n : Type} (c : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) :
    {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} =
      (fun y : n ⊕ Fin i → k => q.inv • flagIn c i y) ⁻¹' (L : Set (n ⊕ Fin c → k)) := by
  ext y
  refine ⟨fun h => h.1, fun h => ⟨h, fun l hl => ?_⟩⟩
  simp [flagIn, not_lt.2 hl]

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (q : Unif k) (ν : Measure k) [ν.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L.IsLattice k] (i : ℕ), i ≤ c → IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} ∧ volStep ν q L i ≠ 0 ∧ volStep ν q L i ≠ ⊤ := by
  intro k _ _ _ _ _ _ n _ _ c q ν _ L _ i hi
  haveI := secondCountable k
  haveI := t2Space k
  have ho : IsOpen {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} := by
    rw [region_eq]
    exact (isClopen_lattice L).2.preimage ((continuous_flagIn c i).const_smul q.inv)
  refine ⟨ho, ?_, ?_⟩
  · refine ho.measure_ne_zero _ ⟨0, ?_⟩
    rw [region_eq]
    have : flagIn (k := k) (n := n) c i 0 = 0 := by
      funext j
      rcases j with r | l <;> simp [flagIn]
    simp [this]
  · have hK := (isCompact_lat L).image
      (f := fun (z : n ⊕ Fin c → k) (j : n ⊕ Fin i) => ((q.1 : 𝒪[k]) : k) * z (Sum.map id (Fin.castLE hi) j)) (by fun_prop)
    refine ne_top_of_le_ne_top (hK.measure_lt_top (μ := Measure.pi fun _ : n ⊕ Fin i => ν)).ne (measure_mono ?_)
    rw [region_eq]
    intro y hy
    refine ⟨_, hy, ?_⟩
    funext j
    rcases j with r | l
    · simp [flagIn, Unif.inv, q.ne_zero]
    · simp [flagIn, Unif.inv, q.ne_zero]

end GlobalTheory.LatPair.VolStep
