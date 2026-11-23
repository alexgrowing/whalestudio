import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.RatPartition

theorem finite_ratW_mem {D : D7} (A T : HSp D) {C : Set (WO A T)} (hC : IsCompact C) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ C}.Finite := by
  obtain ⟨i1, -, -, i4, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i4; haveI := i5
  have hLc : IsClosed (ratMx D T.rank A.rank : Set (Mx D T.rank A.rank)) := AddSubgroup.isClosed_of_discrete
  let φ : Matrix (Fin T.rank) (Fin A.rank) D.host.E → ratMx D T.rank A.rank := fun γ => ⟨ratW T A γ, γ, rfl⟩
  have hφ : Function.Injective φ := fun a b h =>
    Matrix.map_injective GlobalTheory.MixModel.incA_injective (congrArg Subtype.val h)
  have hs : IsCompact ((↑) ⁻¹' C : Set (ratMx D T.rank A.rank)) := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact hC.inter_right hLc
  exact (hs.finite_of_discrete.preimage (f := φ) hφ.injOn : _)

theorem exists_partition_one : ∀ (D : D7) (A T : HSp D), ∃ χ : WO A T → ℝ, Continuous χ ∧ HasCompactSupport χ ∧
    (∀ u, 0 ≤ χ u) ∧ ∀ u, HasSum (fun γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E => χ (ratW T A γ + u)) 1 := by
  intro D A T
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i2; haveI := i4
  haveI : RegularSpace (Mx D T.rank A.rank) := IsTopologicalAddGroup.regularSpace _
  haveI : ContinuousSub (Mx D T.rank A.rank) := IsTopologicalAddGroup.to_continuousSub
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  have hS : IsCompact (tsupport f) := hfc
  let g : Matrix (Fin T.rank) (Fin A.rank) D.host.E → WO A T → ℝ := fun γ u => f (ratW T A γ + u)
  have hgc : ∀ γ, Continuous (g γ) := fun γ => f.continuous.comp (continuous_add_left (ratW T A γ : WO A T))
  have hfin : ∀ N : Set (WO A T), IsCompact N → {γ | (Function.support (g γ) ∩ N).Nonempty}.Finite := by
    intro N hN
    refine (finite_ratW_mem A T ((hS.prod hN).image (continuous_fst.sub continuous_snd))).subset ?_
    rintro γ ⟨u, hu, huN⟩
    exact ⟨(ratW T A γ + u, u), ⟨subset_tsupport _ hu, huN⟩, add_sub_cancel_right _ _⟩
  have hlf : LocallyFinite fun γ => Function.support (g γ) := by
    intro u
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds u
    exact ⟨N, hN, hfin N hNc⟩
  have hpt : ∀ u, (Function.support fun γ => g γ u).Finite := by
    intro u
    refine (hfin {u} isCompact_singleton).subset ?_
    intro γ hγ
    exact ⟨u, hγ, rfl⟩
  let s : WO A T → ℝ := fun u => ∑ᶠ γ, g γ u
  have hs_cont : Continuous s := continuous_finsum hgc hlf
  have hg0 : ∀ γ u, 0 ≤ g γ u := fun γ u => (hf01 _).1
  have hs1 : ∀ u, 1 ≤ s u := by
    intro u
    obtain ⟨x, ⟨γ, rfl⟩, hx⟩ := hKc u
    have h1 : g γ u = 1 := hf1 hx
    rw [← h1]
    exact single_le_finsum γ (hpt u) (fun j => hg0 j u)
  have hs_inv : ∀ γ₀ u, s (ratW T A γ₀ + u) = s u := by
    intro γ₀ u
    have e : ∀ γ, g γ (ratW T A γ₀ + u) = g (γ + γ₀) u := by
      intro γ
      simp only [g, ratW]
      rw [Matrix.map_add _ (map_add (incA D)) γ γ₀, add_assoc]
    simp only [s, e]
    exact finsum_comp_equiv (Equiv.addRight γ₀) (f := fun γ => g γ u)
  have hpos : ∀ u, 0 < s u := fun u => zero_lt_one.trans_le (hs1 u)
  refine ⟨fun u => f u * (s u)⁻¹, f.continuous.mul (hs_cont.inv₀ fun u => (hpos u).ne'), hfc.mul_right,
    fun u => mul_nonneg (hf01 u).1 (inv_nonneg.2 (hpos u).le), fun u => ?_⟩
  have e : (fun γ => f (ratW T A γ + u) * (s (ratW T A γ + u))⁻¹) = fun γ => g γ u * (s u)⁻¹ := by
    funext γ
    rw [hs_inv]
  simp only [e]
  have h : HasSum (fun γ => g γ u) (∑ γ ∈ (hpt u).toFinset, g γ u) :=
    hasSum_sum_of_ne_finset_zero (fun γ hγ => by simpa using hγ)
  rw [← finsum_eq_sum _ (hpt u)] at h
  have h2 := h.mul_right (s u)⁻¹
  rwa [mul_inv_cancel₀ (hpos u).ne'] at h2

end GlobalTheory.RatPartition

end
