import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNatMulIntegralMatricesSubsetOpenAddSubgrou

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SBBox

theorem exists_nhds_zero_add_eq {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X] {Y : Type}
    [Zero Y] {g : X → Y} (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N ∈ nhds (0 : X), ∀ y, ∀ u ∈ N, g (y + u) = g y := by
  classical
  have hW : ∀ x : X, ∃ W ∈ nhds (0 : X), ∀ a ∈ W, ∀ b ∈ W, g (x + (a + b)) = g x := by
    intro x
    have h1 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ nhds (0 : X) := by
      refine (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id) |>.mem_nhds ?_
      simp
    obtain ⟨W, hW, hWW⟩ := exists_nhds_zero_half h1
    exact ⟨W, hW, fun a ha b hb => hWW a ha b hb⟩
  choose W hW0 hWg using hW
  let V : X → Set X := fun x => W x ∩ Neg.neg ⁻¹' W x
  have hV0 : ∀ x, V x ∈ nhds (0 : X) := fun x => Filter.inter_mem (hW0 x) (neg_mem_nhds_zero X (hW0 x))
  have hcov : tsupport g ⊆ ⋃ x : X, (fun y => y - x) ⁻¹' interior (V x) := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    simp only [Set.mem_preimage, sub_self]
    exact mem_interior_iff_mem_nhds.2 (hV0 x)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun x => (fun y => y - x) ⁻¹' interior (V x))
    (fun x => isOpen_interior.preimage (continuous_id.sub continuous_const)) hcov
  refine ⟨⋂ x ∈ t, V x, (Filter.biInter_finset_mem t).2 fun x _ => hV0 x, fun y u hu => ?_⟩
  have hu' : ∀ x ∈ t, u ∈ W x ∧ -u ∈ W x := fun x hx => by
    have := Set.mem_iInter₂.1 hu x hx
    exact ⟨this.1, this.2⟩
  have h0 : ∀ x, (0 : X) ∈ W x := fun x => mem_of_mem_nhds (hW0 x)
  by_cases hy : y ∈ tsupport g
  · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hyx' : y - x ∈ W x := (interior_subset hyx : y - x ∈ V x).1
    have e1 : g (y + u) = g x := by
      have := hWg x (y - x) hyx' u (hu' x hx).1
      rwa [show x + (y - x + u) = y + u by abel] at this
    have e2 : g y = g x := by
      have := hWg x (y - x) hyx' 0 (h0 x)
      rwa [show x + (y - x + 0) = y by abel] at this
    rw [e1, e2]
  · by_cases hyu : y + u ∈ tsupport g
    · obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyu)
      have hyx' : y + u - x ∈ W x := (interior_subset hyx : y + u - x ∈ V x).1
      have e1 : g y = g x := by
        have := hWg x (y + u - x) hyx' (-u) (hu' x hx).2
        rwa [show x + (y + u - x + -u) = y by abel] at this
      have e2 : g (y + u) = g x := by
        have := hWg x (y + u - x) hyx' 0 (h0 x)
        rwa [show x + (y + u - x + 0) = y + u by abel] at this
      rw [e1, e2]
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

variable {F : Type} [Field F] [NumberField F]

def ballR (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (v.adicCompletion F) :=
  Valued.v.leAddSubgroup (v.intValuation r)

theorem mem_ballR {r : 𝓞 F} {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} :
    x ∈ ballR r v ↔ Valued.v x ≤ v.intValuation r := Iff.rfl

theorem isOpen_ballR {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (ballR r v : Set (v.adicCompletion F)) := by
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)
  have hcv : Valued.v c = v.intValuation r := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R v r
  have hc : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hcv
    exact (v.intValuation_ne_zero r hr) hcv.symm
  have e : (ballR r v : Set (v.adicCompletion F)) =
      (fun x => x / c) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    change Valued.v x ≤ v.intValuation r ↔ Valued.v (x / c) ≤ 1
    rw [map_div₀, ← hcv, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hc))]
  rw [e]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_id.div_const c)

theorem ballR_subset (r : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (ballR r v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F := fun x hx => by
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (mem_ballR.1 hx).trans (v.intValuation_le_one r)

theorem eventually_ballR_eq {r : 𝓞 F} (hr : r ≠ 0) :
    ∀ᶠ v in Filter.cofinite, (ballR r v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F := by
  have h : (Ideal.span {r} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_dvd]
  refine lt_of_le_of_ne (v.intValuation_le_one r) fun h1 => hv ?_
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_ballR, h1, HeightOneSpectrum.mem_adicCompletionIntegers]

end GlobalTheory.SBBox

namespace GlobalTheory.SBBox

theorem exists_box_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  intro F _ _ κ _ g hg
  classical
  obtain ⟨N, hN, hNg⟩ := exists_nhds_zero_add_eq hg.1 hg.2
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, -, t, ht, hIt⟩ := hN
  have hr : ∀ i, ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ y : FiniteAdeleRing (𝓞 F) F,
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ v.intValuation r) → y ∈ t i :=
    fun i => GlobalTheory.OpenSubAdele.exists_small_of_mem_nhds (ht i)
  choose r hr0 hrt using hr
  set R : 𝓞 F := ∏ i, r i
  have hR0 : R ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hr0 i
  have hle : ∀ i (v : HeightOneSpectrum (𝓞 F)), v.intValuation R ≤ v.intValuation (r i) := by
    intro i v
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem r (Finset.mem_univ i)
    rw [show R = r i * c from hc, map_mul]
    exact mul_le_of_le_one_right' (v.intValuation_le_one c)
  refine ⟨ballR R, isOpen_ballR hR0, ballR_subset R, eventually_ballR_eq hR0, fun y u hu => ?_⟩
  refine hNg y u (hIt fun i _ => hrt i (u i) fun v => ?_)
  exact (mem_ballR.1 (hu i v)).trans (hle i v)

end GlobalTheory.SBBox
