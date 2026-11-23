import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLatticePointsInSiegelSetBoundStatement

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DBase

theorem ncard_biUnion_le' {α ι : Type*} (I : Finset ι) (S : ι → Set α) (h : ∀ i ∈ I, (S i).Finite) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) _)

end MainStatements.WeightKernel.Dec.DBase

namespace MainStatements.WeightKernel.Dec
open DBase

theorem base : Base := by
  intro D V r X Y hW c hc
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : GA D V)
  have hC₀ : IsCompact (V₀⁻¹ * V₀) := hV₀c.inv.mul hV₀c
  obtain ⟨A, B₀, hAB⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc _ hC₀
  refine ⟨A, fun Γ hΓ f hf hfs C W hC hW' => ?_⟩
  set K : Set (GA D V) := C⁻¹ * tsupport f * W⁻¹ with hK
  have hKc : IsCompact K := (hC.inv.mul hfs.isCompact).mul hW'.inv
  have hint : interior V₀ ∈ nhds (1 : GA D V) := interior_mem_nhds.2 hV₀n
  obtain ⟨I, hI⟩ := hKc.elim_finite_subcover (fun g : K => (g : GA D V) • interior V₀)
    (fun g => isOpen_interior.smul _) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩,
      ⟨1, mem_of_mem_nhds hint, by simp⟩⟩)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨max M 0 * I.card * max B₀ 0, fun t ht a ha x hx y hy => ?_⟩
  obtain ⟨hfin₀, hcnt₀⟩ := hAB t ht a ha
  set S₀ := {δ : GF V | a⁻¹ * rat V δ * a ∈ V₀⁻¹ * V₀}
  set S : K → Set (GF V) := fun g => {δ : GF V | a⁻¹ * rat V δ * a ∈ (g : GA D V) • V₀}
  have hS : ∀ g, (S g).Finite ∧ (S g).ncard ≤ S₀.ncard := by
    intro g
    rcases (S g).eq_empty_or_nonempty with h | ⟨δ₀, hδ₀⟩
    · rw [h]; simp
    have hmap : ∀ δ ∈ S g, δ₀⁻¹ * δ ∈ S₀ := by
      intro δ hδ
      obtain ⟨u, hu, hu'⟩ := hδ
      obtain ⟨u₀, hu₀, hu₀'⟩ := hδ₀
      refine ⟨u₀⁻¹, Set.inv_mem_inv.2 hu₀, u, hu, ?_⟩
      simp only [smul_eq_mul] at hu' hu₀'
      have e : a⁻¹ * rat V (δ₀⁻¹ * δ) * a = (a⁻¹ * rat V δ₀ * a)⁻¹ * (a⁻¹ * rat V δ * a) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e, ← hu', ← hu₀']; group
    have hinj : Set.InjOn (fun δ => δ₀⁻¹ * δ) (S g) := fun _ _ _ _ h => mul_left_cancel h
    have hf1 : (S g).Finite := Set.Finite.of_finite_image (hfin₀.subset (by
      rintro _ ⟨δ, hδ, rfl⟩; exact hmap δ hδ)) hinj
    exact ⟨hf1, Set.ncard_le_ncard_of_injOn _ hmap hinj hfin₀⟩
  set T := {δ : GF V | a⁻¹ * rat V δ * a ∈ K}
  have hTsub : T ⊆ ⋃ g ∈ I, S g := by
    intro δ hδ
    obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.1 (hI hδ)
    exact Set.mem_iUnion₂.2 ⟨g, hg, Set.smul_set_mono interior_subset hmem⟩
  have hUfin : (⋃ g ∈ I, S g).Finite := Set.Finite.biUnion I.finite_toSet fun g _ => (hS g).1
  have hTfin : T.Finite := hUfin.subset hTsub
  have hTcnt : (T.ncard : ℝ) ≤ I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A := by
    have h1 : T.ncard ≤ I.card * S₀.ncard := by
      refine (Set.ncard_le_ncard hTsub hUfin).trans ((ncard_biUnion_le' I S fun g _ => (hS g).1).trans ?_)
      simpa using Finset.sum_le_sum (s := I) fun g _ => (hS g).2
    have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
    calc (T.ncard : ℝ) ≤ I.card * S₀.ncard := by exact_mod_cast h1
      _ ≤ I.card * (max B₀ 0 * (∏ i, max (t i) 1) ^ A) := by
          gcongr
          exact hcnt₀.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring

  set g : Γ → ℂ := fun ν => f (x * a⁻¹ * ν * (a * y)) with hg
  have hsupp : ∀ ν : Γ, g ν ≠ 0 → ∃ δ ∈ T, rat V δ = ν := by
    intro ν hν
    obtain ⟨δ, hδ⟩ : (ν : GA D V) ∈ (ratEmb D.sp.cm.sig V.gram).range :=
      (range_ratEmb D.sp.cm.sig V.gram).symm ▸ hΓ ν.2
    refine ⟨δ, ?_, hδ⟩
    have hs : x * a⁻¹ * ν * (a * y) ∈ tsupport f := subset_tsupport _ hν
    show a⁻¹ * rat V δ * a ∈ K
    refine ⟨x⁻¹ * (x * a⁻¹ * ν * (a * y)), ⟨x⁻¹, Set.inv_mem_inv.2 hx, _, hs, rfl⟩, y⁻¹,
      Set.inv_mem_inv.2 hy, ?_⟩
    show _ = _
    rw [show rat V δ = ν from hδ]; group
  have hsf : (Function.support g).Finite := by
    refine (hTfin.image (rat V)).preimage (Subtype.val_injective.injOn) |>.subset ?_
    intro ν hν
    obtain ⟨δ, hδ, e⟩ := hsupp ν hν
    exact ⟨δ, hδ, e⟩
  have hcard : (hsf.toFinset.card : ℝ) ≤ T.ncard := by
    have : (Function.support g).ncard ≤ T.ncard := by
      have h2 : (Function.support g).ncard ≤ (rat V '' T).ncard :=
        Set.ncard_le_ncard_of_injOn Subtype.val (fun ν hν => by
          obtain ⟨δ, hδ, e⟩ := hsupp ν hν; exact ⟨δ, hδ, e⟩) Subtype.val_injective.injOn (hTfin.image _)
      exact h2.trans (Set.ncard_image_le hTfin)
    rw [Set.ncard_eq_toFinset_card _ hsf] at this
    exact_mod_cast this
  show ‖∑' ν : Γ, g ν‖ ≤ _
  rw [tsum_eq_sum (s := hsf.toFinset) (fun ν hν => by simpa using hν)]
  have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
    pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
  calc ‖∑ ν ∈ hsf.toFinset, g ν‖ ≤ ∑ ν ∈ hsf.toFinset, ‖g ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ hsf.toFinset, max M 0 := Finset.sum_le_sum fun ν _ => (hM _).trans (le_max_left _ _)
    _ = hsf.toFinset.card * max M 0 := by simp
    _ ≤ T.ncard * max M 0 := by gcongr
    _ ≤ (I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A) * max M 0 := by gcongr
    _ = _ := by ring

end MainStatements.WeightKernel.Dec
