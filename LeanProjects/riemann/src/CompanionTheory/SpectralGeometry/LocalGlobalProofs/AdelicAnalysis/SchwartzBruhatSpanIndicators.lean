import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompactSubgroupAndLevel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SbEqSumCosetIndicators
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

namespace GlobalTheory.CompanionTheory.SW.ThW

theorem sb_eq_sum_rational_coset_indicators :
    ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type)
      [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)),
      NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) →
      ∀ φ : (ι → A F) → ℂ, SB φ →
        ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ),
          φ = ∑ a ∈ s, c a • indC N a := by
  intro F _ _ _ _ ι _ _ χ μ h hopen φ hφ
  classical
  obtain ⟨-, -, -, -, -, hdense, -, hU, -, hNopen⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨-, hlev⟩ := GlobalTheory.CompanionTheory.SW.Core.compact_subgroup_and_level (ι → A F) χ μ h
  obtain ⟨L, L', -, -, -, oL', -, -, hinv⟩ := hlev φ hφ

  have h0 : (L' : Set (ι → A F)) ∈ 𝓝 (0 : ι → A F) := oL'.mem_nhds L'.zero_mem
  rw [nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, -, t, ht, hsub⟩ := h0
  have hU0 : (⋂ i, t i) ∈ 𝓝 (0 : A F) := Filter.iInter_mem.2 ht
  obtain ⟨N, hN, hNU⟩ := hU _ hU0
  have hle : latN F ι N ≤ L' := by
    intro x hx
    apply hsub
    intro i _
    obtain ⟨y, hy, e⟩ := hx i
    rw [e]
    exact Set.mem_iInter.1 (hNU y hy) i

  have happ : ∀ (a : ι → A F) (i : ι), ∃ b : F,
      ∃ y ∈ Oh F, a i - algebraMap F (A F) b = (N : A F) * y := by
    intro a i
    have ho : IsOpen {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y} :=
      (hNopen N hN).preimage (continuous_const.sub continuous_id)
    have hne : {b : A F | ∃ y ∈ Oh F, a i - b = (N : A F) * y}.Nonempty :=
      ⟨a i, 0, fun _ => zero_mem _, by simp⟩
    obtain ⟨b, hb⟩ := hdense.exists_mem_open ho hne
    exact ⟨b, hb⟩
  choose r hr using happ
  have hrl : ∀ a : ι → A F, a - toA (r a) ∈ latN F ι N := fun a i => hr a i
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.SW.Span.sb_eq_sum_coset_indicators (ι → A F) χ μ h φ hφ (latN F ι N)
    (hopen N hN) (fun x l hl => hinv x l (hle hl))
  have hind : ∀ (a x : ι → A F),
      Set.indicator {y | y - a ∈ latN F ι N} (fun _ => (1 : ℂ)) x = indC N (r a) x := by
    intro a x
    have hset : {y | y - a ∈ latN F ι N} = {y | y - toA (r a) ∈ latN F ι N} := by
      ext y
      have e : y - toA (r a) = (y - a) + (a - toA (r a)) := by abel
      simp only [Set.mem_setOf_eq]
      rw [e]
      exact (AddSubgroup.add_mem_cancel_right _ (hrl a)).symm
    rw [hset]
    rfl
  refine ⟨N, hN, s.image r, fun b => ∑ a ∈ s with r a = b, φ a, ?_⟩
  funext x
  rw [hs x, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, hind, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image r) (g := r)
    (fun a ha => Finset.mem_image_of_mem r ha)]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => ?_
  rw [(Finset.mem_filter.1 ha).2]

end GlobalTheory.CompanionTheory.SW.ThW
