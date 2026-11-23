import Development.WeilBound.CoreStatements.ThetaDilations.SqPosOfNe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IwasawaDecompositionAdelicSL2Statement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v => mul_mem (hx v) (hy v)

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

def LN (F ι : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  zero_mem' := fun _ => ⟨0, fun _ => zero_mem _, (mul_zero _).symm⟩
  add_mem' := fun ha hb i => by
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨y', hy', e'⟩ := hb i
    exact ⟨y + y', fun v => add_mem (hy v) (hy' v), by rw [Pi.add_apply, e, e', mul_add]⟩
  neg_mem' := fun ha i => by
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, fun v => neg_mem (hy v), by rw [Pi.neg_apply, e, mul_neg]⟩

theorem co_LN {N : ℕ} (hN : 0 < N) : CO (LN F ι N) := by
  obtain ⟨-, -, -, h1, -, -, -, -, -, h2⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have e : (LN F ι N : Set (ι → A F)) = Set.univ.pi fun _ => (fun y => (N : A F) * y) '' Oh F := by
    ext x
    exact ⟨fun h i _ => (h i).imp fun y hy => ⟨hy.1, hy.2.symm⟩, fun h i => (h i trivial).imp fun y hy => ⟨hy.1, hy.2.symm⟩⟩
  refine ⟨e ▸ isCompact_univ_pi fun _ => h1.image (continuous_const.mul continuous_id), ?_⟩
  have e' : (LN F ι N : Set (ι → A F)) = ⋂ i, (fun x => x i) ⁻¹' {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
    ext x; rw [Set.mem_iInter]; rfl
  exact e' ▸ isOpen_iInter_of_finite fun i => (h2 N hN).preimage (continuous_apply i)

theorem LN_small {U : Set (ι → A F)} (hU : U ∈ 𝓝 (0 : ι → A F)) : ∃ N : ℕ, 0 < N ∧ (LN F ι N : Set (ι → A F)) ⊆ U := by
  obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  obtain ⟨N, hN, h⟩ := h1 (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨N, hN, fun x hx => hsub fun i _ => ?_⟩
  obtain ⟨y, hy, e⟩ := hx i
  exact e ▸ Set.mem_iInter.1 (h y hy) i

theorem orbit_adelic [MeasurableSpace (A F)] {ψ : AddChar (A F) ℂ} {h : A F} {B : Matrix ι ι (A F)}
    {μ : Measure (ι → A F)} (H : NAQuad ψ h B μ) {φ : (ι → A F) → ℂ} (hφ : SB φ) :
    ∃ (L' : AddSubgroup (ι → A F)) (s : Finset (ι → A F)) (C : ℝ), CO L' ∧ ∀ k : SL(2, A F), (∀ i j, k i j ∈ Oh F) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧
        ∃ c : (ι → A F) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by
  have hD := H.2.2.2.2.2
  obtain ⟨L, L', hL, hL', -, h0, hinv⟩ := sb_level hD hφ
  obtain ⟨L₂, hL₂, hK⟩ := co_cpt hD ((co_LN (F := F) (ι := ι) one_pos).1.image (continuous_const_smul h))
  obtain ⟨N, hN, hsub⟩ := LN_small (((hL'.2.inter (co_perp hD hL).2).inter (co_perp hD hL₂).2).mem_nhds
    ⟨⟨L'.zero_mem, (perpG hD L).zero_mem⟩, (perpG hD L₂).zero_mem⟩)
  refine orbit_bd H (Oh F) (co_LN hN) (fun a ha x hx i => ?_) hφ fun x hx y hy => funext fun u => ?_
  · obtain ⟨y, hy, e⟩ := hx i
    exact ⟨a * y, oh_mul ha hy, by rw [Pi.smul_apply, e, smul_eq_mul, mul_left_comm]⟩
  · have h1 : chiB ψ B (h • x) y = 1 := (hsub hy).2 _ (hK ⟨x, fun i => by
      obtain ⟨z, hz, e⟩ := hx i
      exact ⟨N * z, oh_mul (oh_nat N) hz, by rw [e, Nat.cast_one, one_mul]⟩, rfl⟩)
    rw [chiB, smul_dotProduct, smul_eq_mul] at h1
    rw [Heisenberg₂, hinv u x (hsub hx).1.1, AddChar.map_add_eq_mul, h1, mul_one]
    by_cases hu : u ∈ L
    · rw [show ψ (u ⬝ᵥ (B *ᵥ y)) = 1 from (hsub hy).1.2 u hu, one_mul]
    · rw [h0 u hu, mul_zero]

end PositivityTheory.PlacePermOperatorBicommutantSpan
