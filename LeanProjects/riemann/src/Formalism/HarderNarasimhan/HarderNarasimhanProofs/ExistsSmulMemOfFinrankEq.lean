import Formalism.HarderNarasimhan.DegSupermodZ
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.LatticeSlopes.LatticeSlopesProofs.DiscreteTopologyOfLe

open Module Submodule

noncomputable section

namespace Formalism.HN

theorem exists_smul_mem_of_finrank_eq {E : Type*} [AddCommGroup E] (S N : Submodule ℤ E) [Module.Finite ℤ S]
    (hNS : N ≤ S) (hrk : finrank ℤ S = finrank ℤ N) :
    ∀ x ∈ S, ∃ a : ℤ, a ≠ 0 ∧ a • x ∈ N := by
  intro x hx
  set P : Submodule ℤ S := N.comap S.subtype with hP
  have hPr : finrank ℤ P = finrank ℤ N :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hNS)
  have h := P.finrank_quotient_add_finrank
  have h0 : finrank ℤ (S ⧸ P) = 0 := by omega
  obtain ⟨a, ha, hax⟩ := (Module.finrank_eq_zero_iff.1 h0) (Submodule.Quotient.mk ⟨x, hx⟩)
  refine ⟨a, ha, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  exact hax

theorem satR_mem_zl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E) (N : Submodule R V) (y : E) :
    y ∈ zl ρ N ↔ ∃ x ∈ N, ρ x = y := Iff.rfl

theorem real_saturation_property : SatR := by
  intro R V E _ _ _ _ _ _ ρ L N hL hNL
  obtain ⟨hinj, hdisc⟩ := hL
  have : DiscreteTopology (zl ρ L) := hdisc
  have hNL' : zl ρ N ≤ zl ρ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (satR_mem_zl ρ N y).1 hy
    exact (satR_mem_zl ρ L _).2 ⟨x, hNL hx, rfl⟩
  obtain ⟨-, hNS, hrk⟩ := Formalism.F.saturProps E (zl ρ L) (zl ρ N) hdisc hNL'
  set S := Formalism.F.satur (zl ρ L) (zl ρ N) with hSdef
  have : DiscreteTopology S :=
    Formalism.F.discreteTopology_of_le (L := zl ρ L) inf_le_left
  have htor := exists_smul_mem_of_finrank_eq S (zl ρ N) hNS hrk
  have hspan : ∀ y : E, y ∈ S ↔ y ∈ zl ρ L ∧ y ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) :=
    fun y => Submodule.mem_inf
  refine ⟨{ carrier := {x | x ∈ L ∧ ρ x ∈ S}
            add_mem' := ?_
            zero_mem' := ?_
            smul_mem' := ?_ }, ?_, ?_, ?_⟩
  · rintro x y ⟨hxL, hxS⟩ ⟨hyL, hyS⟩
    refine ⟨L.add_mem hxL hyL, ?_⟩
    rw [map_add]
    exact S.add_mem hxS hyS
  · refine ⟨L.zero_mem, ?_⟩
    rw [map_zero]
    exact S.zero_mem
  · rintro c x ⟨hxL, hxS⟩
    have hcxL : c • x ∈ L := L.smul_mem c hxL
    refine ⟨hcxL, (hspan _).2 ⟨(satR_mem_zl ρ L _).2 ⟨c • x, hcxL, rfl⟩, ?_⟩⟩
    obtain ⟨a, ha, hax⟩ := htor (ρ x) hxS
    obtain ⟨n, hnN, hn⟩ := (satR_mem_zl ρ N _).1 hax
    have haxL : a • x ∈ L := L.toAddSubgroup.zsmul_mem hxL a
    have hn' : n = a • x := by
      apply hinj (hNL hnN) haxL
      rw [hn, map_zsmul]
    have haxN : a • x ∈ N := hn' ▸ hnN
    have h1 : a • (c • x) ∈ N := by
      rw [smul_comm]
      exact N.smul_mem c haxN
    have h2 : a • ρ (c • x) ∈ zl ρ N := by
      rw [← map_zsmul]
      exact (satR_mem_zl ρ N _).2 ⟨_, h1, rfl⟩
    have h3 : (a : ℝ) • ρ (c • x) ∈ span ℝ ((zl ρ N : Submodule ℤ E) : Set E) := by
      rw [Int.cast_smul_eq_zsmul]
      exact Submodule.subset_span h2
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have h4 := (span ℝ ((zl ρ N : Submodule ℤ E) : Set E)).smul_mem (a : ℝ)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at h4
  · intro x hx
    exact ⟨hNL hx, hNS ((satR_mem_zl ρ N _).2 ⟨x, hx, rfl⟩)⟩
  · intro x hx
    exact hx.1
  · ext y
    rw [satR_mem_zl]
    constructor
    · rintro ⟨x, ⟨-, hxS⟩, rfl⟩
      exact hxS
    · intro hy
      obtain ⟨x, hxL, rfl⟩ := (satR_mem_zl ρ L _).1 ((hspan y).1 hy).1
      exact ⟨x, ⟨hxL, hy⟩, rfl⟩

end Formalism.HN
