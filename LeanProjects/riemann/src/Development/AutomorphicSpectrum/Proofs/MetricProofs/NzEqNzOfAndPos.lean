import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCase

theorem nz_eq_nzOf_of_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) (r : ℕ) (y : Fin r → Λ), IsCMFam σ → IsIsoSub R.form I → (∀ a, y a ∈ I) → LinearIndependent (𝓞 E) y → (Submodule.span (𝓞 E) (Set.range y)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 → R.nz σ I = R.nzOf σ I y ∧ 0 < R.nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ R σ I r y hσ hI hy hli hidx
  by_cases hbot : I = ⊥
  · subst hbot
    have hy0 : ∀ a, y a = 0 := fun a => by simpa using hy a
    have hr : r = 0 := by
      by_contra h
      exact hli.ne_zero (⟨0, Nat.pos_of_ne_zero h⟩ : Fin r) (hy0 _)
    subst hr
    have hno : ¬ ∃ r v, IsNzFamily (⊥ : Submodule (𝓞 E) Λ) r v := by
      rintro ⟨ρ, v, h1, hv, hl, -⟩
      exact hl.ne_zero (⟨0, h1⟩ : Fin ρ) (by simpa using hv ⟨0, h1⟩)
    have hnz : R.nz σ (⊥ : Submodule (𝓞 E) Λ) = 1 := by
      simp only [RiemLat.nz]
      exact dif_neg hno
    have hof : R.nzOf σ (⊥ : Submodule (𝓞 E) Λ) y = 1 := by
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      simp [RiemLat.nzOf, hs]
    rw [hnz, hof]
    exact ⟨rfl, one_pos⟩
  · have hr : 1 ≤ r := by
      by_contra h
      have hr0 : r = 0 := by omega
      subst hr0
      have hs : Submodule.span (𝓞 E) (Set.range y) = ⊥ := by
        simp [Set.range_eq_empty]
      have hb : (⊥ : Submodule (𝓞 E) Λ).toAddSubgroup = ⊥ := rfl
      rw [hs, hb, AddSubgroup.relIndex_bot_left] at hidx
      haveI : Finite I.toAddSubgroup := Nat.finite_of_card_ne_zero hidx
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      haveI := R.free
      have hfin : IsOfFinAddOrder (⟨x, hx⟩ : I.toAddSubgroup) := isOfFinAddOrder_of_finite _
      obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hfin
      have hnx' : n • x = 0 := congrArg Subtype.val hnx
      have hzx : (n : ℤ) • x = 0 := by rw [natCast_zsmul]; exact hnx'
      exact hx0 ((smul_eq_zero.1 hzx).resolve_left (by exact_mod_cast hn.ne'))
    have hfam : IsNzFamily I r y := ⟨hr, hy, hli, hidx⟩
    have h := (GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ R σ I hσ hI hbot).2 r y hfam
    exact ⟨h.1, h.2.1⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCase
