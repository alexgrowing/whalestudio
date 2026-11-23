import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem re_pi_bijective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), Function.Bijective FA.Re.π := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hdeg0 := FA.Re.degree
  unfold ReciprocityTheory.AnForm.M.IsDegreeOff at hdeg0
  have hdeg := hdeg0.2.2.2.2.1
  rw [FA.br_empty, FA.deg_one] at hdeg
  have h1 : ∀ x, ∃ a, FA.Re.π ⁻¹' {x} = {a} := fun x => Set.ncard_eq_one.1 (hdeg x (by simp))
  constructor
  · intro a b hab
    obtain ⟨c, hc⟩ := h1 (FA.Re.π a)
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton _)
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := Set.mem_preimage.2 (Set.mem_singleton_iff.2 hab.symm)
    rw [hc] at ha hb
    exact (Set.mem_singleton_iff.1 ha).trans (Set.mem_singleton_iff.1 hb).symm
  · intro x
    obtain ⟨c, hc⟩ := h1 x
    have hcx : c ∈ FA.Re.π ⁻¹' {x} := by
      rw [hc]
      exact Set.mem_singleton c
    exact ⟨c, Set.mem_singleton_iff.1 (Set.mem_preimage.1 hcx)⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
