import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PartialFlagBlocks
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap

theorem orbit_symm {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  show z' q = (c q.1)⁻¹ * (c q.1 * z' q)
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem orbit_trans {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z')
    (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext q
  show c q.1 * (c' q.1 * z'' q) = c q.1 * c' q.1 * z'' q
  rw [mul_assoc]

theorem not_mem_mcPts_top {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h1 := (show (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ (⊤ : Ideal (MRing ι)), eval z (map (Int.castRingHom ℂ) f) = 0 from hz).2 1 Submodule.mem_top
  simp at h1

theorem factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N) (n e e' : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (R : AnLogRes (mCoordIdeal y) ⊤ e)
    (Rp : AnLogRes (mCoordIdeal (y ∘ stepV M p)) ⊤ e') (pr : R.X → Rb.X) (prp : Rp.X → Rb.X) (h : R.X → Rp.X),
    (∀ x, SameOrbit (basePart M.blk (R.lift x x)) (Rb.lift (pr x) (pr x))) →
    (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ stepV M p = Rp.lift x x ∧
      SameOrbit (basePart M.blk z) (Rb.lift (prp x) (prp x))) →
    (∀ x, SameOrbit (Rp.lift (h x) (h x)) (R.lift x x ∘ stepV M p)) →
    (∀ x, prp (h x) = pr x) ∧ ∀ x x', pr x = pr x' →
      (∀ k, M.blk p = some k → ∃ a : ℂ, ∀ m : ι k, R.lift x x ⟨k, m⟩ = a * R.lift x' x' ⟨k, m⟩) → h x = h x' := by
  intro K _ ι _ Φ _ y Ψ N j M p n e e' Rb R Rp pr prp hh H1 H2 H3
  have hnz : ∀ x k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hb : ∀ z w : (Σ k, ι k) → ℂ, SameOrbit (z ∘ stepV M p) (w ∘ stepV M p) →
      SameOrbit (basePart M.blk z) (basePart M.blk w) := by
    rintro z w ⟨c, hc, hzw⟩
    exact ⟨fun k => c ⟨k.1, Or.inl k.2⟩, fun k => hc _,
      funext fun q => congrFun hzw ⟨⟨q.1.1, Or.inl q.1.2⟩, q.2⟩⟩
  refine ⟨fun x => ?_, fun x x' hpr hsc => ?_⟩
  · obtain ⟨z, -, hz1, hz2⟩ := H2 (hh x)
    have o1 : SameOrbit (z ∘ stepV M p) (R.lift x x ∘ stepV M p) := by
      rw [hz1]
      exact H3 x
    exact Rb.inj _ _ (not_mem_mcPts_top _)
      (orbit_trans (orbit_trans (orbit_symm hz2) (hb _ _ o1)) (H1 x))
  · apply Rp.inj _ _ (not_mem_mcPts_top _)
    refine orbit_trans (H3 x) (orbit_trans ?_ (orbit_symm (H3 x')))
    have h1' := H1 x'
    rw [← hpr] at h1'
    obtain ⟨cb, hcb, hbeq⟩ := orbit_trans (H1 x) (orbit_symm h1')
    refine ⟨fun k => if hk : (∀ p', M.blk p' ≠ some k.1) then cb ⟨k.1, hk⟩
      else (hsc k.1 (k.2.resolve_left hk)).choose, fun k => ?_, ?_⟩
    · dsimp only
      split_ifs with hk
      · exact hcb _
      · intro h0
        obtain ⟨i, hi⟩ := hnz x k.1
        apply hi
        rw [(hsc k.1 (k.2.resolve_left hk)).choose_spec i, h0, zero_mul]
    · funext q
      show R.lift x x ⟨q.1.1, q.2⟩ = _ * R.lift x' x' ⟨q.1.1, q.2⟩
      dsimp only
      split_ifs with hk
      · exact congrFun hbeq ⟨⟨q.1.1, hk⟩, q.2⟩
      · exact (hsc q.1.1 (q.1.2.resolve_left hk)).choose_spec q.2

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepMap
