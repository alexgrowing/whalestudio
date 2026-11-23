import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := h' k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem fstPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0 := fun k => h (some k)

theorem sndPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0 := by
  intro k
  by_cases e : k = k₀
  · subst e
    obtain ⟨i, hi⟩ := h none
    refine ⟨i, ?_⟩
    change z (v₁ k ⟨k, i⟩) ≠ 0
    rw [v₁_self]
    exact hi
  · obtain ⟨i, hi⟩ := h (some k)
    refine ⟨i, ?_⟩
    change z (v₁ k₀ ⟨k, i⟩) ≠ 0
    rw [v₁_ne (p := ⟨k, i⟩) e]
    exact hi

theorem basePart_snd_eq_fst {σ : Type} (blk : σ → Option K) {k₀ : K} (p : σ) (hp : blk p = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hk⟩, i⟩ := q
  have e : k ≠ k₀ := by
    rintro rfl
    exact hk p hp
  change z (v₁ k₀ ⟨k, i⟩) = z (v₀ k₀ ⟨k, i⟩)
  rw [v₁_ne (p := ⟨k, i⟩) e]
  rfl

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr hb hW x z₀ z₁ h₀ h₁
  have hL : ∀ o, ∃ i, RW.lift x x ⟨o, i⟩ ≠ 0 := (RW.mem x x (RW.mem_U x)).1
  have hbase : SameOrbit (basePart M.blk z₀) (Rb.lift (pr x) (pr x)) :=
    orbit_trans (basePart_orbit M.blk h₀) (orbit_symm (hW.2.1 x))
  refine ⟨?_, ?_, blocks_of_orbit h₀ (fstPt_blocks hL), blocks_of_orbit h₁ (sndPt_blocks hL)⟩
  · obtain ⟨c, hc, e⟩ := hbase
    rw [e]
    exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x _ c hc).2 (Rb.mem (pr x) (pr x) (Rb.mem_U _))).1
  · have h₁' := basePart_orbit M.blk h₁
    rw [basePart_snd_eq_fst M.blk (τ, a) hb] at h₁'
    exact orbit_trans h₁' (orbit_symm (basePart_orbit M.blk h₀))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase
