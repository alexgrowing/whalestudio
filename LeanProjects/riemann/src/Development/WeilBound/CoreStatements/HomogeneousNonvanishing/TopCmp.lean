import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpBuild
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.CoordK

theorem side_eq (II : IntersectionSystem) (hPF : HasPFCoord II)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Kᵢ : Type} [Fintype Kᵢ] {ιᵢ : Kᵢ → Type} [∀ k, Fintype (ιᵢ k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κᵢ : Kᵢ → K} {vᵢ : (Σ k, ιᵢ k) → Σ k, ι k} {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι' k) → Ω}
    {D : ℕ} {σᵢ τ : Type} {Sᵢ : AnSys D σᵢ} {S : AnSys D τ}
    (Reᵢ : Realis Sᵢ (mCoordIdeal (y ∘ vᵢ))) (Re : Realis S (mCoordIdeal y')) (e : σᵢ → τ)
    (hbᵢ : IsBlockMap κᵢ vᵢ) (hb : IsBlockMap κ v) (hyv : y' ∘ v = y) (hfn : blockFnField y' = blockFnField y)
    (hdeg : Re.deg = 1) (hpull : ∀ a t, IsPullHerm (κ ∘ κᵢ) (v ∘ vᵢ) (Reᵢ.line a t) (Re.line (e a) t))
    (w : Fin (D + 1) → σᵢ) (t : ℝ) (ht : 0 < t) (ht' : t ≤ Sᵢ.t₀) :
    (IntermediateField.relfinrank (blockFnField (y ∘ vᵢ)) (blockFnField y) : ℝ) *
        II Kᵢ ιᵢ (mCoordIdeal (y ∘ vᵢ)) (D + 1) (fun j => Reᵢ.line (w j) t) =
      Re.num II t (fun j => e (w j)) := by
  have hbc : IsBlockMap (κ ∘ κᵢ) (v ∘ vᵢ) := by
    obtain ⟨h1, h2, h3, h4⟩ := hb
    obtain ⟨g1, g2, g3, g4⟩ := hbᵢ
    refine ⟨h1.comp g1, h2.comp g2, fun p => by simp [Function.comp, h3, g3], ?_⟩
    rintro q ⟨k, hk⟩
    obtain ⟨p, rfl⟩ := h4 q ⟨κᵢ k, hk⟩
    have hp : p.fst = κᵢ k := h1 (by rw [← h3]; exact hk.symm)
    obtain ⟨r, rfl⟩ := g4 p ⟨k, hp.symm⟩
    exact ⟨r, rfl⟩
  have hy : y' ∘ (v ∘ vᵢ) = y ∘ vᵢ := by rw [← Function.comp_assoc, hyv]
  have himg : imageZ (v ∘ vᵢ) (mCoordIdeal y') = mCoordIdeal (y ∘ vᵢ) := by
    rw [JoinBlock.imageZ_coord (κ ∘ κᵢ) (v ∘ vᵢ) y' hbc.1 hbc.2.2.1, hy]
  have key := hPF Kᵢ ιᵢ K' ι' (κ ∘ κᵢ) (v ∘ vᵢ) Ω y' (D + 1) (fun j => Reᵢ.line (w j) t)
    (fun j => Re.line (e (w j)) t) hbc Re.arith (by rw [himg]; exact Reᵢ.arith)
    (fun j => Reᵢ.line_smooth (w j) t ht ht') (fun j => hpull (w j) t)
  rw [himg, hy, hfn] at key
  simp only [Realis.num, hdeg, Nat.cast_one, div_one]
  exact key.symm

end GlobalTheory.CompanionTheory.Ar.Cmp.CoordK

namespace PositivityTheory.UnitarySelfGeneration

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

end PositivityTheory.UnitarySelfGeneration
