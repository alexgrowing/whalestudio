import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncModelEmbeddedLogResolutionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVarStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BlockJoinInclusionsCompatStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp.Good

theorem coord_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply h
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem join_blocks {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {M : ℕ} (y₂ : (Σ _ : Unit, Fin M) → Ω) (hy : IsRelevant (mCoordIdeal y))
    (h₂ : ∃ i, y₂ ⟨(), i⟩ ≠ 0) : ∀ k, ∃ i, joinVec y y₂ ⟨k, i⟩ ≠ 0 := by
  rintro (k | u)
  · obtain ⟨i, hi⟩ := hy k
    exact ⟨i, coord_ne_zero y ⟨k, i⟩ hi⟩
  · obtain ⟨i, hi⟩ := h₂
    exact ⟨i, hi⟩

theorem exists_good_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (K' : Type) (_ : Fintype K') (ι' : K' → Type) (_ : ∀ k, Fintype (ι' k)) (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (y' : (Σ k, ι' k) → Ω) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J e) (Amp : HermLine ι'), IsBlockMap κ v ∧ y' ∘ v = y ∧ blockFnField y' = blockFnField y ∧ IsArithVar (mCoordIdeal y') (e + 1) ∧ IsEmbedded R.A (mCoordIdeal y') R.U R.lift ∧ IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), evC z (rename v β) = 0 → z ∈ mcPts J := by
  intro hRes K _ ι _ Ω _ _ y e β b hV hβ hβP
  obtain ⟨M, y₂, J, ⟨i₀, hi₀⟩, hfield, hJh, hJ, hsnc, hz⟩ :=
    GlobalTheory.T.adjoin_coords_arith_var hRes K ι Ω y e β b hV hβ hβP
  have hj := (GlobalTheory.T.block_join_inclusions_compat).1 K ι Unit (fun _ => Fin M) Ω y y₂
  have hb₁ := hj.1
  have hcomp : joinVec y y₂ ∘ joinInl ι (fun _ : Unit => Fin M) = y := hj.2.2.1
  have hblocks := join_blocks y y₂ hV.2.1.2.2 ⟨i₀, hi₀⟩
  have harith : IsArithVar (mCoordIdeal (joinVec y y₂)) (e + 1) := by
    refine GlobalTheory.T.isArithVar_of_block_algebraic K ι (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Sum.inl
      (joinInl ι fun _ : Unit => Fin M) Ω (joinVec y y₂) (e + 1) hb₁ hblocks ?_ ?_
    · rw [hcomp]; exact hV
    · rw [hcomp, hfield]
      intro t ht
      exact isAlgebraic_algebraMap (⟨t, ht⟩ : blockFnField y)
  obtain ⟨R, hR⟩ := GlobalTheory.T.snc_model_embedded_log_resolution (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M) Ω (joinVec y y₂) e J
    harith hJh hJ hsnc
  obtain ⟨Amp, h₁, h₂, h₃⟩ := GlobalTheory.T.embedded_resolution_ample_metric (K ⊕ Unit) (joinIdx ι fun _ : Unit => Fin M)
    (mCoordIdeal (joinVec y y₂)) J e R hR
  exact ⟨K ⊕ Unit, inferInstance, joinIdx ι fun _ : Unit => Fin M, inferInstance, Sum.inl,
    joinInl ι fun _ : Unit => Fin M, joinVec y y₂, J, R, Amp, hb₁, hcomp, hfield, harith, hR, h₁, h₂, h₃, hz⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.Good
