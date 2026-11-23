import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

theorem GlobalTheory.CompHt.eigtau_sum_mem_latT_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (δ : ℂ_[p]), δ ≠ 0 → ∀ (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H),
      (∀ w ∈ Q.eigV (embInt c Q.integers τ.1), (w ∈ htLat c Q τ.1 ↔ δ • w ∈ Q.latT)) →
      ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers τ.1) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q τ.1) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖δ⁻¹ * a i‖ ≤ 1) := by
  intro E _ _ _ H p _ δ hδ l c _ Q τ hyp n xx g hx hb a
  letI := H.starRing
  set s := ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) with hs
  have hsV : s ∈ Q.eigV (embInt c Q.integers τ.1) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  have h1 := hyp (δ⁻¹ • s) (Submodule.smul_mem _ _ hsV)
  rw [smul_smul, mul_inv_cancel₀ hδ, one_smul] at h1
  rw [← h1, hs, Finset.smul_sum]
  simp_rw [smul_smul]
  rw [hb.sum_mem_iff]
  simp_rw [mem_range_iff_norm_le]
