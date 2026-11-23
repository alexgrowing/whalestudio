import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem exists_sameDiv_of_lbIso : ∀ (X : Scheme.{0}) (L M : LB X) (σ : L.Sec), L.IsLB → M.IsLB → LBIso L M →
    ∃ τ : M.Sec, SameDiv σ τ := by
  intro X L M σ hL hM h
  obtain ⟨u, hu⟩ := LBIso.symm h
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL, fun x => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
  refine ⟨M.U j ⊓ L.U i, i, j, inf_le_right, inf_le_left,
    ReciprocityTheory.ChartRestriction.G.Semi.res (ReciprocityTheory.ChartRestriction.G.DVR.divLe j i) (u.s (i, j)), ⟨hj, hi⟩, ?_⟩
  have e := ReciprocityTheory.ChartRestriction.G.DVR.secOfIso_spec (u := u) σ hu hM hL j i
  unfold ReciprocityTheory.ChartRestriction.G.DVR.isoCand at e
  change _ = _ * (ReciprocityTheory.ChartRestriction.G.DVR.rs (inf_le_left : M.U j ⊓ L.U i ≤ M.U j)
    ((ReciprocityTheory.ChartRestriction.G.DVR.secOfIso (u := u) σ hu hM hL).f j))
  rw [e, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end GlobalTheory.LogPair
