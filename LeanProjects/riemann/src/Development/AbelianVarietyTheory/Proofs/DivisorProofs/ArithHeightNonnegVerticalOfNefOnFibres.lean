import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIntersectionNumberNonnegSubscheme
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.VertHeight

theorem charZero_residueField_genericPoint (Z : Scheme.{0}) [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) :
    CharZero (Z.residueField (genericPoint Z)) := by
  have h₁ : CharZero Z.functionField :=
    (RingHom.charZero_iff (Z.germToFunctionField_injective ⊤)).1 hc
  exact (RingHom.charZero_iff (Z.residue (genericPoint Z)).hom.injective).1 h₁

theorem height_nonneg_of_vertical : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (C : HermLB p) (h : X → ℝ), NefFib C →
    C.IsArithHeight h → ∀ z : X, ¬ CharZero (X.residueField z) → 0 ≤ h z := by
  intro k _ X _ p D hX C h hC H z hz
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  rcases hX.vertical_or_horizontal i with ⟨ℓ, _, ⟨a⟩⟩ | ⟨hc, -⟩
  · letI := a
    haveI := hX.finite
    obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    rw [H.vertical Z i (ZMod ℓ) d hd, Nat.card_zmod]
    refine mul_nonneg ?_ (Real.log_nonneg (by exact_mod_cast (Fact.out : ℓ.Prime).one_le))
    have hN := GlobalTheory.FibreNef.isNef_pull_of_nefOver ℓ i C
      ((GlobalTheory.VertForm.nefFib_iff C).1 hC ℓ Fact.out)
    rw [topSelf_def]
    exact_mod_cast GlobalTheory.nefNumerics_outright.1.interNum_nonneg
      (GlobalTheory.FibreNef.isProjOver_fibre hX.isProjOver ℓ i) hd fun _ => hN
  · haveI := charZero_residueField_genericPoint Z hc
    exact absurd ((i.residueFieldMap (genericPoint Z)).hom.charZero) hz

end GlobalTheory.VertHeight
