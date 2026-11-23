import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLociStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimLeZeroFibreAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIrreducibleZeroSetSectionClosedIrreducibleStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.AmpleCut

theorem le_of_succ_le_add_one {x : WithBot ℕ∞} {d : ℕ} (h : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ x + 1) :
    (d : WithBot ℕ∞) ≤ x := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h
  | coe x =>
    induction x using ENat.recTopCoe with
    | top => exact_mod_cast le_top
    | coe n =>
      have : d + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : d ≤ n)

theorem exists_irreducible_diff_NV : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d e : ℕ) (C : Set X) (f : X.functionField), ℓ.Prime →
    IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → ((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim C → 0 < e →
    f ∈ P.H e 0 → ∃ C' : Set X, IsIrreducible C' ∧ IsClosed C' ∧ C' ⊆ C \ NV P e 0 f ∧
      (d : WithBot ℕ∞) ≤ topologicalKrullDim C' := by
  intro k _ X _ p D hX P hA ℓ d e C f hℓ hCi hCc hCf hdim he hf
  by_cases h0 : C ∩ NV P e 0 f = ∅
  · refine ⟨C, hCi, hCc, fun x hx => ⟨hx, fun hx' => ?_⟩, ?_⟩
    · exact (Set.eq_empty_iff_forall_notMem.1 h0) x ⟨hx, hx'⟩
    · exact le_trans (by exact_mod_cast Nat.le_succ d) hdim
  obtain ⟨u, hu⟩ := (GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci k X p P e).2 f hf
  have hisP : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have hne : (C ∩ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)).Nonempty := by
    rw [← hu]; exact Set.nonempty_iff_ne_empty.2 h0
  by_cases hsub : C ⊆ (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u : Set X)
  · exfalso
    have haff := IsAmpleLB.isAffineOpen_nonzeroLocus p hA he u
    have h1 := GlobalTheory.T.topologicalKrullDim_le_zero_fibre_affineOpen k X p (GlobalTheory.MixHt.isAmb_of_isArithVar hX) ℓ _ C hℓ haff hCi hCc hCf hsub
    have h2 := hdim.trans h1
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by simpa using h2
    have := WithBot.coe_le_coe.1 this
    norm_cast at this
  · obtain ⟨C', h1, h2, h3, h4⟩ :=
      GlobalTheory.T.exists_irreducible_zeroSet_section_closedIrreducible k X p D hX (lbPow P.L.B e) u C (isLB_lbPow hA.isLB e) hCi hCc hne hsub
    refine ⟨C', h1, h2, ?_, le_of_succ_le_add_one (hdim.trans h4)⟩
    rw [hu]; exact h3

end GlobalTheory.AmpleCut
