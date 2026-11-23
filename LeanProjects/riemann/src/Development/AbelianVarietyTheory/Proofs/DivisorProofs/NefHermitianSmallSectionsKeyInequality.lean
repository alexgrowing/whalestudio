import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyLeShiftOfSmallSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePullBirationalModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionTensorIsometricTransShiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNefCore

theorem key_ineq : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (B : HermLB p) (β : ℝ), B.IsNef D → B.IsSelfInter β → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (J : Type) [Fintype J] [Nonempty J] (e : J → X.functionField) (n : J → ℕ), LinearIndependent ℤ e → SmallFam B (boxFam e x) (fun c => n c.1 * Δ) → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ β + ((D : ℝ) + 1) * (Δ + D * Real.log 2 / 2 + Real.log (Fintype.card J) / 2) * gdeg B D := by
  intro hA hAmp hSP k _ X _ p D hX B β hB hβ x Δ hx hΔ J _ _ e n he hsm

  have hne : ∀ c, boxFam e x c ≠ 0 := by
    intro c
    simp only [boxFam]
    refine mul_ne_zero (he.ne_zero c.1) ?_
    exact Finset.prod_ne_zero_iff.2 fun i _ => hx.ne_zero i
  obtain ⟨Y, hY, π, φ, hvarY, hmod, htot⟩ := GlobalTheory.T.exists_birationalModel_totallyOrdered_family k X p D hX (J × Finset (Fin D)) (boxFam e x) hne
  haveI := hY
  set q := π ≫ p with hq
  set f : J × Finset (Fin D) → Y.functionField := fun c => φ (boxFam e x c) with hf
  have hbox : f = boxFam (φ ∘ e) (φ ∘ x) := by
    funext c
    simp [hf, boxFam, map_mul, map_prod]
  have hx' : AlgebraicIndependent ℤ (φ ∘ x) := hx.map' (f := φ.toIntAlgHom) φ.injective
  have he' : LinearIndependent ℤ (φ ∘ e) :=
    he.map' φ.toIntAlgHom.toLinearMap (LinearMap.ker_eq_bot.2 φ.injective)
  set w : J × Finset (Fin D) → ℝ := fun c => n c.1 * Δ with hw
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k Y q (J × Finset (Fin D)) f w htot
  obtain ⟨μ, hμ⟩ : ∃ μ, M.IsSelfInter μ := by
    obtain ⟨Φ, hΦ⟩ := ((hA.arExists k Y q D hvarY).2 PUnit fun _ => M).1
    exact ⟨_, ((hA.arIso k Y q D hvarY).2 PUnit _ Φ hΦ).1 PUnit.unit⟩

  have hN : ∀ j, n j ≤ ∑ i, n i := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hchain := GlobalTheory.T.boxFamily_movingParts_chain_bound hA hAmp hSP k Y q D hvarY (φ ∘ x) Δ hx' hΔ (∑ i, n i) J (φ ∘ e) n M μ he' hN
    (hbox ▸ htot) (hbox ▸ hM) hμ

  set s : ℝ := Real.log (Fintype.card (J × Finset (Fin D))) / 2 with hs
  set B' := B.pull π rfl with hB'
  have hsmall : SmallFam B' f w := GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel k X Y p q π rfl φ hmod B _ (boxFam e x) w hsm
  have hle : Le M (B'.shift (fun _ => s) fun _ => rfl) := GlobalTheory.T.fubiniStudy_le_shift_of_smallSections k Y q M B' _ f w hM hsmall
  have hle' := (GlobalTheory.T.hermLBLeBySmallSection_tensor_isometric_trans_shift k Y q (B'.shift (fun _ => s) fun _ => rfl) M M).2.2.2 Δ hle

  have hs0 : 0 ≤ s := by
    rw [hs]
    have : (1 : ℝ) ≤ Fintype.card (J × Finset (Fin D)) := by exact_mod_cast Fintype.card_pos
    have := Real.log_nonneg this
    linarith
  have hMnef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hA k Y q D hvarY M _ f w hM fun c => by
    simp only [hw]; exact mul_nonneg (Nat.cast_nonneg _) hΔ.le
  have hB'nef : B'.IsNef D := GlobalTheory.T.hermitianLineBundle_isNef_pullback hA hSP k X Y p q D D hX hvarY π rfl B hB
  have hA1 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY B' s hs0 hB'nef
  have hA2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY _ Δ hΔ.le hA1
  have hM2 := GlobalTheory.NefShift.isNef_shift_nonneg k Y q D hvarY M Δ hΔ.le hMnef

  obtain ⟨hg, hgs⟩ := GlobalTheory.T.geometricDegree_pull_birationalModel hA k X Y p q D hX hvarY π rfl φ hmod B
  have h1 := hgs β s hβ
  have h2 := hA.arShift k Y q D hvarY _ _ Δ h1
  have h3 := hA.arShift k Y q D hvarY M μ Δ hμ
  have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hA hAmp hSP k Y q D hvarY _ _ _ _ hA2 hM2 hle' h2 h3
  rw [GlobalTheory.CovTest.GeoSwap.gdeg_shift_const, hg] at hmono

  have hcard : s = Real.log (Fintype.card J) / 2 + D * Real.log 2 / 2 := by
    rw [hs, Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]
    push_cast
    rw [Real.log_mul (by exact_mod_cast Fintype.card_ne_zero) (by positivity), Real.log_pow]
    ring
  rw [hcard] at hmono
  nlinarith [hchain, hmono]

end GlobalTheory.HSNefCore
