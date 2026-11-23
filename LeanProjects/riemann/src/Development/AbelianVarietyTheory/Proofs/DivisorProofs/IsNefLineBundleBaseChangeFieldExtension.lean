import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefFieldExt

variable {k E : Type} [Field k] [Field E] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra E Γ(Y, ⊤)]

theorem isNef_pull (hN : Published.NefNumerics) [IsProper (strHom k X)] {L H : LB X} (h : IsNef k L)
    (hH : IsAmpleLB H) {H' : LB Y} (hH' : IsAmpleLB H') (g : Y ⟶ X) : IsNef E (L.pull g) := by
  have hL := LB.isLB_pull h.isLB g
  have hA := LB.isLB_pull hH.isLB g
  refine ⟨hL, fun C hC => ?_⟩
  let Z : Closeds X := Closeds.closure (g '' C)
  have hi : IsIrreducible (Z : Set X) := (hC.1.image g g.continuous.continuousOn).closure
  obtain ⟨φ, hφ⟩ : ∃ φ, φ ≫ redι Z = redι C ≫ g := ⟨IsClosedImmersion.lift (redι Z) (redι C ≫ g) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.map_vanishingIdeal]), IsClosedImmersion.lift_fac _ _ _⟩

  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hi
  have hZp : IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hHZ := hH.pull_of_isClosedImmersion (redι Z)
  have hproj := hHZ.isProjOver (strHom k _)
  have hLZ : IsNef k (L.pull (redι Z)) := h.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))

  letI := algebraΓAlong E (redι C)
  have := hC.isProper_strHom
  have := isIntegral_red hC.1

  have hdense : ∀ U : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
      genericPoint _ ∈ U → ∃ y, φ y ∈ U := fun U hU => by
    obtain ⟨V, hV, hUV⟩ := (redι Z).isClosedEmbedding.isInducing.isOpen_iff.1 U.isOpen
    have h1 : redι Z (genericPoint _) ∈ V := by
      rw [← Set.mem_preimage, hUV]; exact hU
    have h2 : redι Z (genericPoint _) ∈ closure (g '' C) := by
      have := (range_redι Z).le ⟨genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme, rfl⟩
      exact this
    obtain ⟨_, hv, ⟨c, hc, rfl⟩⟩ := mem_closure_iff.1 h2 V hV h1
    obtain ⟨y, rfl⟩ := (range_redι C).ge hc
    refine ⟨y, ?_⟩
    rw [← SetLike.mem_coe, ← hUV, Set.mem_preimage]
    have e : redι Z (φ y) = g (redι C y) := congrArg (fun q => q y) hφ
    rw [e]; exact hv
  have key : ∀ m : ℕ, 0 ≤ m * interNumRed E C ![L.pull g] + interNumRed E C ![H.pull g] := fun m => by
    have hbig := (hLZ.pow hHZ m).isBig_tens_ample hN hproj hHZ
    obtain ⟨r, ⟨s, hs0⟩, hr⟩ :=
      (hbig.frequently_hasNonzeroSec.and_eventually (Filter.eventually_ge_atTop 1)).exists
    obtain ⟨x, hx⟩ := hdense (nonzeroLocus s) ((sec_ne_zero_iff s).1 hs0)
    have hx' : x ∈ nonzeroLocus (secPull s φ) := (nonzeroLocus_secPull s φ).ge hx
    have hLZ' := LB.isLB_pull h.isLB (redι Z)
    have hHZ' := LB.isLB_pull hH.isLB (redι Z)
    have hr' := isLB_lbPow (isLB_tens (isLB_lbPow hLZ' m) hHZ') r
    have h0 := (interNum_one_nonneg_of_sec (k := E) (hH'.pull_of_isClosedImmersion (redι C))
      ((topologicalKrullDim_red C).trans hC.2) (LB.isLB_pull hr' φ) (secPull s φ)
      ((sec_ne_zero_iff _).1 (sec_ne_zero_of_mem hx'))).1
    have hT' := isLB_tens (isLB_lbPow hL m) hA
    have h1 : interNumRed E C ![lbPow (tens (lbPow (L.pull g) m) (H.pull g)) r] =
        interNum E (structureModule _) ![(lbPow (tens (lbPow (L.pull (redι Z)) m) (H.pull (redι Z))) r).pull φ] := by
      rw [interNumRed_one_eq (isLB_lbPow hT' r)]
      refine interNum_congr_cls E _ (isLB_vecOne (LB.isLB_pull (isLB_lbPow hT' r) _))
        (isLB_vecOne (LB.isLB_pull hr' φ)) fun i => ?_
      fin_cases i
      change pull (redι C) (cls _ (isLB_lbPow hT' r)) = pull φ (cls _ hr')
      rw [cls_lbPow_tens_lbPow hL hA, cls_lbPow_tens_lbPow hLZ' hHZ', cls_pull h.isLB, cls_pull hH.isLB,
        cls_pull h.isLB, cls_pull hH.isLB]
      simp only [map_nsmul, map_add, ← pull_comp, hφ]
    rw [← h1, hC.interNumRed_lbPow hH' hT', hC.interNumRed_of_cls_eq_add hH' hT' (isLB_lbPow hL m) hA rfl,
      hC.interNumRed_lbPow hH' hL] at h0
    exact nonneg_of_mul_nonneg_right h0 (Nat.cast_pos.2 hr)
  by_contra! hneg
  have := key ((interNumRed E C ![H.pull g]).natAbs + 1)
  have h2 := le_abs_self (interNumRed E C ![H.pull g])
  have h3 := abs_nonneg (interNumRed E C ![H.pull g])
  push_cast at this
  nlinarith

end GlobalTheory.NefFieldExt

namespace GlobalTheory.NefFieldExt

theorem isNef_baseChange : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0})
    (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p →
    letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  intro hN k E _ _ _ Y X p q π H hp
  letI := algebraΓOfHom p
  letI := algebraΓOfHom q
  intro L hL
  obtain ⟨hpp, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsProper (strHom k Y) := by rw [strHom_eq (f := p) fun _ => rfl]; exact hpp
  have : IsAffineHom π := MorphismProperty.of_isPullback H.flip inferInstance
  exact isNef_pull hN hL hA (hA.pull_of_isAffineHom π) π

end GlobalTheory.NefFieldExt
