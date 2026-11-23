import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPointSpecializesInOpenOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNefStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionNonvanishingOfBaseChangeStatement
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

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.EffGen

theorem core_gen (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : X),
      IsClosed ({x} : Set X) → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' → (D + 1).choose 2 < m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, x ∈ nonzeroLocus s := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x hx hNn hNb hN'n hm hpos hBc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' (2 * m - 1) 2 hNn hNb hN'n (by omega)
  obtain ⟨m', D₀, U, hm', hD₀, hcur, hxU, hklt, hnk⟩ := GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective hK.2 X q D hq hD N₀ 2 x two_pos hn₀ hb₀ hx
    (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ hxZ he hdim
      have h2 := GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed hNN ℂ X q hq N N' N₀ hN hN' h₀ (2 * m - 1) 2 Z e hNn hN'n hc₀ hdim
      have h3 : ((2 * m - 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * m - 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((((D + 1).choose 2 : ℕ) : ℝ) * 2) ^ e < ((2 * m - 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have : (D + 1).choose 2 * 2 < 2 * m - 1 := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)
  obtain ⟨J, hJ, hvan⟩ := GlobalTheory.T.nadel_vanishing_canonical_add_boundary hK.1 X q D hq K B N hB D₀ m' 2 hm' two_pos hD₀ hNn hNb
    (fun C hC => by
      have e1 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq B N N' hB hN hN' m 1 C hC (by rw [hBc, one_smul])
      have e2 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq N₀ N N' h₀ hN hN' (2 * m - 1) 2 C hC hc₀
      have e3 := hcur C hC
      rw [e3, e1, e2]
      have : ((2 * m - 1 : ℕ) : ℚ) = 2 * m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [this]
      ring)
  exact GlobalTheory.T.exists_section_nonvanishing_point ℂ X q hq (tens K.bundle B) (isLB_tens K.isLB hB) J x U hx hxU
    (fun y hy => by
      rw [hJ]
      constructor
      · intro h
        by_contra hne
        exact h (hklt y hy hne)
      · rintro rfl
        exact hnk) (hvan 1 one_pos)

theorem effective_generation : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  intro hK hNN F _ _ Y p D _ hproj hgc hD1
  letI := algebraΓOfHom p
  intro K N N' B hN hN' hB a m y hNn hN'n hm hdec hBc
  obtain ⟨N₁, N₂, h₁, h₂, ha, hcls, hamp, hN₂⟩ := hdec
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  let σ : F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := F)).toRingHom
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hqp, hsurj⟩ := GlobalTheory.T.baseChange_smooth_projective_variety_properties F ℂ Y _ p q π D H hproj hgc
  haveI := hXi; haveI := hXn; haveI := hsm
  letI := algebraΓOfHom q
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  obtain ⟨y', rfl⟩ := hsurj y
  haveI : Smooth q := SmoothOfRelativeDimension.smooth D q
  obtain ⟨m₁, A, s₁, hm₁, hA, hAa, hy⟩ := hamp
  obtain ⟨x, hxc, hyx, hxU⟩ := GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType ℂ _ q (π ⁻¹ᵁ nonzeroLocus s₁) y' hy
  have hAx : AmpleAt (N₁.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine Y _ π N₁ h₁ x ⟨m₁, A, s₁, hm₁, hA, hAa, hxU⟩
  have hNnC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N hNn
  have hN'nC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N' hN'n
  have hN₂C := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N₂ hN₂
  have hc : a • cls (N.pull π) (pull_isLB hN π) = cls (N₁.pull π) (pull_isLB h₁ π) + cls (N₂.pull π) (pull_isLB h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add]
  have hbig := GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hcB : cls (B.pull π) (pull_isLB hB π) = m • cls (N.pull π) (pull_isLB hN π) + cls (N'.pull π) (pull_isLB hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul]
  obtain ⟨s, hs⟩ := core_gen hK hNN _ q D hqp hD1 (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    _ _ _ m x hxc hNnC hbig hN'nC hm hpos hcB
  exact GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange F ℂ Y _ p q π H hproj K.bundle B K.isLB hB y' ⟨s, hyx.mem_open (nonzeroLocus s).isOpen hs⟩

end GlobalTheory.EffGen
