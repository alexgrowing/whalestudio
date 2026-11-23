import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMaximalLePrimeAddDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimQuotientLeOfMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.DimCoheight

theorem trdeg_eq_of_isFractionRing (R A K : Type) [CommRing R] [Nontrivial R] [CommRing A] [IsDomain A]
    [Field K] [Algebra R A] [Algebra A K] [Algebra R K] [IsScalarTower R A K] [FaithfulSMul R A]
    [IsFractionRing A K] : Algebra.trdeg R K = Algebra.trdeg R A := by
  have _ : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A K)
  have _ : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  rw [← trdeg_add_eq R A (A := K), trdeg_eq_zero (R := A) (A := K), add_zero]

theorem exists_ringKrullDim_affine_eq (Y : Scheme.{0}) [IsIntegral Y]
    (hft : ∀ U : Y.Opens, IsAffineOpen U → Algebra.FiniteType ℤ Γ(Y, U)) :
    ∃ c : WithBot ℕ∞, ∀ U : Y.Opens, IsAffineOpen U → Nonempty U → ringKrullDim Γ(Y, U) = c := by
  by_cases h0 : CharZero Y.functionField
  · refine ⟨((Cardinal.toENat (Algebra.trdeg ℤ Y.functionField) + 1 : ℕ∞) : WithBot ℕ∞),
      fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharZero Γ(Y, U) := ⟨fun a b h => by
      have := congrArg (algebraMap Γ(Y, U) Y.functionField) h
      simpa using this⟩
    have hinj : Function.Injective (algebraMap ℤ Γ(Y, U)) := RingHom.injective_int _
    have : FaithfulSMul ℤ Γ(Y, U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    rw [IntFiniteTypeDim.ringKrullDim_eq_trdeg_add_one _ hinj,
      ← trdeg_eq_of_isFractionRing ℤ Γ(Y, U) Y.functionField]
  · obtain ⟨p, hp⟩ := CharP.exists Y.functionField
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact h0 (CharP.charP_to_charZero _)
    have : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero Y.functionField p).resolve_right hp0⟩
    letI : Algebra (ZMod p) Y.functionField := ZMod.algebra _ p
    refine ⟨((Algebra.trdeg (ZMod p) Y.functionField).toENat : WithBot ℕ∞), fun U hU _ => ?_⟩
    have := hft U hU
    have := functionField_isFractionRing_of_isAffineOpen Y U hU
    have hK := IsFractionRing.injective Γ(Y, U) Y.functionField
    have : CharP Γ(Y, U) p := (algebraMap Γ(Y, U) Y.functionField).charP hK p
    letI : Algebra (ZMod p) Γ(Y, U) := ZMod.algebra _ p
    have : IsScalarTower (ZMod p) Γ(Y, U) Y.functionField := IsScalarTower.of_algebraMap_eq
      fun x => congrArg (· x) (RingHom.ext_zmod (algebraMap (ZMod p) Y.functionField)
        ((algebraMap Γ(Y, U) Y.functionField).comp (algebraMap (ZMod p) Γ(Y, U))))
    have : Algebra.FiniteType (ZMod p) Γ(Y, U) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) Γ(Y, U)
    exact GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg_fractionRing (ZMod p) Y.functionField

end GlobalTheory.DimCoheight

namespace GlobalTheory.DimCoheight

theorem finiteType_of_isAmb {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} (hq : IsAmb q)
    (U : Y.Opens) (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(Y, U) := by
  have := hq.finite
  have : IsProper q := CommonModel.isProper_of_isProjOver hq.isProjOver
  have : LocallyOfFiniteType (spMap (Int.castRingHom k)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hl : LocallyOfFiniteType (Spec.map (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k)))) := by
    rw [Spec.map_preimage]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hl
  have e : (Spec.preimage (hU.fromSpec ≫ q ≫ spMap (Int.castRingHom k))).hom = algebraMap ℤ Γ(Y, U) :=
    RingHom.ext_int _ _
  rw [e] at hl
  exact RingHom.finiteType_algebraMap.mp hl

theorem coheight_add_eq : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e →
    Order.coheight z + (e : ℕ∞) = d := by
  intro k _ Y _ q hq d hd z e hz
  have hft := finiteType_of_isAmb hq
  obtain ⟨c, hc⟩ := exists_ringKrullDim_affine_eq Y hft

  have hdc : (d : WithBot ℕ∞) ≤ c := by
    rw [← hd]
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    have hU : IsAffineOpen U := hU
    refine ⟨(U : Set Y), U.isOpen, hyU, ?_⟩
    have hne : Nonempty U := ⟨⟨y, hyU⟩⟩
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans (hc U hU hne).le

  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : Nonempty U := ⟨⟨z, hzU⟩⟩
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum Γ(Y, U), hU.fromSpec P = z := by
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hzU
    exact this
  have := hft U hU
  have hcA := hc U hU hne

  obtain ⟨M, hM, hMd⟩ : ∃ M : Ideal Γ(Y, U), M.IsMaximal ∧ (d : WithBot ℕ∞) ≤ M.height := by
    rcases Nat.eq_zero_or_eq_succ_pred d with h | h
    · obtain ⟨M, hM⟩ := Ideal.exists_maximal Γ(Y, U)
      exact ⟨M, hM, by rw [h]; exact_mod_cast bot_le⟩
    · by_contra hne
      push_neg at hne
      have : ringKrullDim Γ(Y, U) ≤ ((d.pred : ℕ) : WithBot ℕ∞) := by
        refine (ringKrullDim_le_iff_isMaximal_height_le _).2 fun m hm => ?_
        have h1 := hne m hm
        rw [h] at h1
        have h2 : m.height < ((d.pred + 1 : ℕ) : ℕ∞) := by exact_mod_cast h1
        exact_mod_cast Order.le_of_lt_add_one (by exact_mod_cast h2)
      have h3 := hdc.trans (hcA.symm.le.trans this)
      rw [h] at h3
      have : d.pred + 1 ≤ d.pred := by exact_mod_cast h3
      omega
  have h2 := FinTypeIntCatenary.height_maximal_le Γ(Y, U) P.asIdeal M

  let x : Spec Γ(Y, U) := P
  have eS := (asIso (hU.fromSpec.stalkMap x) ≪≫ Spec.stalkIso Γ(Y, U) x).commRingCatIsoToRingEquiv
  have hPh : (P.asIdeal.height : WithBot ℕ∞) = Order.coheight z := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P.asIdeal (Localization.AtPrime P.asIdeal),
      ← ringKrullDim_eq_of_ringEquiv eS, ← ringKrullDim_stalk_eq_coheight]
    rw [← hP]

  have h3 : ringKrullDim (Γ(Y, U) ⧸ P.asIdeal) ≤ e := by
    rw [← topologicalKrullDim_range_inter_closure_eq (B := Γ(Y, U)) hU.fromSpec P, hP, ← hz]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  have hge : (d : WithBot ℕ∞) ≤ (Order.coheight z : WithBot ℕ∞) + (e : WithBot ℕ∞) := by
    rw [← hPh]
    exact hMd.trans (h2.trans (add_le_add le_rfl h3))

  have hle : topologicalKrullDim (closure ({z} : Set Y)) + Order.coheight z ≤ topologicalKrullDim Y := by
    haveI : QuasiSober (closure ({z} : Set Y)) := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
    exact DimCodim.dim_add_le_of_le_coheight continuous_subtype_val Subtype.val_injective _
      fun w => Order.coheight_anti (specializes_iff_mem_closure.2 w.2)
  rw [hz, hd] at hle
  have a1 : (e : ℕ∞) + Order.coheight z ≤ d := by exact_mod_cast hle
  have a2 : (d : ℕ∞) ≤ Order.coheight z + e := by exact_mod_cast hge
  rw [add_comm] at a1
  exact le_antisymm a1 a2

end GlobalTheory.DimCoheight
