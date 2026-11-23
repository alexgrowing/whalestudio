import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.HalfIndex

theorem relIndex_nsmul_half : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT c v π hc hπ k hk
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  obtain ⟨σ, q1, q2⟩ := GlobalTheory.SplitLinear.exists_section (S := S) (T := T) hc.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D c = 0 := GlobalTheory.PlaceModelSum.infPart_split hc
  set L0 := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hL0
  set L := L0.comap σ with hL
  have hM : L0 ⊓ GlobalTheory.PlaceModel.half S T c = L.map σ := by
    rw [hL, AddSubgroup.map_comap_eq, ← GlobalTheory.SplitLinear.section_range hπ q1 q2, inf_comm]
  let nk : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    nsmulAddMonoidHom k
  have hcomm : (L.map σ).map (nsmulAddMonoidHom k) = (L.map nk).map σ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun w => (map_nsmul σ k w).symm
  have e1 : ((L0 ⊓ GlobalTheory.PlaceModel.half S T c).map (nsmulAddMonoidHom k)).relIndex (L0 ⊓ GlobalTheory.PlaceModel.half S T c) =
      (L.map nk).relIndex L := by
    rw [hM, hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ inj]
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hnk : ∀ w, nk w = (k : Fv D.host.F v) • w := fun w => (Nat.cast_smul_eq_nsmul (Fv D.host.F v) k w).symm
  have nkinj : Function.Injective nk := fun w w' h => by
    rw [hnk, hnk] at h
    exact smul_right_injective _ hk0 h
  have nksurj : Function.Surjective nk := fun w => ⟨(k : Fv D.host.F v)⁻¹ • w, by rw [hnk, smul_inv_smul₀ hk0]⟩
  have e2 : (L.map nk).relIndex L = L.relIndex (L.comap nk) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective L (L.comap nk) nkinj,
      AddSubgroup.map_comap_eq_self_of_surjective nksurj]
  let u : (Fv D.host.F v)ˣ := Units.mk0 _ hk0
  have hH : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v),
      ((k : Fv D.host.F v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v))) * w * (1 : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) = nk w := fun w => by
    rw [hnk, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hA := GlobalTheory.SplitLinear.relIndex_matrix_lattice D.host.F v S.rank T.rank L (L.comap nk)
    (fun o ho m hm => GlobalTheory.SplitLinear.section_smul hc.1 hπ q1 q2 o ho m hm)
    (GlobalTheory.SplitLinear.section_den hS hT hπ q1 q2) (fun w => ?_)
    ((k : Fv D.host.F v) • 1) 1 1 (u ^ T.rank) (by simp) (by simp [u, Matrix.det_smul]) (fun m hm => ?_) (fun w => ?_)
  rotate_left
  · obtain ⟨N, hN, h1⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS hT (σ w)
      (GlobalTheory.PlaceDatum.infPart_of_half hinf (q2 w))
    exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [hH]
    exact nsmul_mem hm k
  · rw [hH]
    rfl
  have hkc : (((k : v.adicCompletionIntegers D.host.F)) : Fv D.host.F v) = (k : Fv D.host.F v) := by simp
  have hv : Valued.v (k : Fv D.host.F v) ≠ 0 := by simpa using hk0
  have h1 : Valued.v (k : Fv D.host.F v) ≤ 1 := hkc ▸ (k : v.adicCompletionIntegers D.host.F).2
  have hl : WithZero.log (Valued.v (k : Fv D.host.F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (k : Fv D.host.F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (k : Fv D.host.F v))).toNat, by omega⟩
  have he' : Valued.v (k : Fv D.host.F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  have hcard := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers D.host.F v).2
    (k : v.adicCompletionIntegers D.host.F) e (by rw [hkc]; exact he')
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v u = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ e)⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, Units.val_mk0, he, zpow_neg, zpow_natCast]
  have h1' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  rw [e1, e2, hcard]
  apply Nat.cast_injective (R := ℝ)
  rw [hA, GlobalTheory.SplitLinear.absV_pow, hu, h1']
  push_cast
  rw [one_pow, one_mul, ← pow_mul, inv_pow, inv_inv, mul_comm T.rank S.rank]

end GlobalTheory.HalfIndex
