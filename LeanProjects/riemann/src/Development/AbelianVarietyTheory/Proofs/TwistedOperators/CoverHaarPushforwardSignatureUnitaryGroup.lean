import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjGaugeInvariant

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem haar_of_proper {p q n : ℕ} (T : GrpData p q) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε))
    [μ.IsHaarMeasure] (π : T.G →* Formalism.REAL.UJ ε) (hp : IsProperMap π) (hs : Function.Surjective π) :
    ∃ c : NNReal, c ≠ 0 ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  have hc : Continuous π := hp.continuous
  have ht : Filter.Tendsto π (Filter.cocompact T.G) (Filter.cocompact (Formalism.REAL.UJ ε)) := by
    refine Filter.hasBasis_cocompact.tendsto_right_iff.2 fun K hK => ?_
    have hK' : IsCompact (π ⁻¹' K) := hp.isCompact_preimage hK
    exact hK'.compl_mem_cocompact
  haveI hν : (Measure.map π T.haar).IsHaarMeasure := Measure.isHaarMeasure_map T.haar π hc hs ht
  refine ⟨Measure.haarScalarFactor (Measure.map π T.haar) μ,
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', hp.isClosedMap.isQuotientMap hc hs,
    hc.measurable, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul _ μ

open GlobalTheory.RealPar.SqInt (reixHom continuous_reixHom) in

noncomputable def reixUJ {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Formalism.UG.Upq p q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨Units.map (reixHom e) g.1, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat_mem h g.2⟩
  invFun g := ⟨Units.map (reixHom e.symm) g.1, by
    have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
    change (Matrix.reindex e.symm e.symm (umat g))ᴴ * Formalism.UG.Jpq p q * Matrix.reindex e.symm e.symm (umat g) =
      Formalism.UG.Jpq p q
    have hJ : Formalism.UG.Jpq p q = Matrix.reindex e.symm e.symm (Formalism.REAL.Jm ε) := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.reindex_form h]; simp
    rw [hJ]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]⟩
  left_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e.symm e.symm (Matrix.reindex e e _) = _
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e e (Matrix.reindex e.symm e.symm _) = _
    simp))
  map_mul' a b := Subtype.ext (map_mul (Units.map (reixHom e)) a.1 b.1)
  continuous_toFun := Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val) _

theorem cover_haar_map : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  intro p q n T ε e br μ h hμ
  obtain ⟨C, hC, -⟩ := GlobalTheory.LeviIso.exists_conj_gauge_invariant n ε
    (if br then starRingEnd ℂ else RingHom.id ℂ) (by cases br <;> simp)
  let π : T.G →* Formalism.REAL.UJ ε :=
    (C.toMonoidHom.comp (reixUJ h).toMonoidHom).comp (GlobalTheory.DetSqrtCover.covHom T)
  have hcov : IsProperMap (GlobalTheory.DetSqrtCover.covHom T) := GlobalTheory.DetSqrtCover.isProperMap_covU T
  have hp : IsProperMap π :=
    (C.toHomeomorph.isProperMap.comp (reixUJ h).toHomeomorph.isProperMap).comp hcov
  have hs : Function.Surjective π :=
    (C.surjective.comp (reixUJ h).surjective).comp (GlobalTheory.DetSqrtCover.surjective_covU T)
  obtain ⟨c, hc0, hq, hm, hmap⟩ := haar_of_proper T ε μ π hp hs
  refine ⟨π, c, hc0, fun g => ?_, hq, hm, hmap⟩
  have hre : umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g)) =
      Matrix.reindex e e ((T.cov g : GL (Ix p q) ℂ) : Mat p q) :=
    GlobalTheory.RealPar.SqInt.reixHom_apply e _
  have hconj := hC (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))
  change umat (C (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))) = _
  refine hconj.trans ?_
  change (umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))).map _ = _
  rw [hre]
  cases br
  · ext i j
    simp [phi, plainMat]
  · ext i j
    simp [phi, barMat]

end GlobalTheory.ArchRec
