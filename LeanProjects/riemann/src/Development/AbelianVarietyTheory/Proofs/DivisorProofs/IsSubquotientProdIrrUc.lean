import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Rank1
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegmentRepresentation
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGLOfExhaustion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GenSph

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

abbrev uc (a : ℂˣ) : IrrGL k := IrrGL.ofChar (unrChar k a) (isSmoothChar_of_isUnram (isUnram_unrChar k a))

theorem eq_first_of_isLSeg {Δ : Segment k} {y : IrrGL k} (h : IsLSeg Δ y.rep) (h1 : Δ.len = 1) : y = Δ.first := by
  have h2 := h.hasSupport
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.1 ((Segment.card_ms Δ).trans h1)
  have h3 : z = Δ.first := by
    have hm : z ∈ Δ.ms := by rw [hz]; exact Multiset.mem_singleton_self z
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hm)
    obtain rfl : a = 0 := by omega
    simp
  rw [hz, h3] at h2
  exact GlobalTheory.CompanionTheory.CuspPairSub.eq_of_hasSupport_singleton h2

theorem isSpherical_prodIrr_uc {c N : ℕ} (β : Fin c → ℂˣ) (hd : ∑ i, (uc k (β i)).1 = N) :
    IsSpherical (prodIrr (fun i => uc k (β i)) hd) := by
  have hv : ∀ i, ∃ v : (uc k (β i)).2.rep.V, v ≠ 0 ∧
      ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (uc k (β i)).1), (uc k (β i)).rep g v = v := fun i => by
    let r := IrrRep.det (Fin 1) (unrChar k (β i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (β i)))
    let e := equivRep r
    let u : r.V := (1 : ℂ)
    have hu : u ≠ 0 := show (1 : ℂ) ≠ 0 from one_ne_zero
    refine ⟨e u, fun h0 => hu (e.toLinearEquiv.injective (h0.trans (map_zero _).symm)), fun g hg => ?_⟩
    have h1 := e.toIntertwiningMap.isIntertwining _ _ g u
    refine h1.symm.trans (congrArg e ?_)
    have h4 : unrChar k (β i) (Matrix.GeneralLinearGroup.det g) = 1 :=
      isUnram_unrChar k (β i) _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg)
    show ((ofChar (detChar (Fin 1) (unrChar k (β i)))) g) (1 : ℂ) = (1 : ℂ)
    simp [ofChar, twist, detChar_apply]
    exact h4
  choose v hv0 hvK using hv
  obtain ⟨f, hf, hf1⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (stdBlocks (fun i => (uc k (β i)).1) hd)
    (ρ := piTensor fun i => (uc k (β i)).rep) (x := PiTensorProduct.tprod ℂ v) fun g hg => by
      rw [piTensor_tprod]
      congr 1
      funext a
      exact hvK a _ (hg a)
  refine (Submodule.ne_bot_iff _).2 ⟨f, hf, fun h0 => ?_⟩
  have h5 : PiTensorProduct.tprod ℂ v = 0 := by rw [← hf1, h0]; rfl
  have hl : ∀ i, ∃ l : Module.Dual ℂ (uc k (β i)).2.rep.V, l (v i) ≠ 0 := fun i => by
    by_contra! hn
    exact hv0 i ((Module.forall_dual_apply_eq_zero_iff ℂ (v i)).1 hn)
  choose l hl using hl
  let ev : (⨂[ℂ] i, (uc k (β i)).2.rep.V) →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compLinearMap l)
  have h6 : ev (PiTensorProduct.tprod ℂ v) = ∏ i, l i (v i) := by simp [ev]
  rw [h5, map_zero] at h6
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hl i) h6.symm

theorem isSubquotient_prodIrr_uc {N : ℕ} (α : Fin N → ℂˣ) (hd : ∑ i, (uc k (α i)).1 = N) :
    IsSubquotient (prodIrr (fun i => uc k (α i)) hd) (prinSeries fun i => unrChar k (α i)) := by
  let φ := multiProdEquiv (stdBlocks (fun i => (uc k (α i)).1) hd) fun a =>
    (equivRep (IrrRep.det (Fin 1) (unrChar k (α a)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α a))))).symm
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ _)

end GlobalTheory.GenSph

namespace GlobalTheory.GenSph
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

end GlobalTheory.GenSph

end
