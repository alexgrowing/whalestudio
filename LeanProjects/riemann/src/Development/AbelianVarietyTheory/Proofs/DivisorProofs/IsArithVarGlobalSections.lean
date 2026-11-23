import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

noncomputable section

namespace GlobalTheory.SteinBase

theorem ringKrullDim_integers (F : Type) [Field F] [NumberField F] : ringKrullDim (𝓞 F) = 1 := by
  have h : Ring.KrullDimLE 1 (𝓞 F) := inferInstance
  refine le_antisymm (by exact_mod_cast Ring.krullDimLE_iff.1 h) ?_
  by_contra hlt
  have : Ring.KrullDimLE 0 (𝓞 F) := Ring.krullDimLE_iff.2 (by
    have h' : ringKrullDim (𝓞 F) ≤ 0 := Order.le_of_lt_succ (not_le.1 hlt)
    exact_mod_cast h')
  exact RingOfIntegers.not_isField F Ring.KrullDimLE.isField_of_isDomain

theorem isArithVar_globalSections : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp (𝓞 F)) (e : ℕ),
    IsArithVar p e → IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 := by
  intro F _ _ X _ p e h
  letI := algebraΓOfHom p
  have hfin : Module.Finite (𝓞 F) (coh (QCoh.structureModule X) 0) :=
    finite_coh_of_isProjOver (R := 𝓞 F) (fun _ => rfl) _ h.isProjOver 0
  have hfinA : Module.Finite (𝓞 F) Γ(X, ⊤) :=
    Module.Finite.equiv ((coh.zeroUnitEquiv X).restrictScalars (𝓞 F))
  have halg : algebraMap (𝓞 F) Γ(X, ⊤) = ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ := RingHom.ext fun c => by
    change p.appTop _ = _
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have hc : CharZero Γ(X, ⊤) := h.charZero
  have hinj : Function.Injective (algebraMap (𝓞 F) Γ(X, ⊤)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hI : (RingHom.ker (algebraMap (𝓞 F) Γ(X, ⊤))).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
      ext n
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot, algebraMap_int_eq, eq_intCast,
        map_intCast, Int.cast_eq_zero]
    have hb := Ideal.eq_bot_of_comap_eq_bot hI
    have hx' : x ∈ RingHom.ker (algebraMap (𝓞 F) Γ(X, ⊤)) := hx
    rw [hb] at hx'
    exact hx'
  have : FaithfulSMul (𝓞 F) Γ(X, ⊤) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hdim : ringKrullDim Γ(X, ⊤) = 1 :=
    (GlobalTheory.ringKrullDim_eq_of_isIntegral (𝓞 F) Γ(X, ⊤)).trans (ringKrullDim_integers F)
  have hfinite : IsFinite (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) :=
    (IsFinite.SpecMap_iff _).2 (halg ▸ RingHom.finite_algebraMap.2 hfinA)
  have hbase : IsProjOver (𝟙 (Sp (𝓞 F))) :=
    (ArithBase.isArithVar_id (k := 𝓞 F) (ringKrullDim_integers F)).isProjOver
  refine ⟨h.isDomain, h.finite, inferInstance, ?_, ?_, ?_⟩
  · simpa using isProjOver_comp_of_isFinite (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) hbase
  · exact (flat_int_iff_charZero _).2
      (((Scheme.ΓSpecIso (.of Γ(X, ⊤))).inv.hom.charZero_iff
        (ConcreteCategory.bijective_of_isIso _).1).1 hc)
  · exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, ⊤)).trans (by rw [hdim]; rfl)

end GlobalTheory.SteinBase
