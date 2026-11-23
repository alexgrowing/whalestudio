import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeightCounting.ToClC

theorem norm_le_one_of_mem_OL (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥(Loc.OL K)) :
    ‖((x : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥K.1) : PadicAlgCl l) :=
    (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).2 x.2
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

theorem mem_clC_of_OL (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (y : ↥(Loc.OL K₀)) :
    algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ clC l (Kt l K₀ L) := by
  refine ⟨Subring.le_topologicalClosure _ ⟨((y : ↥K₀.1) : PadicAlgCl l), ?_, rfl⟩, ?_⟩
  · show ((y : ↥K₀.1) : PadicAlgCl l) ∈ Kt l K₀ L
    exact (le_sup_left.trans (le_sup_left : K₀.1 ⊔ L.1 ≤ _)) (y : ↥K₀.1).2
  · change algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ PadicComplexInt l
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← PadicComplex.coe_eq, PadicComplex.valuation_extends, ← NNReal.coe_le_one, PadicAlgCl.valuation_coe]
    exact norm_le_one_of_mem_OL l K₀ y

def toClC (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)) :=
  ((algebraMap (PadicAlgCl l) ℂ_[l]).comp (K₀.1.val.toRingHom.comp (Loc.OL K₀).val.toRingHom)).codRestrict _
    fun y => mem_clC_of_OL l K₀ L y

theorem exists_toClC : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)),
    ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) :=
  fun l _ K₀ L => ⟨toClC l K₀ L, fun _ => rfl⟩

end GlobalTheory.HeightCounting.ToClC
