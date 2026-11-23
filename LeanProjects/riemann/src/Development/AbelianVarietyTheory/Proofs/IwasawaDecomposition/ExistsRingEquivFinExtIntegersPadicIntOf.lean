import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.IntOfFinExt

theorem mem_integer_iff_norm_le_one (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) :
    x ∈ (PadicAlgCl.valued l).v.integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  show ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem mem_intOf_iff (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (x : PadicAlgCl l) : x ∈ intOf l K ↔ x ∈ K ∧ ‖x‖ ≤ 1 := by
  unfold intOf
  rw [Subring.mem_inf, mem_integer_iff_norm_le_one]
  rfl

def toIntOf (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) : ↥(Loc.OL K) →+* ↥(intOf l K.1) :=
  RingHom.codRestrict ((K.1.val.toRingHom).comp (Loc.OL K).val.toRingHom) (intOf l K.1)
    (fun y => (mem_intOf_iff l K.1 _).2
      ⟨((y : ↥K.1)).2, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (y : ↥K.1)).1 y.2⟩)

theorem toIntOf_bijective (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) :
    Function.Bijective (toIntOf l K) := by
  constructor
  · intro a b h
    have h' : (((a : ↥K.1) : PadicAlgCl l)) = ((b : ↥K.1) : PadicAlgCl l) :=
      congrArg (fun w : ↥(intOf l K.1) => (w : PadicAlgCl l)) h
    exact Subtype.ext (Subtype.ext h')
  · intro z
    obtain ⟨hK, hn⟩ := (mem_intOf_iff l K.1 z).1 z.2
    refine ⟨⟨⟨(z : PadicAlgCl l), hK⟩,
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K ⟨(z : PadicAlgCl l), hK⟩).2 hn⟩, ?_⟩
    exact Subtype.ext rfl

theorem exists_ringEquiv_intOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l),
    ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) :=
  fun l _ K => ⟨RingEquiv.ofBijective (toIntOf l K) (toIntOf_bijective l K), fun _ => rfl⟩

end GlobalTheory.IntOfFinExt
