import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoRes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzTw

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

def resMap : IsLocalRing.ResidueField 𝒪[w.adicCompletion E] →+* ZMod g :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E]) (DzIso.redO i hi) fun a ha => by
    rw [← RingHom.mem_ker, DzIso.ker_redO i hi]
    exact ha

theorem norm_unit (u : ℤ_[g]ˣ) : ‖((u : ℤ_[g]) : ℚ_[g])‖ = 1 := by
  rw [← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.1 u.isUnit

theorem exists_liftsChar (χ₀ : (ZMod g)ˣ →* ℂˣ) :
    ∃ χ : (w.adicCompletion E)ˣ →* ℂˣ, IsSmoothChar χ ∧ DiscreteGroups.sglob.DzType.LiftsChar i χ₀ χ := by
  have hne : ((g : ℕ) : w.adicCompletion E) ≠ 0 := fun h => by
    have := DzIso.valuation_natCast_eq_uniformizer i hi
    rw [h, map_zero] at this
    exact uniformizer_ne_zero this.symm
  have hϖ : valuation (w.adicCompletion E) ((Units.mk0 _ hne : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      uniformizer (w.adicCompletion E) := by
    rw [Units.val_mk0]
    exact DzIso.valuation_natCast_eq_uniformizer i hi
  obtain ⟨χ, hl, h1⟩ := GlobalTheory.LocGL.exists_isTameLift (k := w.adicCompletion E)
    (χ₀.comp (Units.map (resMap i hi).toMonoidHom)) hϖ 1
  refine ⟨χ, GlobalTheory.LocGL.isSmoothChar_of_isTame hl.isTame, fun u x hx => ?_, fun x hx => ?_⟩
  · have hv : valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1 := by
      rw [hx]
      refine le_antisymm ((DzIso.valuation_le_iff i hi _).2 (norm_unit i hi u).le) (not_lt.1 fun hlt => ?_)
      have := (DzIso.valuation_lt_iff i hi _).1 hlt
      rw [norm_unit i hi u] at this
      exact lt_irrefl _ this
    obtain ⟨v, hv'⟩ := GlobalTheory.LocGL.valuation_eq_one_iff.1 hv
    have hx' : ((v : 𝒪[w.adicCompletion E]) : w.adicCompletion E) = (x : w.adicCompletion E) :=
      congrArg Units.val hv'
    rw [← hv', hl v]
    show χ₀ _ = χ₀ _
    refine congrArg χ₀ (Units.ext ?_)
    show PadicInt.toZMod (DzIso.toInt i hi (v : 𝒪[w.adicCompletion E])) = PadicInt.toZMod (u : ℤ_[g])
    congr 1
    apply PadicInt.ext
    rw [DzIso.coe_toInt, hx', hx, RingEquiv.symm_apply_apply]
  · have : x = Units.mk0 _ hne := Units.ext (by rw [hx, Units.val_mk0])
    rw [this, h1]

end DiscreteGroups.sglob.DzTw
