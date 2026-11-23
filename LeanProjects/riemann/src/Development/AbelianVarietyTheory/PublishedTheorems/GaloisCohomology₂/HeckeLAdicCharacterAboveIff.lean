import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal

namespace GlobalTheory.Published

def HeckeLAdicCharacterAbove : Prop := GlobalTheory.TripleGal.CharAbove

theorem heckeLAdicCharacterAbove_iff : HeckeLAdicCharacterAbove ↔
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
      (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
      (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
      ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
      IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
        GlobalTheory.Pst.Induces Bw →
        IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
        IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
        (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)} :=
  Iff.rfl

end GlobalTheory.Published

namespace GlobalTheory.HeckeGal

theorem IsLAdicOf.eq_of_isGlobalArtin {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {art art' : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    (ha' : IsGlobalArtin art') {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ} {μ μ' : G E Ω →* (Qbar l)ˣ}
    (hμ : Continuous μ) (hμ' : Continuous μ') (h : IsLAdicOf art ι χ n μ) (h' : IsLAdicOf art' ι χ n μ') :
    μ = μ' := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hs := Filter.eventually_cofinite.1 (hl.and (GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ).1)
  refine mul_inv_eq_one.1 (GlobalTheory.FrobDense.eq_one_of_frob E Ω art ha _ (μ * μ'⁻¹) (hμ.mul hμ'.inv) hs.toFinset
    fun v hv A hA σ hσ => ?_)
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  exact Units.ext ((h.frob_unr ha (Or.inl hv.1) hv.2 hA hσ).trans (h'.frob_unr ha' (Or.inl hv.1) hv.2 hA hσ).symm)

end GlobalTheory.HeckeGal

end
