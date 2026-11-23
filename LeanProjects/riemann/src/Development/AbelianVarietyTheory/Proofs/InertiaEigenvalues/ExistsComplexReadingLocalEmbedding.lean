import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff

noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ReadEmbEx

theorem exists_read {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)
    (ι : FractionRing O →+* ℂ) :
    ∃ φ : ↥B.LL.1 →+* ℂ, ∀ a : O, φ (B.toLL a) = ι (algebraMap O (FractionRing O) a) := by
  let f : FractionRing O →+* ↥B.LL.1 := IsFractionRing.lift (GlobalTheory.EmbInj.toLL_inj B)
  have hf : ∀ a : O, f (algebraMap O (FractionRing O) a) = B.toLL a := fun a =>
    IsFractionRing.lift_algebraMap _ a
  have hb : Function.Bijective f := by
    refine ⟨f.injective, fun y => ?_⟩
    obtain ⟨n, d, hd, e⟩ := GlobalTheory.EmbInj.exists_frac B y
    have hd' : B.toLL d ≠ 0 := fun h0 => hd (GlobalTheory.EmbInj.toLL_inj B (h0.trans (map_zero _).symm))
    refine ⟨algebraMap O _ n / algebraMap O _ d, ?_⟩
    rw [map_div₀, hf, hf, ← e, mul_div_cancel_left₀ _ hd']
  let e := RingEquiv.ofBijective f hb
  refine ⟨ι.comp e.symm.toRingHom, fun a => ?_⟩
  rw [← hf]
  exact congrArg ι (e.symm_apply_apply _)

theorem exists_readEmb : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  intro D bkP i ι v hv τ
  obtain ⟨φ, hφ⟩ := exists_read (bkP.br i v hv) ι
  let c : D.host.E →+* ↥(bkP.br i v hv).Kw.1 :=
    ((bkP.br i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (bkP.br i v hv).Kw.1 (bkP.br i v hv).j_E
  have h : ReadEmb bkP i ι v hv τ ((φ.comp (AlgHom.toRingHom τ)).comp c) := by
    intro x n d hx
    have := congrArg φ hx.2
    rw [map_mul, hφ, hφ] at this
    exact this
  exact ⟨_, h, fun v' hv' τ' hc x n d hx => h _ n d ((hc x n d).1 hx)⟩

end GlobalTheory.ReadEmbEx

end
