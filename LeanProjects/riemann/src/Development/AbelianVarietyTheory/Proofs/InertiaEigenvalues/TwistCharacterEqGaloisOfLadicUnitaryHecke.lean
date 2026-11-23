import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.HeckeRead

theorem read_of_isGal_side : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  intro D N T art ha i κ ι hι b embO hO χ hχu S hS H hH n r hr
  classical
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (T.l i)
  refine ⟨hfin.toFinset ∪ S, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hu, y, hy⟩ := hS P hP.2
  have hAt := (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ H (MonoidHom.ext hH) P).1 hu
  have hyC : D.what₂.embLL ((y : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ) := hy
  have hyi : D.what₂.embLL ((y⁻¹ : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [IntermediateField.coe_inv, map_inv₀, hyC]
  refine ⟨_, hAt, y⁻¹, ?_, fun σ hσ => ?_⟩
  · rw [zpow_zero, mul_one]
    exact hyi
  · have hl : ((T.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hP.1
    have hf := hr.frob ha (Or.inl hl) hu (N.plOm.2 P) hσ
    have inj : Function.Injective (fun z : FractionRing (T.O0 i) => ι (κ z)) := ι.injective.comp κ.injective
    have hkey : algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i) =
        (if b then T.emb0 i else T.emb0b i) y⁻¹ := by
      cases b
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ) := by
          have e1 : starRingEnd ℂ (ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i)))) =
              ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn] at e1
          have := congrArg (starRingEnd ℂ) e1
          simpa only [Complex.conj_conj] using this
        have hst : ((y : D.LL0) : D.what₂.LL) = star ((y⁻¹ : D.LL0) : D.what₂.LL) := by
          apply D.what₂.embLL.injective
          rw [D.starLL_cx, hyi, hyC]
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn, Complex.conj_conj]
        show _ = T.emb0b i y⁻¹
        rw [T.restX_coefficientEmbedding_conj i y⁻¹ y hst]
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyC]
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
        show _ = T.emb0 i y⁻¹
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyi]
    rw [hO y⁻¹ _ hkey]
    rfl

end GlobalTheory.HeckeRead

end
