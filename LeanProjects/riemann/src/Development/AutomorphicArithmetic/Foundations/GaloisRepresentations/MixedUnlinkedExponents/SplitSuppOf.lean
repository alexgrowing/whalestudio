import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamMixedOf

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
open UpperTheory.Gal.GamX

theorem UpperTheory.Gal.GamX.splitSuppOf :
    UpperTheory.Gal.GamX.SplitSuppOf := by
  unfold UpperTheory.Gal.GamX.SplitSuppOf
  intro hNm hSF hWS hSS K L _ _ _ _ _ _ _ _ hp n hn π P hW v w hw
  haveI : w.1.asIdeal.LiesOver v.asIdeal := w.2
  rcases GlobalTheory.CharLiftStep.cycAt_or_split hp v w.1 with hc | ⟨he, hf⟩
  · exfalso
    refine hw fun u => ?_
    haveI : u.1.asIdeal.LiesOver v.asIdeal := u.2
    have hu : u.1.under (𝓞 K) = v :=
      HeightOneSpectrum.ext (Ideal.LiesOver.over (P := u.1.asIdeal) (p := v.asIdeal)).symm
    obtain ⟨-, -, -, h⟩ := hc
    exact Subtype.ext (h u.1 hu)
  · obtain ⟨hi', hN⟩ := GlobalTheory.CharLiftStep.normU_of_split v w.1 he hf
    set i := RingEquiv.ofBijective _ (GlobalTheory.CharLiftStep.bijective_of_split v w.1 he hf) with hidef
    have hi : Continuous i := GroundTheory.Global.continuous_adicCompletionMap v w.1
    have hcomp : ∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x) :=
      GroundTheory.Global.adicCompletionMap_algebraMap v w.1
    refine ⟨i, hi', hi, hcomp, ?_, ?_⟩
    · rw [hNm K L v w]
      exact MonoidHom.ext fun y => Units.ext (hN y)
    · rintro s s' ⟨τ, hτ, h⟩ ⟨τ', hτ', h'⟩
      haveI : Fact (Module.finrank K L).Prime := ⟨hp⟩
      haveI : IsCyclic (L ≃ₐ[K] L) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K L)
      obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hW' : WeakBC (UpperTheory.CBC.Cusp.cx π).sat (UpperTheory.CBC.Cusp.cx P).sat := hW
      obtain ⟨e, he'⟩ := hSS K L σ hσ hp n hn π P (hWS K L hp n hn π P hW').1 hW' v w.1 i hi hcomp τ τ' hτ hτ'
      have hg : ∀ g : GL (Fin n) (w.1.adicCompletion L),
          Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
        Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
      let φ : Representation.Equiv (τ.ρ.comp (Matrix.GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) τ'.ρ :=
        Representation.Equiv.mk e fun g => LinearMap.ext fun x => by
          simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp]
          exact (he' _ x).trans (congrArg (fun g' => τ'.ρ g' (e x)) (hg g))
      have h2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' h).of_equiv φ
      exact (hSF L n hn P w.1).2.1 s' _ ⟨τ', hτ', h'⟩ ⟨τ', hτ', h2⟩
