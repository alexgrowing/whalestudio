import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterThird
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont F Ω l

private theorem mem_plus {F₀ F : Type} [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Algebra F₀ F]
    [IsTotallyReal F₀] (x : F₀) : algebraMap F₀ F x ∈ maximalRealSubfield F := by
  rw [mem_maximalRealSubfield_iff]
  intro φ
  exact DFunLike.congr_fun
    (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F₀ F)))) x

theorem UpperTheory.cyclotomicCharacter_plusPart :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.CycConj → UpperTheory.V.Af.Sol.ToPolC := by
  intro hA hC F Ω _ _ _ _ _ _ l _ ι n r hpol
  obtain ⟨F₀, _, _, _, _, _, _, hR, μ, c, P, hμ, hs, ⟨j, hj⟩, hp⟩ := hpol
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  letI : Algebra F₀ (maximalRealSubfield F) :=
    ((algebraMap F₀ F).codRestrict (maximalRealSubfield F) mem_plus).toAlgebra
  haveI : IsScalarTower F₀ (maximalRealSubfield F) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    IsScalarTower.algebraMap_apply F₀ F Ω x
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hcyc : IsAlgChar ι (cycBar (maximalRealSubfield F) Ω l ^ ((n : ℤ) - 1)) := by
    refine (hA (maximalRealSubfield F) Ω l ι).1 _ ((cyc_cont _ Ω l).zpow _) fun w _ => ?_
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hA, (n : ℤ) - 1, 1, one_pos, fun s _ => ?_⟩
    rw [pow_one, MonoidHom.zpow_apply, zpow_neg, mul_inv_cancel]
  have hres := (hA F₀ Ω l ι).2.2 (maximalRealSubfield F) μ hμ
  obtain ⟨χ, hc, art, a, h1, h2, h3⟩ := ((hA (maximalRealSubfield F) Ω l ι).2.1 _ _ hcyc hres).1
  refine ⟨_, χ, c', P, ⟨hc, art, a, h1, h2, h3⟩, fun d d' hd hd' => ?_, ⟨j, hj⟩, fun s s' hss => ?_⟩
  · simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply]
    rw [hC _ Ω l d hd, hC _ Ω l d' hd', hs (resG F₀ _ Ω d) (resG F₀ _ Ω d') hd hd']
  · rw [hp s s' (AlgEquiv.ext fun x => DFunLike.congr_fun hss x)]
    congr 2
    change μ (resG F₀ F Ω s) = cycBar F Ω l s ^ (1 - (n : ℤ)) * (cycBar F Ω l s ^ ((n : ℤ) - 1) * μ (resG F₀ F Ω s))
    rw [← mul_assoc, ← zpow_add]
    simp
