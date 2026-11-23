import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.BrMain
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private lemma galOf_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (a b : E ≃ₐ[F] E) (y : B) :
    PositivityTheory.Rg.Tf.Geo.galOf e (a * b) y = PositivityTheory.Rg.Tf.Geo.galOf e a (PositivityTheory.Rg.Tf.Geo.galOf e b y) := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((a * b : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z =
        Algebra.TensorProduct.map (a : E →ₐ[F] E) (AlgHom.id F A)
          (Algebra.TensorProduct.map (b : E →ₐ[F] E) (AlgHom.id F A) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add, hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : TensorProduct F E A ≃ₐ[E] B)
    (y : B) : PositivityTheory.Rg.Tf.Geo.galOf e (1 : E ≃ₐ[F] E) y = y := by
  have h : ∀ z : TensorProduct F E A,
      Algebra.TensorProduct.map ((1 : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F A) z = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x c => simp
    | add x c hx hc => simp only [map_add, hx, hc]
  simp [PositivityTheory.Rg.Tf.Geo.galOf, h]

private lemma galFin_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a b : E ≃ₐ[F] E) (v : Pl F) (y : CompletionsOver E v) :
    galFin (a * b) v y = galFin a v (galFin b v y) := galOf_mul' _ a b y

private lemma galFin_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : Pl F) (y : CompletionsOver E v) : galFin (1 : E ≃ₐ[F] E) v y = y := galOf_one' _ y

theorem globOf : GlobOf := by
  intro F E _ _ _ _ _ _ hp v w hw
  have hs := sum_finrank_eq E v
  rw [Fintype.sum_eq_single w (fun w' h => (h (hw w')).elim)] at hs
  intro alg hcomp
  have hdeg : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1)
      = Module.finrank F E := by
    convert hs using 2
    congr 1
    first
    | exact Algebra.algebra_ext _ _ (fun x => (hcomp x).symm)
    | exact Algebra.algebra_ext _ _ (fun x => hcomp x)
  have hp2 := hp.two_le
  haveI : FiniteDimensional (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) :=
    Module.finite_of_finrank_pos (by omega)
  let ψ : CompletionsOver E v ≃+* HeightOneSpectrum.adicCompletion E w.1 :=
    RingEquiv.ofBijective (Pi.evalRingHom (fun w' : PlacesOver E v => HeightOneSpectrum.adicCompletion E w'.1) w)
      ⟨fun y₁ y₂ h => funext fun w' => by
          obtain rfl := hw w'
          exact h,
        fun z => ⟨fun w' => by
          rw [hw w']
          exact z, rfl⟩⟩
  have hx : ∀ (σ : Gal(E/F)) (x : E),
      galFin σ v (algebraMap E (CompletionsOver E v) x) = algebraMap E (CompletionsOver E v) (σ x) := by
    intro σ x
    have e1 : ∀ z : E, algebraMap E (CompletionsOver E v) z =
        tensorEquiv' E v (z ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v)) := by
      intro z
      rw [tensorEquiv'_tmul, map_one, mul_one]
    rw [e1, e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v (x ⊗ₜ[F] (1 : HeightOneSpectrum.adicCompletion F v))))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have halg : ∀ (σ : Gal(E/F)) (r : HeightOneSpectrum.adicCompletion F v),
      galFin σ v (algebraMap _ (CompletionsOver E v) r) = algebraMap _ (CompletionsOver E v) r := by
    intro σ r
    have e1 : algebraMap _ (CompletionsOver E v) r = tensorEquiv' E v ((1 : E) ⊗ₜ[F] r) := by
      rw [tensorEquiv'_tmul, map_one, one_mul]
    rw [e1]
    show tensorEquiv' E v (Algebra.TensorProduct.map ((σ : E ≃ₐ[F] E) : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 : E) ⊗ₜ[F] r)))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hψalg : ∀ r : HeightOneSpectrum.adicCompletion F v,
      ψ.symm (algebraMap _ (HeightOneSpectrum.adicCompletion E w.1) r) = algebraMap _ (CompletionsOver E v) r := by
    intro r
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply]
    exact (hcomp r).symm
  let φ : Gal(E/F) →* Gal(HeightOneSpectrum.adicCompletion E w.1/HeightOneSpectrum.adicCompletion F v) :=
    { toFun := fun σ =>
        { toFun := fun z => ψ (galFin σ v (ψ.symm z))
          invFun := fun z => ψ (galFin σ⁻¹ v (ψ.symm z))
          left_inv := fun z => by
            show ψ (galFin σ⁻¹ v (ψ.symm (ψ (galFin σ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', inv_mul_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          right_inv := fun z => by
            show ψ (galFin σ v (ψ.symm (ψ (galFin σ⁻¹ v (ψ.symm z))))) = z
            rw [RingEquiv.symm_apply_apply, ← galFin_mul', mul_inv_cancel, galFin_one',
              RingEquiv.apply_symm_apply]
          map_mul' := fun a b => by simp only [map_mul]
          map_add' := fun a b => by simp only [map_add]
          commutes' := fun r => by
            show ψ (galFin σ v (ψ.symm (algebraMap _ _ r))) = _
            rw [hψalg, halg]
            exact hcomp r }
      map_one' := by
        apply AlgEquiv.ext
        intro z
        show ψ (galFin 1 v (ψ.symm z)) = z
        rw [galFin_one', RingEquiv.apply_symm_apply]
      map_mul' := by
        intro a b
        apply AlgEquiv.ext
        intro z
        show ψ (galFin (a * b) v (ψ.symm z)) = ψ (galFin a v (ψ.symm (ψ (galFin b v (ψ.symm z)))))
        rw [RingEquiv.symm_apply_apply, galFin_mul'] }
  haveI : Nontrivial (CompletionsOver E v) := ψ.toEquiv.nontrivial
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    apply AlgEquiv.ext
    intro x
    have h1 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) x) := by
      rw [hσ]
      rfl
    have h2 : φ σ (ψ (algebraMap E (CompletionsOver E v) x)) = ψ (algebraMap E (CompletionsOver E v) (σ x)) := by
      show ψ (galFin σ v (ψ.symm (ψ _))) = _
      rw [RingEquiv.symm_apply_apply, hx]
    exact (algebraMap E (CompletionsOver E v)).injective (ψ.injective (h2.symm.trans h1))
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) ?_⟩
    have c1 := AlgEquiv.card_le (F := HeightOneSpectrum.adicCompletion F v)
      (K := HeightOneSpectrum.adicCompletion E w.1)
    have c2 := IsGalois.card_aut_eq_finrank F E
    simp only [Fintype.card_eq_nat_card] at c1 c2 ⊢
    omega
  refine ⟨?_, hdeg, ?_⟩
  · intro hsplit
    have h1 : Module.finrank (HeightOneSpectrum.adicCompletion F v) (HeightOneSpectrum.adicCompletion E w.1) = 1 := by
      rw [finrank_eq_one_iff_of_nonzero' (1 : HeightOneSpectrum.adicCompletion E w.1) one_ne_zero]
      intro z
      obtain ⟨c, hc⟩ := hsplit w z
      exact ⟨c, by rw [Algebra.smul_def, mul_one, ← hcomp, hc]⟩
    omega
  · intro s hs
    obtain ⟨σ, hσ⟩ := hbij.2 s
    refine ⟨σ, ?_, ?_⟩
    · intro τ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hs (φ τ))
      refine Subgroup.mem_zpowers_iff.2 ⟨n, hinj ?_⟩
      rw [map_zpow, hσ, hn]
    · intro y
      rw [← hσ]
      show _ = ψ (galFin σ v (ψ.symm (ψ y)))
      rw [RingEquiv.symm_apply_apply]
      rfl

end UpperTheory.Gal.InertialTypesAlt.L
