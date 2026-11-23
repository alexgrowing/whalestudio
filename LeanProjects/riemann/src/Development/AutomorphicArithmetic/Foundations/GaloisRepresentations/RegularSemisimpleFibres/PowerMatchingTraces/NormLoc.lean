import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.SelmerRankBoundLaurent
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.NL

open GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem atFin_galAd (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x => rw [galAd, galOf_tmul, tensor_atFin, tensor_atFin, galFin, galOf_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

private theorem atFin_adeleMap (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem galAd_eq_smul (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : galAd σ a = σ • a := by
  have h1 : (MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ) = Formalism.L2.Host.CT.adMap σ.toRingEquiv :=
    UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv _ (continuous_const_smul σ) fun x => smul_algebraMap σ x
  rw [UpperTheory.ConvolutionTheory.K.galAdEq, ← h1]
  rfl

private theorem atFin_pow_smul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (a : 𝔸[E]) :
    atFin v ((σ ^ i) • a) = (galFin σ v)^[i] (atFin v a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_smul, ← galAd_eq_smul, atFin_galAd, ih, Function.iterate_succ_apply']

private theorem prod_gal [IsGalois F E] {M : Type*} [CommMonoid M] (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (f : (E ≃ₐ[F] E) → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank F E), f (σ ^ i) := by
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf (by simpa [ho] using i.2) (by simpa [ho] using j.2) h)
  have hbij : Function.Bijective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [← Fin.prod_univ_eq_prod_range (fun i => f (σ ^ i))]
  exact (Fintype.prod_bijective _ hbij _ _ fun _ => rfl).symm

private theorem det_iter {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (i : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (θ^[i] δ) : Rˣ) : R) = s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hθ]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]

private theorem det_twNorm {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (l : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (twNorm θ l δ) : Rˣ) : R) =
      ∏ i ∈ Finset.range l, s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [twNorm_succ, map_mul, Units.val_mul, ih, Finset.prod_range_succ, Monoid.End.coe_pow, det_iter s n θ hθ]

end

end UpperTheory.Gal.InertialTypesAlt.G.NL

open UpperTheory.Gal.InertialTypesAlt.G.NL GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc in
open scoped NumberField.AdeleRing in
theorem UpperTheory.Gal.InertialTypesAlt.G.normLoc :
    UpperTheory.Gal.InertialTypesAlt.G.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v γ δ h η hη
  set d : (CompletionsOver E v)ˣ := Matrix.GeneralLinearGroup.det δ with hd
  let du : ∀ u : PlacesOver E v, (u.1.adicCompletion E)ˣ := fun u =>
    Units.map (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) u).toMonoidHom d
  let x : IdeleGroup E := ∏ u : PlacesOver E v, IdeleGroup.finiteEmbedding u.1 (du u)
  have hc : ∀ u : PlacesOver E v, ∃ c : (v.adicCompletion F)ˣ,
      ideleNorm F E (IdeleGroup.finiteEmbedding u.1 (du u)) = IdeleGroup.finiteEmbedding v c := by
    rintro ⟨w, hw⟩
    obtain rfl : below F w = v := (below_eq_iff w v).2 hw
    exact ⟨_, ideleNorm_finiteEmbedding w _⟩
  choose c hc using hc
  have hx : ideleNorm F E x = IdeleGroup.finiteEmbedding v (∏ u, c u) := by
    simp only [x, map_prod, hc]
  have hat : atFin v (x : 𝔸[E]) = (d : CompletionsOver E v) := by
    funext w
    change (((IdeleGroup.finiteProj w.1 x : (w.1.adicCompletion E)ˣ)) : w.1.adicCompletion E) = _
    have : IdeleGroup.finiteProj w.1 x = du w := by
      simp only [x, map_prod]
      rw [Finset.prod_eq_single w (fun b _ hb => IdeleGroup.finiteProj_finiteEmbedding_of_ne
        (fun e => hb (Subtype.ext e.symm)) _) (by simp), IdeleGroup.finiteProj_finiteEmbedding]
    rw [this]
    rfl
  have hy : ∏ u, c u = Matrix.GeneralLinearGroup.det γ := by
    haveI := (GroundTheory.Global.nonempty_placesOver E v)
    apply Units.ext
    apply (incFin E v).injective
    have h1 : incFin E v ((∏ u, c u : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        atFin v (adeleMap F E ((ideleNorm F E x : IdeleGroup F) : 𝔸[F])) := by
      rw [hx, atFin_adeleMap]
      congr 1
      exact (congrArg Units.val (IdeleGroup.finiteProj_finiteEmbedding v _)).symm
    rw [h1, coe_ideleNorm, adeleMap_norm, map_prod, prod_gal σ hσ]
    simp only [atFin_pow_smul, hat]
    rw [hd, ← det_twNorm (galFin σ v) n _ (fun _ => rfl), h]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη x
  rw [hx, hy] at h3
  exact h3
