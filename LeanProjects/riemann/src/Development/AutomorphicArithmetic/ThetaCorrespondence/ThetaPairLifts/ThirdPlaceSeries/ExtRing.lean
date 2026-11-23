import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.CoefDuty.ExtRing
end GlobalTheory.CoefDuty.ExtRing
end
open GlobalTheory.CoefDuty.ExtRing in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.CoefDuty.ExtRing.ext_ring_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ) (L₀ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → ∃ big₁ : D.what₂.places.Pl → Finset ℂ, ∀ L₁ : LocAll (lay0 D), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → ∃ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) ∧ ∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z' := by
  classical
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ _ big₀ L₀ hB₀
  obtain ⟨Sp₀, ⟨Au₀⟩, -⟩ := hB₀
  have hg := fun i => exists_gens (Sp₀.iq i) (Sp₀.iq_alg i)
  let gens : ∀ i : L₀.X.nd.Loc, Finset (Qbar (L₀.X.nd.l i)) := fun i => Classical.choose (hg i)
  have hgens : ∀ i x, Sp₀.iq i x ∈ Submodule.span ℚ_[L₀.X.nd.l i] (gens i : Set (Qbar (L₀.X.nd.l i))) :=
    fun i => Classical.choose_spec (hg i)
  let big₁ : D.what₂.places.Pl → Finset ℂ := fun w => (Finset.Icc 1 D.R.m).biUnion fun j =>
    (L₀.X.nd.locs j w).biUnion fun i => (gens i).image fun y => qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y
  have hbig : ∀ i y, y ∈ gens i → qCast (L₀.X.nd.w_l i) (A.pl.ι (L₀.X.nd.w i)) y ∈ big₁ (L₀.X.nd.w i) := by
    intro i y hy
    refine Finset.mem_biUnion.2 ⟨L₀.X.nd.j i, Finset.mem_Icc.2 (L₀.X.nd.j_range i), ?_⟩
    exact Finset.mem_biUnion.2 ⟨i, (L₀.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, Finset.mem_image_of_mem _ hy⟩
  refine ⟨big₁, fun L₁ hB₁ i₀ i₁ hw => ?_⟩
  obtain ⟨Sp₁, ⟨Au₁⟩, -⟩ := hB₁
  change L₀.X.nd.w i₀ = L₁.X.nd.w i₁ at hw
  have hl : L₀.X.nd.l i₀ = L₁.X.nd.l i₁ := by
    exact (L₀.X.nd.w_l i₀).symm.trans ((congrArg _ hw).trans (L₁.X.nd.w_l i₁))
  haveI := L₀.X.nd.lPrime i₀
  haveI := L₁.X.nd.lPrime i₁
  have key : ∀ w (_ : L₀.X.nd.w i₀ = w) (h₁ : D.what₂.places.resChar w = L₁.X.nd.l i₁),
      qCast h₁ (A.pl.ι w) = qCast hl (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) := by
    intro w hw' h₁
    subst hw'
    exact qCast_trans _ _ _ _
  obtain ⟨φ, h1, h2⟩ := exists_ringHom (O₀ := L₀.X.nd.O i₀) (O₁ := L₁.X.nd.O i₁)
    (cr₀ := L₀.X.nd.instO i₀) (dm₀ := L₀.X.nd.domO i₀) (dv₀ := L₀.X.nd.dvrO i₀) (al₀ := L₀.X.nd.algO i₀) (fi₀ := L₀.X.nd.finO i₀)
    (cr₁ := L₁.X.nd.instO i₁) (dm₁ := L₁.X.nd.domO i₁) (dv₁ := L₁.X.nd.dvrO i₁) (al₁ := L₁.X.nd.algO i₁) (fi₁ := L₁.X.nd.finO i₁) hl (Sp₀.iq i₀) (Sp₀.iq_alg i₀) (Sp₁.iq i₁) (Sp₁.iq_alg i₁)
    (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁)))
    (key _ hw _) _ (hgens i₀) (fun y hy => Sp₁.iq_big i₁ _ (hw ▸ hbig i₀ y hy))
  refine ⟨φ, fun z => ?_, h2⟩
  have e₀ := fun x => (congrArg (fun g : Qbar (L₀.X.nd.l i₀) ≃+* ℂ => g (L₀.Y.naut.iotaQ i₀ x)) (Au₀.iotaQC i₀)).trans
    (congrArg (qCast (L₀.X.nd.w_l i₀) (A.pl.ι (L₀.X.nd.w i₀))) (DFunLike.congr_fun (Au₀.iotaQ i₀) x))
  have e₁ := fun x => (congrArg (fun g : Qbar (L₁.X.nd.l i₁) ≃+* ℂ => g (L₁.Y.naut.iotaQ i₁ x)) (Au₁.iotaQC i₁)).trans
    (congrArg (qCast (L₁.X.nd.w_l i₁) (A.pl.ι (L₁.X.nd.w i₁))) (DFunLike.congr_fun (Au₁.iotaQ i₁) x))
  exact (e₁ _).trans ((h1 z).trans (e₀ _).symm)
end
