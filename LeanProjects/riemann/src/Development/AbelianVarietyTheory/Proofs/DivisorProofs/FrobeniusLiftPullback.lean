import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfHomPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobCokernelSmulHomPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSubschemeCounitIsoStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MixedLocalChains.PullFrob

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]

theorem exists_fib_lift {B B' : Vert.Model O} (f : Vert.Model.Hom B' B) :
    ∃ f₀ : (fibI p B').subscheme ⟶ (fibI p B).subscheme,
      f₀ ≫ (fibI p B).subschemeι = (fibI p B').subschemeι ≫ f.f := by
  refine ⟨IsClosedImmersion.lift _ _ ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  intro U
  rw [fibI, Scheme.IdealSheafData.ofIdealTop_ideal, Scheme.Hom.ker_apply, Ideal.map_span, Ideal.span_le,
    Set.image_singleton, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast, map_natCast]
  exact GlobalTheory.SS.FrobField.cast_zero (FrobQuot.natCast_eq_zero_fibI p B') _

theorem isFrob_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
    (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (P P' : Pres B),
    IsFrob p P.mod P'.mod → IsFrob p (P.pull f).mod (P'.pull f).mod := by
  intro O _ _ _ p _ B B' f P P' ⟨h, ⟨e⟩⟩
  obtain ⟨f₀, hf₀⟩ := exists_fib_lift p f
  have h' := FrobQuot.natCast_eq_zero_fibI p B'
  refine ⟨h', ⟨?_⟩⟩
  let i := (fibI p B).subschemeι
  let i' := (fibI p B').subschemeι
  let Fr := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h
  let Fr' := GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h'
  haveI : P.E.IsQuasicoherent := P.vb.isQuasicoherent
  haveI : P.E'.IsQuasicoherent := P.vb'.isQuasicoherent
  haveI : P.mod.IsQuasicoherent := by unfold Pres.mod; infer_instance
  let G := (Scheme.Modules.pullback (Fr ≫ i)).obj P.mod
  have eM : (P'.pull f).mod ≅ (Scheme.Modules.pullback f.f).obj ((Scheme.Modules.pushforward i).obj G) :=
    P'.pullModIso f ≪≫ (Scheme.Modules.pullback f.f).mapIso e
  haveI : (P'.pull f).E.IsQuasicoherent := (P'.pull f).vb.isQuasicoherent
  haveI : (P'.pull f).E'.IsQuasicoherent := (P'.pull f).vb'.isQuasicoherent
  haveI : (P'.pull f).mod.IsQuasicoherent := by unfold Pres.mod; infer_instance
  have hk : smulHom (P'.pull f).mod (p : Γ(B'.X, ⊤)) = 0 := by
    have h1 : smulHom ((Scheme.Modules.pullback f.f).obj ((Scheme.Modules.pushforward i).obj G))
        (p : Γ(B'.X, ⊤)) = 0 := by
      have := VB.pullback_map_smulHom (F := (Scheme.Modules.pushforward i).obj G) f.f (p : Γ(B.X, ⊤))
      rw [map_natCast] at this
      rw [← this, smulHom_pushforward, map_natCast, h, smulHom_zero, Functor.map_zero, Functor.map_zero]
    have h2 := smulHom_comp eM.hom (p : Γ(B'.X, ⊤))
    rw [h1, comp_zero] at h2
    exact (cancel_mono eM.hom).1 (h2.trans zero_comp.symm)
  haveI := FrobQuot.isIso_unit_fibI p B' _ hk
  haveI := GlobalTheory.T.ideal_subscheme_counit_iso (fibI p B) G
  have hsq : f₀ ≫ Fr ≫ i = (Fr' ≫ i') ≫ f.f := by
    rw [← Category.assoc, ← GlobalTheory.SS.FrobField.absFrob_nat f₀ p 1 Fact.out h' h, Category.assoc, hf₀,
      Category.assoc]
  refine asIso ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app (P'.pull f).mod) ≪≫
    (Scheme.Modules.pushforward i').mapIso ?_
  exact (Scheme.Modules.pullback i').mapIso eM ≪≫
    (Scheme.Modules.pullbackComp i' f.f).app _ ≪≫
    (Scheme.Modules.pullbackCongr hf₀.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp f₀ i).app _).symm ≪≫
    (Scheme.Modules.pullback f₀).mapIso
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)) ≪≫
    (Scheme.Modules.pullbackComp f₀ (Fr ≫ i)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hsq).app _ ≪≫
    ((Scheme.Modules.pullbackComp (Fr' ≫ i') f.f).app _).symm ≪≫
    (Scheme.Modules.pullback (Fr' ≫ i')).mapIso (P.pullModIso f).symm

end GlobalTheory.MixedLocalChains.PullFrob
