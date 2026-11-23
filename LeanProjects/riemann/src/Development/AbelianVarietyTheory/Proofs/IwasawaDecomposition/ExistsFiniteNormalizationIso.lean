import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ProjBlowup

theorem exists_normal_model_ringOfIntegers : ∀ (K : Type) [Field K] [NumberField K] (X : Scheme.{0}) (s : X ⟶ Sp (𝓞 K))
    (V : X.Opens), IsProjOver s →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.toScheme → Flat (V.ι ≫ s) →
    ∃ (N : Scheme.{0}) (ν : N ⟶ X), IsFinite ν ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N ∧ IsProjOver (ν ≫ s) ∧
      Flat (ν ≫ s) ∧ IsIso (ν ∣_ V) ∧ Dense ((ν ⁻¹ᵁ V : N.Opens) : Set N) := by
  intro K _ _ X s V hs hV hflat
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str (𝓞 K) n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have hN : GlobalTheory.IsNormalScheme V.toScheme := .of_pred hV
  have hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType (o := .of (𝓞 K)) V.ι s
      fun x hx => GlobalTheory.GraphClosure.charZero_residueField_of_flat (V.ι ≫ s) hx
  have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
  have : Flat (V.ι.toNormalization ≫ V.ι.fromNormalization ≫ s) := by simpa
  refine ⟨_, V.ι.fromNormalization, hfin, IsNormalScheme.pred _, isProjOver_comp_of_isFinite _ hs,
    flat_normalization V.ι _, ?_, ?_⟩
  · have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  · refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2

end GlobalTheory.ProjBlowup
