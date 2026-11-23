import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory

theorem restrict_torus_smul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t')
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    ∀ (a : 𝓞 E) (x : P.D.toPre.X), ρ (a • x) = a • ρ x := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hj _ h₀j
  letI := H.starRing
  have key : ∀ a : 𝓞 E, j ≫ tV.act.act a =
      SplitTorus.torusMap _ (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)) ≫ j := by
    intro a
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated tV.G.hom := tV.semi.separated
    have : Flat (splitTorusAff ZU P'.D.toPre.X).hom :=
      (ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp V) P'.D.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine ExtUnique.over_hom_ext_of_isPullback (SplitTorus.isPullback_bcMap (spMap α) _) ?_
    have e1 := TorusPart.pullTorus_comp n.cart n.cart (tV.act.act a) (tΩ.act.act a) (n.act a) j
    have e2 := TorusPart.pullTorus_torusMap_comp n.cart j
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a))
    have e3 := TorusPart.PELUnif.torus_comp_act P' hβ n' a
    rw [hj, e3] at e1
    rw [hj] at e2
    rw [← TorusPart.pullTorus_left n.cart, ← TorusPart.pullTorus_left n.cart, e1, e2]
  have hmono := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R (maximalIdeal R) t P (ResidueField V) ((residue V).comp ψ) 0
    (TorusPart.map_pow_one_eq_zero h₀) t₀.G m₀'.φ m₀'.cart).1
  have key2 : ∀ a : 𝓞 E, ρ.comp (DistribSMul.toAddMonoidHom P.D.toPre.X (H.bar a)) =
      (DistribSMul.toAddMonoidHom P'.D.toPre.X (H.bar a)).comp ρ := by
    intro a
    have e := congrArg (TorusPart.pullTorus m₀.cart) (key a)
    rw [TorusPart.pullTorus_comp m₀.cart m₀.cart (tV.act.act a) (t₀.act.act a) (m₀.act a) j,
      TorusPart.pullTorus_torusMap_comp m₀.cart j, h₀j, Category.assoc,
      TorusPart.PELUnif.torus_comp_act P h₀ m₀' a, ← Category.assoc, ← Category.assoc,
      ← SplitTorus.torusMap_comp, ← SplitTorus.torusMap_comp] at e
    haveI : Mono (TorusPart.PELUnif.torus P h₀ m₀') := hmono
    have : Nonempty (Sp (ResidueField V)) := inferInstance
    exact SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro a x
  have k := DFunLike.congr_fun (key2 (H.bar a)) x
  rw [show H.bar (H.bar a) = a from star_star a] at k
  exact k

end GlobalTheory
