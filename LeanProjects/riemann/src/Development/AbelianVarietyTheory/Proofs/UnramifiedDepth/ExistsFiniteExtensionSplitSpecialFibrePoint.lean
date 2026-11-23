import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitPoint

theorem exists_extend {V W Ω : Type} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [Field Ω] [IsAlgClosed Ω] (β : V →+* Ω) (hβ : ∀ a ∈ maximalIdeal V, β a = 0) :
    ∃ β' : W →+* Ω, β'.comp (algebraMap V W) = β ∧ ∀ a ∈ maximalIdeal W, β' a = 0 := by
  have hm : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := V) _)
  have : IsLocalHom (algebraMap V W) := ((IsLocalRing.local_hom_TFAE (algebraMap V W)).out 4 0).1 hm
  have : IsLocalHom β := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (hβ a h)⟩
  let : Algebra (ResidueField V) Ω := (ResidueField.lift β).toAlgebra
  have : Algebra.IsIntegral V (ResidueField W) :=
    ⟨fun x => by
      obtain ⟨y, rfl⟩ := residue_surjective x
      exact (Algebra.IsIntegral.isIntegral (R := V) y).map (IsScalarTower.toAlgHom V W (ResidueField W))⟩
  have : Algebra.IsIntegral (ResidueField V) (ResidueField W) := Algebra.IsIntegral.tower_top V
  let g : ResidueField W →ₐ[ResidueField V] Ω := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp (residue W), RingHom.ext fun a => ?_, fun a ha => ?_⟩
  · exact g.commutes (residue V a)
  · show g (residue W a) = 0
    rw [(residue_eq_zero_iff a).2 ha, map_zero]

theorem polAt_pullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {j : Sp K ⟶ S} (hp : GlobalTheory.LN.PolAt t j) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K)
    (h : j' ≫ f = g ≫ j) : GlobalTheory.LN.PolAt t' j' := by
  have hN := pull_isLB t'.PP.isLB (pullback.fst t'.G.hom j')
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom j)
  obtain ⟨φ, hφ, e, -⟩ := GlobalTheory.Ex.UnifModel.exists_cancel (g := g) (f := j)
    (((isGrpPullback_pullback t'.G j').comp m.cart).congr h rfl) (isGrpPullback_pullback t.G j) t.PP.isLB hM hN
    (GlobalTheory.Ex.UnifModel.iso_pull (GlobalTheory.Ex.UnifModel.iso_of_map m) _ rfl) ⟨Out.CubePf.idIsoL _, Out.CubePf.idIsoL_isGen hM⟩
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) hφ.1 hp.1,
    amplePt _ _ g _ _ φ hφ _ _ hM hN e hp.2.1 hp.2.2⟩

theorem exists_split_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ t : SAB H (Sp V), GlobalTheory.LN.PolAt t (Out.jK V) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : V →+* Ω), (∀ a ∈ maximalIdeal V, β a = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (f : V →+* W) (β' : W →+* Ω) (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap f)), GlobalTheory.LN.CDvr W ∧ β'.comp f = β ∧ (∀ a ∈ maximalIdeal W, β' a = 0) ∧ GlobalTheory.LN.PolAt t' (Out.jK W) ∧ GlobalTheory.LN.SplitOver t'.G (maximalIdeal W) := by
  intro E _ _ _ H V _ _ _ ⟨d, hc, h0⟩ t hp Ω _ _ β hβ
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, dW, cW, fW, hsp⟩ := GlobalTheory.Ex.UnifModel.exists_split V F t.G t.semi
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap V W)) t
  obtain ⟨β', h₁, h₂⟩ := exists_extend (W := W) β hβ
  have i : Function.Injective (algebraMap V W) := fun _ _ h =>
    FaithfulSMul.algebraMap_injective V F (congrArg (fun z : W => (z : F)) h)
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W _).comp i
  let gm : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, β', _, m,
    ⟨dW, cW, charZero_of_injective_algebraMap i⟩, h₁, h₂, polAt_pullback m hp _ (spMap gm) ?_, hsp⟩
  exact (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
    (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm

end GlobalTheory.SplitPoint
