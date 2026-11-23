import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem isCptGen_comp_of_flat_preimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j] [Flat j]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (w : A) (hw : ∀ y : A, y ⤳ w → y = w) :
    IsCptGen (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) := by
  have e : genPt (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) = j w :=
    congrArg j (A.fromSpecResidueField_apply w _)
  refine isCptGen_of_maximal_of_surjective hX _ ?_ ?_
  · rw [e]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap j hy
    rw [hw a ha]
  · unfold Scheme.stalkClosedPointTo
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
      ((A.fromSpecResidueField w ≫ j).stalkMap_surjective _)

theorem eq_genericPoint_of_specializes {A : Type*} [TopologicalSpace A] [T0Space A] {U : Set A}
    (hU : U ∈ irreducibleComponents A) {w : A} (hw : IsGenericPoint w U) (y : A) (hy : y ⤳ w) : y = w := by
  have h1 : U ⊆ closure {y} := by
    rw [← hw.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy)) isClosed_closure
  have h2 : closure {y} ⊆ U := hU.2 isIrreducible_singleton.closure h1
  have h3 : w ⤳ y := hw.specializes (h2 (subset_closure rfl))
  exact (hy.antisymm h3).eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_cptOver_of_flat_preimmersion {O : Type} [CommRing O] {β : O →+* c.F} [IsPreimmersion (spMap β)]
    [Flat (spMap β)] (Y : Model Xo c β) (U : Set (Xo.XF c)) (hU : U ∈ irreducibleComponents (Xo.XF c)) :
    Nonempty (CptOver Y U) := by
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  obtain ⟨w, hw⟩ := QuasiSober.sober hU.1 (isClosed_of_mem_irreducibleComponents U hU)
  let Ω : Type := (Xo.XF c).residueField w
  let ξ₀ : Sp Ω ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField w
  have e : genPt ξ₀ = w := (Xo.XF c).fromSpecResidueField_apply w _
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists Y.X Y.t.G Ω (ξ₀ ≫ Y.j)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act Y.X Y.t.G Ω (ξ₀ ≫ Y.j) V M (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  exact ⟨{
    Ω := Ω
    ξ₀ := ξ₀
    inc := (Spec.preimage (ξ₀ ≫ pullback.snd _ _)).hom
    over_inc := (Spec.map_preimage _).symm
    gen := isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) w
      (eq_genericPoint_of_specializes hU hw)
    closure := fun u => by rw [e]; exact hw.specializes_iff_mem.symm
    V := V
    M := M
    ρ := ρ
    act := hρ }⟩

theorem nonempty_cptOver_of_fraction {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (Y : Model Xo c β) (U : Set (Xo.XF c))
    (hU : U ∈ irreducibleComponents (Xo.XF c)) : Nonempty (CptOver Y U) := by
  letI : Algebra O c.F := β.toAlgebra
  haveI : IsDomain O := hβ.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hfr x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  haveI : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  haveI : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  exact nonempty_cptOver_of_flat_preimmersion Y U hU

end GlobalTheory.CompanionTheory.Ar.Flat
