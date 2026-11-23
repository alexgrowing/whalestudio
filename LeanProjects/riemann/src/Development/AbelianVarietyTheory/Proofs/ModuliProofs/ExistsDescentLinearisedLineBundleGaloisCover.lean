import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentOfIsReduced

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LinDescent

private lemma isOpenImmersion_of_section_of_etale' {X Y : Scheme.{0}} (s : Y ⟶ X) (g : X ⟶ Y)
    [Etale g] (h : s ≫ g = 𝟙 Y) : IsOpenImmersion s := by
  have hP : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion @Etale :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr fun _ _ f hf => by
      have : Etale f := hf
      exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  refine MorphismProperty.of_postcomp (W := @IsOpenImmersion) (W' := @Etale) s g inferInstance ?_
  rw [h]
  infer_instance

private lemma exists_mem_range_lift_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) (p : ↥(pullback π π)) :
    ∃ a, p ∈ Set.range ⇑(pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) :
      X ⟶ pullback π π) := by
  let K := AlgebraicClosure ((pullback π π).residueField p)
  let q : Spec (CommRingCat.of K) ⟶ pullback π π :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑((pullback π π).residueField p) K)) ≫ (pullback π π).fromSpecResidueField p
  obtain ⟨a, ha, -⟩ := h.fibre K (q ≫ pullback.snd π π) (q ≫ pullback.fst π π)
    (by simp only [Category.assoc, pullback.condition])
  let x : ↥(Spec (CommRingCat.of K)) := show PrimeSpectrum K from IsLocalRing.closedPoint K
  refine ⟨a, (q ≫ pullback.snd π π) x, ?_⟩
  have e : (q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X) (by rw [h.inv a, Category.id_comp]) = q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact ha
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  have hq : q x = p := by
    have hx : q x ∈ Set.range ((pullback π π).fromSpecResidueField p) :=
      ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    rw [Scheme.range_fromSpecResidueField] at hx
    exact Set.mem_singleton_iff.mp hx
  calc _ = ((q ≫ pullback.snd π π) ≫ pullback.lift (ρ a) (𝟙 X)
        (by rw [h.inv a, Category.id_comp])) x := (Scheme.Hom.comp_apply _ _ _).symm
    _ = q x := by rw [e]
    _ = p := hq

theorem locTransitive_of_isGaloisCover {X Y : Scheme.{0}} {π : X ⟶ Y} {Ga : Type} [Group Ga]
    {ρ : Ga → (X ⟶ X)} (h : IsGaloisCover Ga ρ π) : LocTransitive ρ π := by
  intro Z g₁ g₂ hg z
  let φ : Z ⟶ pullback π π := pullback.lift g₁ g₂ hg
  obtain ⟨c, hc⟩ := exists_mem_range_lift_of_isGaloisCover h (φ z)
  let gr : X ⟶ pullback π π := pullback.lift (ρ c) (𝟙 X) (by rw [h.inv c, Category.id_comp])
  have : Etale π := h.etale
  have : IsOpenImmersion gr :=
    isOpenImmersion_of_section_of_etale' gr (pullback.snd π π) (pullback.lift_snd _ _ _)
  let U : Z.Opens := φ ⁻¹ᵁ gr.opensRange
  have hr : Set.range (U.ι ≫ φ) ⊆ Set.range gr := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact v.2
  let lw := IsOpenImmersion.lift gr (U.ι ≫ φ) hr
  have hw : lw ≫ gr = U.ι ≫ φ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨c, U.toScheme, U.ι, inferInstance, ⟨z, hc⟩, rfl, ?_⟩
  have h1 : U.ι ≫ g₁ = lw ≫ ρ c := by
    have e := congrArg (· ≫ pullback.fst π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_fst] at e
    exact e.symm
  have h2 : U.ι ≫ g₂ = lw := by
    have e := congrArg (· ≫ pullback.snd π π) hw
    simp only [Category.assoc, gr, φ, pullback.lift_snd, Category.comp_id] at e
    exact e.symm
  rw [h1, h2]

theorem exists_descent_of_isGaloisCover :
    ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (L : LB X), IsGaloisCover Ga ρ π → L.IsLB → ∀ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a)))) → ∃ M : LB Y, M.IsLB ∧ LBIso L (M.pull π) := by
  intro X Y π Ga _ ρ L hG hL u hu hc
  have : Finite Ga := hG.finite
  have : IsFinite π := hG.fin
  have : Etale π := hG.etale
  have : Surjective π := hG.onto
  have hfree : ∀ (k : Type) [Field k] [IsAlgClosed k] (r : Sp k ⟶ X),
      Function.Injective fun c => r ≫ ρ c := by
    intro k _ _ r a b hab
    obtain ⟨d, -, hd⟩ := hG.fibre k r (r ≫ ρ a) (by rw [Category.assoc, hG.inv])
    exact (hd a rfl).trans (hd b hab.symm).symm
  exact exists_descent_of_galois hL hG.one (fun a c => (hG.mul a c).symm) hG.inv
    (locTransitive_of_isGaloisCover hG) hfree hu hc

end GlobalTheory.LinDescent
