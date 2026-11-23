import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ResidueCard

theorem card_ringHom_eq {X Z : Scheme.{0}} (i : Z ⟶ X) [IsPreimmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem card_emb (F L : Type) [Field F] [NumberField F] [Field L] [Algebra F L] [Module.Finite F L] :
    Nat.card (L →+* ℂ) = Module.finrank ℚ F * Nat.card (L →ₐ[F] AlgebraicClosure F) := by
  haveI : NumberField L := NumberField.of_module_finite F L
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AlgHom.card, NumberField.Embeddings.card,
    Module.finrank_mul_finrank]

theorem card_parity_sign_length_of_eq {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nat.card (X.residueField x →+* ℂ) = Module.finrank ℚ F *
      Nat.card {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite F (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[F] AlgebraicClosure F) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s =
        spMap (algebraMap F (AlgebraicClosure F)) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[F] AlgebraicClosure F) →
      {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      ExtConj.below_comp x _⟩
  have hb : Function.Bijective P := by
    refine ⟨fun a b h => ?_, ?_⟩
    · have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.fromSpecResidueField x =
          Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨ψ, h⟩ := ExtConj.factor y x hyx
      have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) := by
        rw [Spec.map_comp, hφ, ← Category.assoc, h]
        exact hy
      have h3 := Spec.map_injective h2
      exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩
  rw [card_emb F (X.residueField x), Nat.card_congr (Equiv.ofBijective P hb)]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  intro F _ _ Y M x hx
  have h1 : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion M.j := MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip h1
  rw [card_ringHom_eq]
  exact card_parity_sign_length_of_eq Y.str x hx

end GlobalTheory.TrueGeo.ResidueCard
