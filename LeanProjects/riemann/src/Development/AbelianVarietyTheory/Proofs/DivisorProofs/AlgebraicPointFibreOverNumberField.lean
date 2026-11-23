import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsExtBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointDefinedOverNumberFieldStatement
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BdFibPoint

open IsLocalRing

theorem exists_extend {A k K : Type} [CommRing A] [IsLocalRing A] [Field k] [Field K] [NumberField K]
    (a : A →+* k) (b : A →+* K) [IsLocalHom a] [IsLocalHom b] (ha : a.Finite) (io : K →+* Qb) :
    ∃ (_ : NumberField k) (io₀ : k →+* Qb), io₀.comp a = io.comp b := by
  let a' : ResidueField A →+* k := ResidueField.lift a
  let b' : ResidueField A →+* K := ResidueField.lift b
  have ea : a'.comp (residue A) = a := ResidueField.lift_comp_residue a
  have eb : b'.comp (residue A) = b := ResidueField.lift_comp_residue b
  have ha' : a'.Finite := RingHom.Finite.of_comp_finite (f := residue A) (by rw [ea]; exact ha)
  haveI : CharZero (ResidueField A) := b'.charZero
  haveI : FiniteDimensional ℚ (ResidueField A) :=
    Module.Finite.of_injective b'.toRatAlgHom.toLinearMap b'.injective
  haveI : NumberField (ResidueField A) := ⟨⟩
  letI : Algebra (ResidueField A) k := a'.toAlgebra
  letI : Algebra (ResidueField A) Qb := (io.comp b').toAlgebra
  haveI : Module.Finite (ResidueField A) k := ha'
  haveI : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let f : k →ₐ[ResidueField A] Qb := IsAlgClosed.lift
  refine ⟨NumberField.of_module_finite (ResidueField A) k, f.toRingHom, ?_⟩
  rw [← ea, ← eb]
  ext x
  exact congrArg _ (f.commutes (residue A x))

theorem exists_through {X : Scheme.{0}} {K R : Type} [Field K] [NumberField K] [CommRing R] [IsLocalRing R]
    (io : K →+* Qb) (w : Sp K ⟶ X) (ξ : Sp R ⟶ X) (h : ξ (closedPoint R) = w (closedPoint K))
    (hf : ((residue R).comp (Scheme.stalkClosedPointTo (R := .of R) ξ).hom).Finite) :
    ∃ (_ : NumberField (ResidueField R)) (io₀ : ResidueField R →+* Qb),
      spMap io₀ ≫ spMap (residue R) ≫ ξ = spMap io ≫ w := by
  let a := Scheme.stalkClosedPointTo (R := .of R) ξ
  let e := X.presheaf.stalkCongr (Inseparable.of_eq h)
  let b := e.hom ≫ Scheme.stalkClosedPointTo (R := .of K) w
  have ha : Spec.map a ≫ X.fromSpecStalk _ = ξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  have hb : Spec.map b ≫ X.fromSpecStalk _ = w := by
    rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom]
    exact (congrArg (_ ≫ ·) (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (Inseparable.of_eq h).ge)).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)
  haveI : IsLocalHom a.hom := Scheme.isLocalHom_stalkClosedPointTo _
  haveI : IsLocalHom ((residue R).comp a.hom) := RingHom.isLocalHom_comp _ _
  haveI : IsLocalHom b.hom := by
    haveI : IsLocalHom e.hom.hom := isLocalHom_of_isIso _
    haveI := Scheme.isLocalHom_stalkClosedPointTo (R := .of K) w
    exact RingHom.isLocalHom_comp _ _
  obtain ⟨hN, io₀, H⟩ := exists_extend ((residue R).comp a.hom) b.hom hf io
  refine ⟨hN, io₀, ?_⟩
  rw [← ha, ← hb, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext H

theorem exists_fibAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) :
    ∃ (φ : Fib (ResidueField R)) (m : CubeMap φ.G t.G), FibAt t (spMap (residue R)) φ m := by
  have h₀ : ∀ a ∈ maximalIdeal R ^ (0 + 1), residue R a = 0 := fun a ha => by
    rw [zero_add, pow_one] at ha
    exact (residue_eq_zero_iff a).2 ha
  have hs : spMap (Ideal.Quotient.lift _ (residue R) h₀) ≫ ReciprocityTheory.ChartRestriction.G.Out.thick R (maximalIdeal R) 0 =
      spMap (residue R) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨φ, m, h₁, h₂, h₃⟩ := SpecialFibreExt.exists_fib P.U.toUnifPre 0 (spMap (Ideal.Quotient.lift _ (residue R) h₀))
  refine ⟨φ, m, h₁.congr hs rfl, h₂.trans hs, ?_⟩
  have key : ∀ (M : RigLB t.G) (c : CubicalStr t.G M), M = t.PP → HEq c t.cub → m.IsPullCubical φ.cub c →
      m.IsPullCubical φ.cub t.cub := by
    rintro M c rfl h h'
    exact eq_of_heq h ▸ h'
  exact key _ _ P.bundle (PelUnifCompare.cubG_heq P) h₃

theorem exists_fibre_at_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (y : Sp Qb ⟶ gen T.Z), y (IsLocalRing.closedPoint Qb) ∈ genBd T.Z → ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb) (y₀ : Sp K₀ ⟶ gen T.Z) (φ : Fib K₀) (m : CubeMap φ.G T.Z.t.G), spMap io₀ ≫ y₀ = y ∧ FibAt T.Z.t (y₀ ≫ genι T.Z) φ m := by
  intro E _ _ _ H Dw l Xo c O _ β Y T y hy
  have := isProper_genStr T.Z
  obtain ⟨K, _, _, io, w, rfl⟩ := GlobalTheory.T.algebraic_point_defined_over_number_field c.F _ (genStr T.Z) inferInstance y
  obtain ⟨k, _, m, d, ξ, t, P, g, hξ, ⟨-, -, hf⟩, -, -, ⟨sm⟩, -⟩ := T.toric _ hy
  have hx : ξ (closedPoint _) = w (closedPoint K) :=
    hξ.trans (congrArg w (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  obtain ⟨hN, io₀, e⟩ := exists_through io w ξ hx hf
  obtain ⟨φ, n, h₁, h₂, h₃⟩ := exists_fibAt t P
  refine ⟨_, _, hN, io₀, spMap (residue _) ≫ ξ, φ, SpecialFibreExt.comp n sm.cm, e, ?_, ?_, ?_⟩
  · exact (h₁.comp sm.cart).congr (Category.assoc _ _ _).symm rfl
  · show n.e ≫ sm.cm.e = _
    rw [h₂, sm.base, Category.assoc]
  · exact pullCubComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl sm.lin h₃

end GlobalTheory.BdFibPoint
