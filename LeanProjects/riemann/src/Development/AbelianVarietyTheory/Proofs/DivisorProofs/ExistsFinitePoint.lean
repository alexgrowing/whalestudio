import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GCTrait

theorem spMap_comp'' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem map_cycAway_mem {n : ℕ} {L : Type} [Field L] (φ : cycAway n →+* L) (K : Subring L)
    (hz : φ (zetaAway n) ∈ K) (hi : φ ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ ∈ K) (c : cycAway n) : φ c ∈ K := by
  obtain ⟨c, hc⟩ := c
  induction hc using Subring.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz
    · exact hi
  | zero => rw [show (⟨0, _⟩ : cycAway n) = 0 from rfl, map_zero]; exact K.zero_mem
  | one => rw [show (⟨1, _⟩ : cycAway n) = 1 from rfl, map_one]; exact K.one_mem
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, _⟩ : cycAway n) = ⟨x, hx⟩ + ⟨y, hy⟩ from rfl, map_add]; exact K.add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, _⟩ : cycAway n) = -⟨x, hx⟩ from rfl, map_neg]; exact K.neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, _⟩ : cycAway n) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]; exact K.mul_mem ihx ihy

theorem exists_finite_point (n : ℕ) {X : Scheme.{0}} (s : X ⟶ Sp (cycAway n)) [LocallyOfFiniteType s]
    (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (x : Sp K ⟶ X),
      spMap (algebraMap K (PadicAlgCl p)) ≫ x = y := by
  obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
    (x := y (default : PrimeSpectrum (PadicAlgCl p))) trivial
  have hr : Set.range y ⊆ Set.range hU.fromSpec := by
    rintro _ ⟨q, rfl⟩
    rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) q default]
    exact hy
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU.fromSpec y hr)
  obtain ⟨a, ha⟩ := Spec.map_surjective (hU.fromSpec ≫ s)
  have hft : a.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), ha]
    infer_instance
  letI := a.hom.toAlgebra
  obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := cycAway n) (A := Γ(X, U)) (self := hft)
  let S : Set (PadicAlgCl p) := φ.hom '' (T : Set Γ(X, U)) ∪
    {φ.hom (a.hom (zetaAway n)), φ.hom (a.hom ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩)}
  have hSfin : S.Finite := (T.finite_toSet.image _).union (Set.toFinite _)
  haveI : Finite S := hSfin.to_subtype
  let K := IntermediateField.adjoin ℚ_[p] S
  have hK : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hS : S ⊆ K := IntermediateField.subset_adjoin ℚ_[p] S
  have hc : ∀ c : cycAway n, φ.hom (a.hom c) ∈ K.toSubfield.toSubring :=
    map_cycAway_mem (φ.hom.comp a.hom) K.toSubfield.toSubring
      (hS (Or.inr (Or.inl rfl))) (hS (Or.inr (Or.inr rfl)))
  have hmem : ∀ b, φ.hom b ∈ K := fun b => by
    have hb : b ∈ Algebra.adjoin (cycAway n) (T : Set Γ(X, U)) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap c => exact hc c
    | add a b _ _ ha hb => rw [map_add]; exact K.add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
  let φK : Γ(X, U) →+* K := φ.hom.codRestrict K hmem
  refine ⟨K, hK, spMap φK ≫ hU.fromSpec, ?_⟩
  rw [← Category.assoc, spMap_comp'', ← IsOpenImmersion.lift_fac hU.fromSpec y hr, ← hφ]
  rfl

theorem exists_ext_emb (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W) (fK : FractionRing V →+* FractionRing W)
    (hinj : Function.Injective f) (hloc : IsLocalHom f) (hfin : f.Finite)
    (hc : ∀ a, fK (algebraMap V _ a) = algebraMap W _ (f a)) (κ : FractionRing V →+* PadicAlgCl p)
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∃ ι : FractionRing W →+* PadicAlgCl p, ι.comp fK = κ ∧
      ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  letI : Algebra V W := f.toAlgebra
  letI : Algebra (FractionRing V) (FractionRing W) := fK.toAlgebra
  letI : Algebra (FractionRing V) (PadicAlgCl p) := κ.toAlgebra
  haveI : Algebra.IsIntegral V W := ⟨fun w => hfin.to_isIntegral w⟩
  haveI : IsLocalHom (algebraMap V W) := hloc
  have hint : ∀ w : W, IsIntegral (FractionRing V) (algebraMap W (FractionRing W) w) := fun w =>
    IsIntegral.map_of_comp_eq (algebraMap V (FractionRing V)) (algebraMap W (FractionRing W))
      (RingHom.ext fun v => hc v) (Algebra.IsIntegral.isIntegral w)
  haveI : Algebra.IsAlgebraic (FractionRing V) (FractionRing W) := by
    constructor
    intro z
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) z
    rw [div_eq_mul_inv]
    exact ((hint a).mul (hint b).inv).isAlgebraic
  let ι : FractionRing W →ₐ[FractionRing V] PadicAlgCl p := IsAlgClosed.lift
  have hι : ι.toRingHom.comp fK = κ := RingHom.ext fun x => ι.commutes x
  refine ⟨ι.toRingHom, hι, GlobalTheory.unitBall_eq_of_integral_dvr p V W hinj κ ι.toRingHom (fun v => ?_) hV⟩
  show ι (algebraMap W (FractionRing W) (f v)) = _
  rw [← hc]
  exact ι.commutes _

theorem exists_cTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X₁.M.Z), Set.range (gPt p ≫ y ≫ X₁.π) ⊆ Set.range i → ∃ c : CTrait X₁ p (y (cPt p)), c.y = y := by
  intro g n F W Z i X₁ hg hn hodd hi p _ y hr
  let y₁ : Sp (PadicAlgCl p) ⟶ F.X := IsOpenImmersion.lift i (gPt p ≫ y ≫ X₁.π) hr
  have hy₁ : y₁ ≫ i = gPt p ≫ y ≫ X₁.π := IsOpenImmersion.lift_fac _ _ _
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  obtain ⟨K, hK, x, hx⟩ := exists_finite_point n F.s p y₁
  obtain ⟨hdvr, hcomp, hunit⟩ := GlobalTheory.intRing_complete_dvr p K hK
  haveI := hdvr
  haveI : CharZero (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := inferInstance
  let e : FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) ≃ₐ[GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K] K := FractionRing.algEquiv _ K
  let es : K →+* FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := e.symm.toRingEquiv.toRingHom
  have hbase : GlobalTheory.Mum.Base (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K) := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  obtain ⟨T, f, fK, hinj, hloc, hfin, hc, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n (cycAway n) (zetaAway n) F _ hbase hdvr (spMap es ≫ x)
  obtain ⟨ι, hι, hint⟩ := exists_ext_emb p _ T.V f fK hinj hloc hfin hc _ hunit
  have h2 : algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p) =
      (algebraMap K (PadicAlgCl p)).comp e.toRingEquiv.toRingHom := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (RingHom.ext fun v => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply]
    refine (IsFractionRing.lift_algebraMap (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing_injective K) v).trans ?_
    show _ = algebraMap K (PadicAlgCl p) (e (algebraMap _ _ v))
    rw [AlgEquiv.commutes]
    rfl
  have hκ : (algebraMap (FractionRing (GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.intRing K)) (PadicAlgCl p)).comp es = algebraMap K (PadicAlgCl p) := by
    ext k
    rw [h2]
    show algebraMap K (PadicAlgCl p) (e (e.symm k)) = _
    rw [AlgEquiv.apply_symm_apply]
  have key : spMap ι ≫ spMap fK ≫ spMap es = spMap (algebraMap K (PadicAlgCl p)) := by
    rw [spMap_comp'', spMap_comp'', ← RingHom.comp_assoc, hι, hκ]
  refine ⟨⟨y, rfl, T, ι, hint, ?_⟩, rfl⟩
  calc gPt p ≫ y ≫ X₁.π = y₁ ≫ i := hy₁.symm
    _ = (spMap (algebraMap K (PadicAlgCl p)) ≫ x) ≫ i := by rw [hx]
    _ = ((spMap ι ≫ spMap fK ≫ spMap es) ≫ x) ≫ i := by rw [key]
    _ = spMap ι ≫ T.y ≫ i := by rw [hTy]; simp only [Category.assoc]

end GlobalTheory.Poinc.GCTrait
