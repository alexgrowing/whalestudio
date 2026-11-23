import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AutomorphicArithmetic.DivisorFrames.ExistsExtPointInvValLtOneOfPoleAtPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem eval_chart {R : Type} [CommRing R] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (ψ : Γ(X, U) →+* R) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U) :
    (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec : Sp R ⟶ X).appLE U ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom ψ := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ ((congrArg _ (Subsingleton.elim _ _)).trans (CategoryTheory.Functor.map_id _ _))).trans
      (Category.comp_id _)
  have e2 := Scheme.ΓSpecIso_naturality (R := Γ(X, U)) (CommRingCat.ofHom ψ)
  have e3 : (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec : Sp R ⟶ X).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ h1 ≫ (Spec.map (CommRingCat.ofHom ψ) : Sp R ⟶ Spec Γ(X, U)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e3, e1, Category.assoc]
  erw [e2]
  exact Iso.inv_hom_id_assoc _ _

private theorem charZero_chart {O : Type} [CommRing O] [IsDomain O] [CharZero O] {X : Scheme.{0}} (q : X ⟶ Sp O)
    [Flat q] {U : X.Opens} (hU : IsAffineOpen U) [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (HorizPt.strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv)) h₁
  let _ : Algebra O Γ(X, U) := (HorizPt.strHom q U).hom.toAlgebra
  have : Module.Flat O Γ(X, U) := h₂
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective O Γ(X, U))

theorem UpperTheory.regular_at_point_extension :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (F' : Type) [Field F'] [NumberField F'] (ε : F →+* F') (O : ValuationSubring F') [IsDiscreteValuationRing O] (b : 𝓞 F →+* O), IsUp v ε O b → ∀ (T : Vert.Model O), GlobalTheory.IsNormalScheme T.X → ∀ (x : T.X), T.str x = closedPoint O → ∀ (V D : T.X.Opens), x ∈ V → genericPoint T.X ∈ D → ∀ f : T.X.functionField, ¬ RegAt x f → ∃ (e : TrueGeo.Ext v) (zt : Sp e.O ⟶ T.X), ⊤ ≤ zt ⁻¹ᵁ V ∧ (spMap e.O.subtype ≫ zt) ≫ T.str ≫ spMap b = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) ∧ below (spMap e.O.subtype ≫ zt) ∈ D ∧ (RegAt (below (spMap e.O.subtype ≫ zt)) f⁻¹ → e.w (valAt (spMap e.O.subtype ≫ zt) f⁻¹) < 1) := by
  intro F _ _ v F' _ _ ε O _ b hup T hN x hx V D hxV hD f hf
  have := T.isProper
  have := T.flat
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hle : U ≤ V := hUV
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(T.X, U) := charZero_chart T.str hU
  let _ : Algebra O Γ(T.X, U) := (HorizPt.strHom T.str U).hom.toAlgebra
  have : Algebra.FiniteType O Γ(T.X, U) :=
    RingHom.FiniteType.comp (T.str.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2)
  haveI := isIntegrallyClosed_sections_of_stalks hN.isIntegrallyClosed_stalk hU
  haveI := functionField_isFractionRing_of_isAffineOpen T.X U hU
  have key : ∀ y : U, RegAt (y : T.X) f ↔ ∃ s c : Γ(T.X, U), algebraMap _ T.X.functionField s * f =
      algebraMap _ T.X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    NormalPole.mem_range_iff (B := T.X.presheaf.stalk (y : T.X)) (hU.primeIdealOf y).asIdeal f
  have hm : ∀ a ∈ maximalIdeal O, algebraMap O Γ(T.X, U) a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    intro a ha
    have e₁ : T.str x = Spec.map (HorizPt.strHom T.str U) (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [← HorizPt.fromSpec_str T.str hU]
      exact congrArg T.str (hU.fromSpec_primeIdealOf ⟨x, hxU⟩).symm
    have ha' : a ∈ (T.str x).asIdeal := by
      rw [hx]
      exact ha
    rw [e₁] at ha'
    exact ha'
  obtain ⟨d, hdD, hd⟩ := hU.exists_basicOpen_le (V := D) ⟨genericPoint T.X, hD⟩ (gen_mem hxU)
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hd
    exact hd
  obtain ⟨c, s, hs, hcs⟩ := IsFractionRing.div_surjective (A := Γ(T.X, U)) f⁻¹
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsc : algebraMap _ T.X.functionField s * f⁻¹ = algebraMap _ T.X.functionField c := by
    rw [← hcs, mul_div_cancel₀ _ (IsFractionRing.to_map_eq_zero_iff.not.mpr hs0)]
  obtain ⟨e, φ, t, h₁, h₂, h₃, h₄⟩ := UpperTheory.exists_ext_point_inv_val_lt_one_of_pole_at_prime F v F' ε O b hup Γ(T.X, U) T.X.functionField
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal (hU.primeIdealOf ⟨x, hxU⟩).isPrime hm f
    (fun s c e => by_contra fun hs => hf ((key ⟨x, hxU⟩).2 ⟨s, c, e, hs⟩)) (d * s) (mul_ne_zero hd0 hs0)
  rw [map_mul] at h₂
  let zt : Sp e.O ⟶ T.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hz : spMap e.O.subtype ≫ zt = Spec.map (CommRingCat.ofHom (e.O.subtype.comp φ)) ≫ hU.fromSpec := by
    simp only [zt]
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hzU : ⊤ ≤ (spMap e.O.subtype ≫ zt) ⁻¹ᵁ U := by
    intro p _
    rw [hz]
    exact (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  have hbU : below (spMap e.O.subtype ≫ zt) ∈ U := hzU trivial
  have hval : ∀ a : Γ(T.X, U), valAt (spMap e.O.subtype ≫ zt) (algebraMap _ T.X.functionField a) =
      (φ a : AlgebraicClosure F) := by
    intro a
    refine (OfModel.valAt_fnOf _ hbU hzU a).trans ?_
    revert hzU
    rw [hz]
    intro hzU
    rw [eval_chart hU _ hzU]
    rfl
  refine ⟨e, zt, ?_, ?_, ?_, fun hr => ?_⟩
  · intro p _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · simp only [zt, Category.assoc]
    rw [← Category.assoc hU.fromSpec, HorizPt.fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  · refine hdD ?_
    change (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))) : Spec Γ(T.X, U)) ∈ hU.fromSpec ⁻¹ᵁ T.X.basicOpen d
    rw [hU.fromSpec_preimage_basicOpen]
    intro h
    have h' : ((φ d : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact left_ne_zero_of_mul h₂ (Subtype.ext h')
  · have hmul := OfModel.valAt_mul (spMap e.O.subtype ≫ zt)
      (f := algebraMap _ T.X.functionField s) (regAt_fnOf hbU (gen_mem hbU) s) hr
    rw [hsc, hval, hval, ← h₄ s c hsc, MulMemClass.coe_mul] at hmul
    have hφ : ((φ s : e.O) : AlgebraicClosure F) ≠ 0 := fun h => right_ne_zero_of_mul h₂ (Subtype.ext h)
    rw [← mul_left_cancel₀ hφ hmul]
    exact h₃
