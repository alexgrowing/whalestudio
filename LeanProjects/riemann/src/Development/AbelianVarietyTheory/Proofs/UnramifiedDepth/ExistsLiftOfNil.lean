import Mathlib
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothNilLift

theorem exists_lift_of_nil {R A W K : Type} [CommRing R] [CommRing A] [CommRing W] [CommRing K]
    [Algebra R A] [Algebra R W] [Algebra R K] [Algebra.Smooth R A] (ρ : W →ₐ[R] K)
    (hρ : Function.Surjective ρ) (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (φ : A →ₐ[R] K) :
    ∃ ψ : A →ₐ[R] W, ρ.comp ψ = φ := by
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := A)
  choose w hw using fun i : Fin n => hρ (φ (f (MvPolynomial.X i)))
  let g : MvPolynomial (Fin n) R →ₐ[R] W := MvPolynomial.aeval w
  have hg : ρ.comp g = φ.comp f := by
    ext i
    simp [g, hw]
  have hg' : ∀ p, ρ (g p) = φ (f p) := fun p => AlgHom.congr_fun hg p
  let J : Ideal W := (RingHom.ker f.toRingHom).map g.toRingHom
  have hJ : J ≤ RingHom.ker ρ := by
    refine Ideal.map_le_iff_le_comap.mpr fun p hp => ?_
    have hp' : f p = 0 := hp
    change ρ (g p) = 0
    rw [hg', hp', map_zero]
  have hJfg : J.FG := hker.map _
  have hJn : IsNilpotent J :=
    (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).mpr fun a ha => hn a (hJ ha)
  let g₀ : (MvPolynomial (Fin n) R ⧸ RingHom.ker f) →ₐ[R] W ⧸ J :=
    Ideal.Quotient.liftₐ (RingHom.ker f) ((Ideal.Quotient.mkₐ R J).comp g) fun p hp =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem g.toRingHom hp)
  let E := Ideal.quotientKerAlgEquivOfSurjective hf
  let ψ₀ : A →ₐ[R] W ⧸ J := g₀.comp E.symm.toAlgHom
  have hψ₀ : ∀ p, ψ₀ (f p) = Ideal.Quotient.mk J (g p) := by
    intro p
    have h1 : E.symm (f p) = Ideal.Quotient.mk _ p := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change g₀ (E.symm (f p)) = _
    rw [h1]
    rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.exists_lift J hJn ψ₀
  refine ⟨ψ, AlgHom.ext fun a => ?_⟩
  obtain ⟨p, rfl⟩ := hf a
  have h2 : Ideal.Quotient.mk J (ψ (f p)) = Ideal.Quotient.mk J (g p) :=
    (AlgHom.congr_fun hψ (f p)).trans (hψ₀ p)
  have h3 : ρ (ψ (f p) - g p) = 0 := hJ (Ideal.Quotient.eq.mp h2)
  rw [map_sub, sub_eq_zero] at h3
  change ρ (ψ (f p)) = _
  rw [h3, hg']

theorem exists_point_lift {R₀ : Type} [CommRing R₀] (X : Over (Spec (CommRingCat.of R₀)))
    [Smooth X.hom] {W K : Type} [CommRing W] [CommRing K] [Algebra R₀ W] [Algebra R₀ K]
    [IsLocalRing K] (ρ : W →ₐ[R₀] K) (hρ : Function.Surjective ρ)
    (hn : ∀ a ∈ RingHom.ker ρ, IsNilpotent a) (z : sp (R₀ := R₀) K ⟶ X) :
    ∃ y : sp (R₀ := R₀) W ⟶ X, spMap ρ ≫ y = z := by
  let x : Spec (CommRingCat.of K) ⟶ X.left := z.left
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint K))) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum K) ⤳ IsLocalRing.closedPoint K :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum K).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hmem
  let a0 : R₀ →+* Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv ≫ X.hom.appLE ⊤ U le_top).hom
  letI : Algebra R₀ Γ(X.left, U) := a0.toAlgebra
  have hover : hU.fromSpec ≫ X.hom = Spec.map (CommRingCat.ofHom a0) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec X.hom
      (isAffineOpen_top (Spec (CommRingCat.of R₀))) hU (le_top : U ≤ X.hom ⁻¹ᵁ ⊤)
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [← h, CommRingCat.ofHom_hom, Spec.map_comp]
  haveI : Algebra.Smooth R₀ Γ(X.left, U) := by
    have h1 : RingHom.Smooth (X.hom.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Smooth) X.hom inferInstance
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R₀))⟩ ⟨U, hU⟩ le_top
    have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of R₀)).inv.hom :=
      RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of R₀)).symm.commRingCatIsoToRingEquiv.bijective
    exact h2.comp h1
  let φ := x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom
  have hφx : Spec.map φ ≫ hU.fromSpec = x := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
      (isAffineOpen_top (Spec (CommRingCat.of K))) hx
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id, Category.id_comp]
  have hφ : φ.hom.comp a0 = algebraMap R₀ K := by
    have e : Spec.map (CommRingCat.ofHom (φ.hom.comp a0)) =
        Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := by
      calc Spec.map (CommRingCat.ofHom (φ.hom.comp a0))
          = Spec.map φ ≫ Spec.map (CommRingCat.ofHom a0) := by
            rw [← Spec.map_comp]; rfl
        _ = Spec.map φ ≫ hU.fromSpec ≫ X.hom := by rw [hover]
        _ = x ≫ X.hom := by rw [← Category.assoc, hφx]
        _ = Spec.map (CommRingCat.ofHom (algebraMap R₀ K)) := Over.w z
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  let φ' : Γ(X.left, U) →ₐ[R₀] K := ⟨φ.hom, fun r => RingHom.congr_fun hφ r⟩
  obtain ⟨ψ, hψ⟩ := exists_lift_of_nil ρ hρ hn φ'
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec) ?_, ?_⟩
  · simp only [sp, Over.mk_hom]
    rw [Category.assoc, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap
  · apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.fromSpec = x
    rw [← hφx, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    exact AlgHom.congr_fun hψ a

theorem main :
  (∀ {R₀ : Type} [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) →
    (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) →
    Smooth G.hom → ∀ (K W : LAlg R₀) (ρW : LHom W K), IsNilOver ρW → SM B K W ρW) := by
  intro R₀ _ G _ _ B e hb _ hnat hsm K W ρW hρ
  refine ⟨hρ, fun x => ?_⟩
  obtain ⟨y, hy⟩ := exists_point_lift G ρW.1 hρ.1 hρ.2 (e K x)
  obtain ⟨y', rfl⟩ := (hb W).2 y
  exact ⟨y', (hb K).1 (by rw [hnat, hy])⟩

end GlobalTheory.SmoothNilLift
