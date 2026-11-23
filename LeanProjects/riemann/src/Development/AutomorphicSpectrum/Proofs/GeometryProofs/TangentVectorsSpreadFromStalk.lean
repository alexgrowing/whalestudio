import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.VAtVNeBot
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Spread

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (c : A →+* B) (d : B →+* C) :
    spMap (d.comp c) = spMap d ≫ spMap c := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_ringHom {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    (z : Sp B ⟶ X) (hr : Set.range z ⊆ Set.range x) : ∃ a : A →+* B, spMap a ≫ x = z := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift x z hr)).hom, ?_⟩
  change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x z hr)).hom) ≫ x = z
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem ringHom_ext {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (x : Sp A ⟶ X) [IsOpenImmersion x]
    {a b : A →+* B} (h : spMap a ≫ x = spMap b ≫ x) : a = b := by
  have h2 := Spec.map_injective ((cancel_mono x).1 h)
  exact congrArg (fun g => g.hom) h2

theorem exists_frac {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [IsOpenImmersion x] (P : X)
    (hP : P ∈ x.opensRange) (θ : R →+* X.presheaf.stalk P) (hθ : spMap θ ≫ x = X.fromSpecStalk P)
    (a : X.presheaf.stalk P) : ∃ r s : R, IsUnit (θ s) ∧ a * θ s = θ r := by
  have hU : IsAffineOpen x.opensRange := isAffineOpen_opensRange x
  let R₂ : Type := Γ(X, x.opensRange)
  let x₂ : Sp R₂ ⟶ X := hU.fromSpec
  have : IsOpenImmersion x₂ := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  have hrange : Set.range x₂ = Set.range x := by
    change Set.range hU.fromSpec = _
    rw [hU.range_fromSpec]
    rfl
  obtain ⟨φ, hφ⟩ := exists_ringHom x x₂ hrange.le
  obtain ⟨φ', hφ'⟩ := exists_ringHom x₂ x hrange.ge
  have hcomp : φ.comp φ' = RingHom.id R₂ := ringHom_ext x₂ (by
    rw [spMap_comp, Category.assoc, hφ', hφ]
    simp [spMap])
  let g : R₂ →+* X.presheaf.stalk P := (X.presheaf.germ x.opensRange P hP).hom
  have hg : spMap g ≫ x₂ = X.fromSpecStalk P := by
    rw [← IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hP]
    rfl
  have hgφ : g.comp φ = θ := ringHom_ext x (by
    rw [spMap_comp, Category.assoc, hφ, hg, hθ])
  have hgs : ∀ t, θ (φ' t) = g t := fun t => by
    rw [← hgφ]
    exact congrArg g (RingHom.congr_fun hcomp t)
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hP⟩ : x.opensRange)
  haveI := hU.isLocalization_stalk ⟨P, hP⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl a
  refine ⟨φ' r, φ' s, ?_, ?_⟩
  · rw [hgs]
    exact IsLocalization.map_units (X.presheaf.stalk P) (M := (hU.primeIdealOf ⟨P, hP⟩).asIdeal.primeCompl) s
  · rw [hgs, hgs]
    exact hrs

end GlobalTheory.CompanionTheory.Ar.LocFn.Spread

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem exists_chart_spread : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (P : X) (ι : Type) [Finite ι] (e : ι → (epsAt (X.fromSpecStalk P) ⟶ G)) (f : X.presheaf.stalk P), (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G (X.fromSpecStalk P) (e i)) → ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (_ : IsOpenImmersion x) (θ : R →+* X.presheaf.stalk P) (e' : ι → (epsAt x ⟶ G)) (f' : R), P ∈ x.opensRange ∧ spMap θ ≫ x = X.fromSpecStalk P ∧ θ f' = f ∧ (∀ i, GlobalTheory.CompanionTheory.Ar.IsTanAt G x (e' i)) ∧ ∀ i, (e i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e' i).left := by
  intro X G _ _ _ P ι _ e f he
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨R₁, _, x₁, hx₁, F, _, _, MF, n, b, hP⟩ := LieVB.exists_chart G P
  have hP' : (X.fromSpecStalk P) (IsLocalRing.closedPoint (X.presheaf.stalk P)) ∈ x₁.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hP
  obtain ⟨θ₁, hθ₁⟩ := LieVB.exists_lift (A := X.presheaf.stalk P) x₁ (X.fromSpecStalk P) hP'
  obtain ⟨Fs, _, _, ⟨Ms⟩⟩ := lieModel_exists X G (X.presheaf.stalk P) (X.fromSpecStalk P)
  obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (A := X.presheaf.stalk P) θ₁ x₁ (X.fromSpecStalk P) hθ₁ MF Ms b
  choose s hs using fun i => Ms.onto (e i) (he i)
  let c : ι → Fin n → X.presheaf.stalk P := fun i k => B.repr (s i) k
  choose num den hden hfrac using Spread.exists_frac x₁ P hP θ₁ hθ₁
  let h : R₁ := den f * ∏ i, ∏ k, den (c i k)
  have hunit : IsUnit (θ₁ h) := by
    simp only [h, map_mul, map_prod]
    exact (hden f).mul (IsUnit.prod_univ_iff.2 fun i => IsUnit.prod_univ_iff.2 fun k => hden _)
  let R : Type := Localization.Away h
  let θ : R →+* X.presheaf.stalk P := IsLocalization.Away.lift h hunit
  have hθc : θ.comp (algebraMap R₁ R) = θ₁ := IsLocalization.Away.lift_comp h hunit
  let x : Sp R ⟶ X := spMap (algebraMap R₁ R) ≫ x₁
  have hopen : IsOpenImmersion (spMap (algebraMap R₁ R)) :=
    inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R₁ (Localization.Away h)))))
  have hx : IsOpenImmersion x := inferInstance
  have hxθ : spMap θ ≫ x = X.fromSpecStalk P := by
    change spMap θ ≫ spMap (algebraMap R₁ R) ≫ x₁ = _
    rw [← Category.assoc, ← Spread.spMap_comp, hθc, hθ₁]
  have hlift : ∀ a, den a ∣ h → ∃ a' : R, θ a' = a := fun a hd => by
    have hu : IsUnit (algebraMap R₁ R (den a)) :=
      isUnit_of_dvd_unit (map_dvd _ hd) (IsLocalization.Away.algebraMap_isUnit h)
    obtain ⟨u, hu⟩ := hu
    have hθu : θ (algebraMap R₁ R (den a)) = θ₁ (den a) := RingHom.congr_fun hθc _
    refine ⟨algebraMap R₁ R (num a) * (u⁻¹ : Rˣ), ?_⟩
    have h1 : θ ((u⁻¹ : Rˣ) : R) * θ₁ (den a) = 1 := by
      rw [← hθu, ← hu, ← map_mul, Units.inv_mul, map_one]
    have h2 : θ (algebraMap R₁ R (num a)) = θ₁ (num a) := RingHom.congr_fun hθc _
    rw [map_mul, h2, ← hfrac a, mul_assoc, mul_comm (θ₁ (den a)), h1, mul_one]
  have hdvd : ∀ i k, den (c i k) ∣ h := fun i k =>
    Dvd.dvd.mul_left ((Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ k, den (c i k)) (Finset.mem_univ i))) _
  choose c' hc' using fun i k => hlift (c i k) (hdvd i k)
  obtain ⟨f', hf'⟩ := hlift f (Dvd.intro _ rfl)
  obtain ⟨F', _, _, ⟨MR⟩⟩ := lieModel_exists X G R x
  obtain ⟨β₁, B₁, hB₁, hβ₁⟩ := LieVB.basis_tr (algebraMap R₁ R) x₁ x rfl MF MR b
  obtain ⟨j, hj⟩ := LieVB.exists_tr (A := R) (B := X.presheaf.stalk P) x (X.fromSpecStalk P) θ hxθ MR Ms
  have hjB : ∀ k, j (B₁ k) = B k := fun k => LieVB.pt_left_inj Ms (by
    rw [hj, hB₁, hβ₁, ← Category.assoc, LieVB.spMap_dual_comp, hθc, hB, hβ])
  refine ⟨R, inferInstance, x, hx, θ, fun i => MR.pt (∑ k, c' i k • B₁ k), f', ?_, hxθ, hf',
    fun i => MR.tan _, fun i => ?_⟩
  · refine ⟨(spMap θ) (IsLocalRing.closedPoint (X.presheaf.stalk P)), ?_⟩
    rw [← Scheme.Hom.comp_apply, hxθ]
    exact Scheme.fromSpecStalk_closedPoint
  · have hsum : j (∑ k, c' i k • B₁ k) = s i := by
      rw [map_sum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (B.sum_repr (s i))
      rw [j.map_smulₛₗ, hc', hjB]
    rw [← hj, hsum, hs]

end GlobalTheory.CompanionTheory.Ar.LocFn
