import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ g : Sec s U.1 →+* C, spMap g ≫ affPt s U = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x U.2 (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  refine ⟨(x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom, ?_⟩
  change Spec.map (x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫ U.2.fromSpec = x
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_spMap_eq {A C : Type} [CommRing A] [CommRing C] {g g' : A →+* C} (h : spMap g = spMap g') : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eq_of_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] {g g' : Sec s U.1 →+* C} (h : spMap g ≫ affPt s U = spMap g' ≫ affPt s U) : g = g' := by
  have : Mono (affPt s U) := @IsOpenImmersion.mono _ _ _ (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  exact eq_of_spMap_eq ((cancel_mono _).1 h)

theorem red_over (D : Data) : D.i ≫ D.s = D.t := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  rw [ht, hpb.w]

variable {D : Data} (Λ : Lift D)

theorem Lift.isDPMorphism (U : AffOp D.X) (T : Thick D.κ D.t) (φ : (Λ.L.obj U).B →ₐ[D.R] T.B) :
    IsDPMorphism (Λ.L.obj U).δ T.δ (φ : (Λ.L.obj U).B →+* T.B) := by
  have hI : ∀ r ∈ D.I, algebraMap D.R T.B r ∈ T.J := fun r hr ↦ T.dp.1 (Ideal.mem_map_of_mem _ hr)
  refine IsDPMorphism.on_span (S := algebraMap D.R (Λ.L.obj U).B '' D.I) _ _ (Λ.gen U) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simpa using hI r hr
  · rintro n _ ⟨r, hr, rfl⟩
    rw [(Λ.L.obj U).dp.2 r hr]
    simpa using (T.dp.2 (n := n) r hr).symm

theorem Lift.hom_iff (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B) :
    spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔
      ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a := by
  constructor
  · intro h
    let φ : (Λ.L.obj U).B →ₐ[D.R] T.B := y.comp (Λ.e U).symm.toAlgHom
    have hφ : ∀ a, φ (Λ.e U a) = y a := fun a ↦ by simp [φ]
    have hd := Λ.isDPMorphism U T φ
    let φ₀ : (Λ.L.obj U).B₀ →+* T.B₀ := RingHom.liftOfSurjective (Λ.L.obj U).π (Λ.L.obj U).surj
      ⟨T.π.comp (φ : (Λ.L.obj U).B →+* T.B), fun b hb ↦
        (T.ker _).2 (hd.1 (Ideal.mem_map_of_mem _ (((Λ.L.obj U).ker b).1 hb)))⟩
    have hc : ∀ b, φ₀ ((Λ.L.obj U).π b) = T.π (φ b) := fun b ↦
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ b
    refine ⟨⟨φ, φ₀, hc, hd, ?_⟩, hφ⟩
    have := D.mono_i
    rw [← cancel_mono D.i, Category.assoc, ← Λ.pt U, ← h, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ (hc _).trans (congrArg T.π (hφ a))
  · rintro ⟨b, hb⟩
    rw [← b.pt, Category.assoc, ← Λ.pt U, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ ((b.comm _).trans (congrArg T.π (hb a))).symm

theorem Lift.hom_spec : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  intro D Λ
  refine ⟨Λ.hom_iff, fun U T h ↦ ?_, fun U C _ g g' h ↦ eq_of_spMap_affPt _ _ h, ?_⟩
  · obtain ⟨g, hg⟩ := exists_spMap_affPt D.s U.unop _ h
    refine ⟨g, hg, fun r ↦ ?_⟩
    have : spMap (g.comp (algebraMap D.R (Sec D.s U.unop.1))) = spMap (T.π.comp (algebraMap D.R T.B)) := by
      rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, hg, Category.assoc, red_over, T.w]
    exact RingHom.congr_fun (eq_of_spMap_eq this) r
  · obtain ⟨N₀, h⟩ := (isDPNilpotent_iff_exists_isLevel D.κ).1 D.nil
    refine ⟨N₀, fun N hN U ↦ ?_⟩
    have h' : fil D.κ N = ⊥ := eq_bot_iff.2 (le_of_le_of_eq (ExpBij.dpFil_anti D.κ hN) h)
    have := fil_le_map_fil _ _ D.κ _ _ (Λ.L.obj U).δ _ (Λ.L.obj U).dp (Λ.gen U) N
    rw [h', Ideal.map_bot] at this
    exact eq_bot_iff.2 this

end GlobalTheory.PDForm
