import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HodgePullHodgePull
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormResFormPullFormPull
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackUnit

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

private theorem formPull_ι_bijective {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V W : Z.Opens) (h : W ≤ V) (a : ℕ) :
    Function.Bijective (formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a) := by
  haveI := isIso_ι_app V W h
  have hsα := semiHom_appSec (s := s) (s' := V.ι ≫ s) (f := V.ι) rfl W
  let α := appSec s (V.ι ≫ s) V.ι W
  let β : Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ W) →+* Sec s W := (inv (V.ι.app W)).hom
  have hαβ : ∀ b, α (β b) = b := fun b => by
    simp only [α, β, appSec]
    exact IsIso.inv_hom_id_apply (V.ι.app W) b
  have hβα : ∀ b, β (α b) = b := fun b => by
    simp only [α, β, appSec]
    exact IsIso.hom_inv_id_apply (V.ι.app W) b
  have hαinj : Function.Injective α := fun x y hxy => by
    rw [← hβα x, ← hβα y, hxy]
  have hsβ : SemiHom (RingHom.id k) β := fun r b => by
    apply hαinj
    rw [hαβ, hsα, hαβ]
    rfl
  have hid₁ : SemiHom (RingHom.id k) (RingHom.id (Sec s W)) := fun r b => rfl
  have hid₂ : SemiHom (RingHom.id k) (RingHom.id (Sec (V.ι ≫ s) (V.ι ⁻¹ᵁ W))) := fun r b => rfl
  have hf : formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a = hsα.mOm a := rfl
  rw [hf, Function.bijective_iff_has_inverse]
  refine ⟨hsβ.mOm a, fun x => ?_, fun y => ?_⟩
  · rw [SemiHom.mOm_mOm hsα hsβ hid₁ hβα x, SemiHom.mOm_id hid₁ (fun _ => rfl)]
  · rw [SemiHom.mOm_mOm hsβ hsα hid₂ hαβ y, SemiHom.mOm_id hid₂ (fun _ => rfl)]

private theorem omegaPull_ι_app_bijective {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V W : Z.Opens) (h : W ≤ V) (hW : IsAffineOpen W) (hW' : IsAffineOpen (V.ι ⁻¹ᵁ W)) (a : ℕ) :
    Function.Bijective ((omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W) := by
  have comm : (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W ∘ toOm s a W =
      toOm (V.ι ≫ s) a (V.ι ⁻¹ᵁ W) ∘ formPull (f := V.ι) (s' := V.ι ≫ s) rfl W a :=
    funext fun x ↦ omegaPull_toOmega (f := V.ι) (s' := V.ι ≫ s) rfl a W x
  have hb : Function.Bijective ((omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a).app W ∘ toOm s a W) := by
    rw [comm]
    exact (toOm_bijective (V.ι ≫ s) a hW').comp (formPull_ι_bijective s V W h a)
  exact (Function.Bijective.of_comp_iff _ (toOm_bijective s a hW)).1 hb

private theorem isIso_restrict_omegaPull {k : Type} [CommRing k] {Z : Scheme.{0}} (s : Z ⟶ Sp k)
    (V : Z.Opens) (a : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a)) := by
  apply GroundTheory.Arith.SchemeCoh.isIso_of_bijective_app_affine
  intro U hU
  have hle : V.ι ''ᵁ U ≤ V := Scheme.Opens.ι_image_le V U
  have hW := hU.image_of_isOpenImmersion V.ι
  have hW' : IsAffineOpen (V.ι ⁻¹ᵁ (V.ι ''ᵁ U)) := by
    rw [Scheme.Hom.preimage_image_eq]
    exact hU
  exact omegaPull_ι_app_bijective s V (V.ι ''ᵁ U) hle hW hW' a

set_option maxHeartbeats 800000 in
theorem UpperTheory.hodgeCohomology_open_restriction_equiv :
    ∀ (Z : Scheme.{0}) (s : Z ⟶ Sp ℂ) (V : Z.Opens) (a b : ℕ), ∃ e : cohOn (Omega s a) V b ≃ hodgeH (V.ι ≫ s) a b, ∀ x : hodgeH s a b, e (cohOn.res ℤ (Omega s a) (le_top : V ≤ ⊤) b x) = hodgePull (f := V.ι) (s' := V.ι ≫ s) rfl a b x := by
  intro Z s V a b
  haveI := isIso_restrict_omegaPull s V a
  let θ : (Omega s a).restrict V.ι ⟶ Omega (V.ι ≫ s) a :=
    (Scheme.Modules.restrictFunctor V.ι).map (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) ≫
      (Scheme.Modules.restrictAdjunction V.ι).counit.app _
  haveI : IsIso θ := by
    dsimp only [θ]
    infer_instance
  have hZ : ∀ r : ℤ, (ConcreteCategory.hom (Scheme.Hom.appTop V.ι)) ((algebraMap ℤ Γ(Z, ⊤)) r) =
      (algebraMap ℤ Γ((V : Scheme), ⊤)) r := fun r => by simp
  have himg : V.ι ''ᵁ ⊤ = V := by simp
  have hmor : (Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a) ≫
      (Scheme.Modules.pushforward V.ι).map θ = omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a := by
    have key := (Scheme.Modules.restrictAdjunction V.ι).unit_naturality
      (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a)
    have tri := (Scheme.Modules.restrictAdjunction V.ι).right_triangle_components (Omega (V.ι ≫ s) a)
    dsimp only [θ]
    rw [Functor.map_comp, ← Category.assoc, key, Category.assoc, tri, Category.comp_id]
  have hle : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ V := by
    simp
  have h1 : ∀ y, cohOn.restrictEquiv ℤ hZ (Omega s a) himg b y =
      cohOn.pull (σ := RingHom.id ℤ) hZ ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) hle b y := by
    intro y
    rfl
  refine ⟨((cohOn.restrictEquiv ℤ hZ (Omega s a) himg b).trans
    (cohOn.mapIso ℤ ⊤ b (asIso θ))).toEquiv, fun (x : cohOn (Omega s a) ⊤ b) => ?_⟩
  have htop : (⊤ : (V : Scheme).Opens) ≤ V.ι ⁻¹ᵁ ⊤ := le_top
  have hA := cohOn.pull_res (G := (Omega s a).restrict V.ι) (σ := RingHom.id ℤ) hZ
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) (le_top : V ≤ ⊤) hle x
  have hB := cohOn.map_pull (G := (Omega s a).restrict V.ι) (σ := RingHom.id ℤ) hZ
    ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a)) θ htop x
  have hC : cohOn.pull (σ := RingHom.id ℤ) hZ ((Scheme.Modules.restrictAdjunction V.ι).unit.app (Omega s a) ≫
      (Scheme.Modules.pushforward V.ι).map θ) htop b x =
      cohOn.pull (σ := RingHom.id ℤ) hZ (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) htop b x :=
    congrArg (fun φ => cohOn.pull (σ := RingHom.id ℤ) hZ φ htop b x) hmor
  have h3 : cohOn.map ℤ θ ⊤ b (cohOn.restrictEquiv ℤ hZ (Omega s a) himg b
      (cohOn.res ℤ (Omega s a) (le_top : V ≤ ⊤) b x)) =
      cohOn.pull (σ := RingHom.id ℤ) hZ (omegaPull (f := V.ι) (s' := V.ι ≫ s) rfl a) htop b x :=
    (congrArg (cohOn.map ℤ θ ⊤ b) ((h1 _).trans hA)).trans (hB.trans hC)
  exact h3
