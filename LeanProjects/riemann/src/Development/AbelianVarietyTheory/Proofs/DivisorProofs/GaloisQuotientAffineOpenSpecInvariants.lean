import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem quot_affine_spec_invariants : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] [Algebra R R'], Base R → FinExt (algebraMap R R') → IsGal (algebraMap R R') → ∀ (G' : Over (Sp R')) (act : Gal (algebraMap R R') → (G'.left ⟶ G'.left)), (∀ σ, act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)) → act 1 = 𝟙 _ → (∀ σ τ, act (σ * τ) = act σ ≫ act τ) → ∀ (H : G'.left.Opens) (hH : ∀ σ, act σ ⁻¹ᵁ H = H) (X : Over (Sp R)) (π : H.toScheme ⟶ X.left), π ≫ X.hom = H.ι ≫ G'.hom ≫ spMap (algebraMap R R') → IsAffineHom π → (∀ σ, (act σ).resLE H H (hH σ).ge ≫ π = π) → (∀ x y : H.toScheme, π x = π y → ∃ σ, act σ (H.ι x) = H.ι y) → (∀ V : X.left.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(H.toScheme, π ⁻¹ᵁ V), (∀ σ (h : π ⁻¹ᵁ V ≤ ((act σ).resLE H H (hH σ).ge) ⁻¹ᵁ (π ⁻¹ᵁ V)), (((act σ).resLE H H (hH σ).ge).appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → ∀ V : X.left.Opens, IsAffineOpen V → ∃ (C' : Type) (_ : CommRing C') (_ : Algebra R C') (_ : Algebra R' C') (_ : IsScalarTower R R' C') (actC : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')) (C : Subalgebra R C') (j : Sp C' ⟶ H.toScheme) (l : Sp C ⟶ X.left), IsOpenImmersion j ∧ IsOpenImmersion l ∧ Set.range l = (V : Set X.left) ∧ IsPullback j (spMap (algebraMap C C')) π l ∧ j ≫ H.ι ≫ G'.hom = spMap (algebraMap R' C') ∧ l ≫ X.hom = spMap (algebraMap R C) ∧ (∀ σ, spMap (actC σ : C' →+* C') ≫ j ≫ H.ι = j ≫ H.ι ≫ act σ) ∧ (∀ σ r, actC σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) ∧ ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := by
  intro R _ _ _ R' _ _ _ _ _ _ _ G' act hact h1 hmul H hH X π hπ hAff hinv _ hsec V hV
  haveI := hAff
  have hU : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π
  let r : Gal (algebraMap R R') → (H.toScheme ⟶ H.toScheme) := fun σ => (act σ).resLE H H (hH σ).ge
  have hrπ : ∀ σ, r σ ≫ π = π := hinv
  have hr : ∀ σ, π ⁻¹ᵁ V ≤ (r σ) ⁻¹ᵁ (π ⁻¹ᵁ V) := fun σ x hx => by
    show x ∈ (r σ ≫ π) ⁻¹ᵁ V
    rw [hrπ σ]; exact hx
  have hrι : ∀ σ, r σ ≫ H.ι = H.ι ≫ act σ := fun σ => Scheme.Hom.resLE_comp_ι _ _
  let a : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ⟶ Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => (r σ).appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (hr σ)
  have key0 : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec = hU.fromSpec ≫ r σ := fun σ =>
    IsAffineOpen.SpecMap_appLE_fromSpec (r σ) hU hU (hr σ)
  have key : ∀ σ, Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι = hU.fromSpec ≫ H.ι ≫ act σ := fun σ => by
    rw [← Category.assoc, key0, Category.assoc, hrι]
  have key_assoc : ∀ σ {Z : Scheme.{0}} (g : G'.left ⟶ Z),
      Spec.map (a σ) ≫ hU.fromSpec ≫ H.ι ≫ g = hU.fromSpec ≫ H.ι ≫ act σ ≫ g := fun σ Z g => by
    simpa only [Category.assoc] using congrArg (· ≫ g) (key σ)
  have a_one : a 1 = 𝟙 _ := by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, h1, Spec.map_id]
    simp
  have a_mul : ∀ σ τ, a (σ * τ) = a τ ≫ a σ := fun σ τ => by
    rw [← Spec.map_inj, ← cancel_mono (hU.fromSpec ≫ H.ι), key, hmul, Spec.map_comp]
    simp only [Category.assoc, key, key_assoc]
  have a_one' : ∀ x, (a 1).hom x = x := fun x => by rw [a_one]; rfl
  have a_mul' : ∀ σ τ x, (a (σ * τ)).hom x = (a σ).hom ((a τ).hom x) := fun σ τ x => by
    rw [a_mul]; rfl
  obtain ⟨φ', hφ'⟩ : ∃ φ' : CommRingCat.of R' ⟶ Γ(H.toScheme, π ⁻¹ᵁ V),
      Spec.map φ' = hU.fromSpec ≫ H.ι ≫ G'.hom := ⟨Spec.preimage _, Spec.map_preimage _⟩
  have semi : ∀ σ, φ' ≫ a σ = CommRingCat.ofHom (Gal.hom σ) ≫ φ' := fun σ => by
    rw [← Spec.map_inj, Spec.map_comp, Spec.map_comp, hφ', key_assoc, hact]
    simp only [Category.assoc]
  have semi' : ∀ σ y, (a σ).hom (φ'.hom y) = φ'.hom (σ.1 y) := fun σ y =>
    congrArg (fun f => f.hom y) (semi σ)
  letI alg' : Algebra R' Γ(H.toScheme, π ⁻¹ᵁ V) := φ'.hom.toAlgebra
  letI algR : Algebra R Γ(H.toScheme, π ⁻¹ᵁ V) := (φ'.hom.comp (algebraMap R R')).toAlgebra
  haveI tow : IsScalarTower R R' Γ(H.toScheme, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have fixR : ∀ σ r, (a σ).hom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r) = algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V) r :=
    fun σ r => by
      show (a σ).hom (φ'.hom (algebraMap R R' r)) = φ'.hom (algebraMap R R' r)
      rw [semi' σ]
      exact congrArg φ'.hom ((show ∀ r, σ.1 (algebraMap R R' r) = algebraMap R R' r from σ.2) r)
  let ah : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    fun σ => { (a σ).hom with commutes' := fixR σ }
  have inv1 : ∀ σ x, (a σ).hom ((a σ⁻¹).hom x) = x := fun σ x => by
    rw [← a_mul', mul_inv_cancel, a_one']
  have inv2 : ∀ σ x, (a σ⁻¹).hom ((a σ).hom x) = x := fun σ x => by
    rw [← a_mul', inv_mul_cancel, a_one']
  let actE : Gal (algebraMap R R') → (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) := fun σ =>
    AlgEquiv.ofAlgHom (ah σ) (ah σ⁻¹) (AlgHom.ext fun x => inv1 σ x) (AlgHom.ext fun x => inv2 σ x)
  let actC : Gal (algebraMap R R') →* (Γ(H.toScheme, π ⁻¹ᵁ V) ≃ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) :=
    { toFun := actE
      map_one' := AlgEquiv.ext fun x => a_one' x
      map_mul' := fun σ τ => AlgEquiv.ext fun x => a_mul' σ τ x }
  have actC_apply : ∀ σ x, actC σ x = (a σ).hom x := fun _ _ => rfl
  let C : Subalgebra R Γ(H.toScheme, π ⁻¹ᵁ V) :=
    ⨅ σ, AlgHom.equalizer (actC σ : Γ(H.toScheme, π ⁻¹ᵁ V) →ₐ[R] Γ(H.toScheme, π ⁻¹ᵁ V)) (AlgHom.id R _)
  have memC : ∀ x, x ∈ C ↔ ∀ σ, actC σ x = x := fun x =>
    Algebra.mem_iInf.trans (forall_congr' fun σ => Iff.rfl)
  have happ : Spec.map (π.app V) ≫ hV.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE]; exact IsAffineOpen.SpecMap_appLE_fromSpec π hV hU le_rfl
  have hmem : ∀ g, (π.app V).hom g ∈ C := by
    intro g; rw [memC]; intro σ
    have e : π.app V ≫ a σ = π.app V := by
      rw [← Spec.map_inj, ← cancel_mono hV.fromSpec, Spec.map_comp]
      simp only [Category.assoc]
      rw [happ, ← Category.assoc, key0, Category.assoc, hrπ]
    exact congrArg (fun f => f.hom g) e
  let ψ : Γ(X.left, V) →+* C := (π.app V).hom.codRestrict C hmem
  have hbij : Function.Bijective ψ := by
    refine ⟨fun x y h => (hsec V).1 (congrArg Subtype.val h), fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨x, hx⟩ := (hsec V).2 y (fun σ _ => (memC y).1 hy σ)
    exact ⟨x, Subtype.ext hx⟩
  let eψ := RingEquiv.ofBijective ψ hbij
  let l : Sp C ⟶ X.left := Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
  have hlr : l.opensRange = V := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]
  have sq : hU.fromSpec ≫ π = spMap (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) ≫ l := by
    rw [← happ]
    show _ = _ ≫ Spec.map eψ.toCommRingCatIso.hom ≫ hV.fromSpec
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hj : hU.fromSpec ≫ H.ι ≫ G'.hom = spMap (algebraMap R' Γ(H.toScheme, π ⁻¹ᵁ V)) := by
    rw [← hφ']; rfl
  have hl : l ≫ X.hom = spMap (algebraMap R C) := by
    obtain ⟨m, hm⟩ : ∃ m : CommRingCat.of R ⟶ CommRingCat.of C, Spec.map m = l ≫ X.hom :=
      ⟨Spec.preimage _, Spec.map_preimage _⟩
    rw [← hm]
    have e : m ≫ CommRingCat.ofHom (algebraMap C Γ(H.toScheme, π ⁻¹ᵁ V)) =
        CommRingCat.ofHom (algebraMap R Γ(H.toScheme, π ⁻¹ᵁ V)) := by
      rw [← Spec.map_inj, Spec.map_comp, hm, ← Category.assoc, ← sq, Category.assoc, hπ]
      have h2 := congrArg (· ≫ spMap (algebraMap R R')) hj
      simp only [Category.assoc] at h2
      rw [h2, ← Spec.map_comp]
      rfl
    congr 1
    ext r
    exact congrArg (fun f => f.hom r) e
  refine ⟨Γ(H.toScheme, π ⁻¹ᵁ V), inferInstance, algR, alg', tow, actC, C, hU.fromSpec, l, inferInstance,
    inferInstance, ?_, ?_, hj, hl, ?_, ?_, memC⟩
  · exact congrArg (fun U : X.left.Opens => (U : Set X.left)) hlr
  · refine (IsOpenImmersion.isPullback _ _ _ _ sq ?_).flip
    rw [hlr, IsAffineOpen.opensRange_fromSpec]
  · intro σ
    exact key σ
  · intro σ y
    exact semi' σ y

end GlobalTheory.Mum
