import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowSubNsmulMemAugIdealSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalSequenceContinuityAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNotMemSmulEqZeroOfSubmodule
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FiniteKilled

variable {S' : Scheme.{0}} {A B : CommRingCat.{0}} (jU : Spec A ⟶ S') {Z : Over S'}
  (jW : Spec B ⟶ Z.left) (φ : A ⟶ B)

def tst {R : CommRingCat.{0}} (χ : A ⟶ R) : Over S' := Over.mk (Spec.map χ ≫ jU)

def tmap {R R' : CommRingCat.{0}} {χ : A ⟶ R} {χ' : A ⟶ R'} (σ : R ⟶ R') (h : χ ≫ σ = χ') :
    tst jU χ' ⟶ tst jU χ :=
  Over.homMk (Spec.map σ) (by simp [tst, ← h, Spec.map_comp])

variable {jU jW φ}

def pt (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R : CommRingCat.{0}} {χ : A ⟶ R} (ψ : B ⟶ R)
    (h : φ ≫ ψ = χ) : tst jU χ ⟶ Z :=
  Over.homMk (Spec.map ψ ≫ jW) (by
    simp only [tst, Over.mk_hom, Category.assoc, ← hc, ← Spec.map_comp_assoc, h])

theorem tmap_pt (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R R' : CommRingCat.{0}} {χ : A ⟶ R}
    {χ' : A ⟶ R'} (σ : R ⟶ R') (h : χ ≫ σ = χ') (ψ : B ⟶ R) (h' : φ ≫ ψ = χ) :
    tmap jU σ h ≫ pt hc ψ h' = pt hc (ψ ≫ σ) (by rw [← Category.assoc, h', h]) := by
  ext1
  change Spec.map σ ≫ Spec.map ψ ≫ jW = Spec.map (ψ ≫ σ) ≫ jW
  rw [Spec.map_comp, Category.assoc]

theorem tmap_tmap {R R' R'' : CommRingCat.{0}} {χ : A ⟶ R} {χ' : A ⟶ R'} {χ'' : A ⟶ R''}
    (σ : R ⟶ R') (h : χ ≫ σ = χ') (τ : R' ⟶ R'') (h' : χ' ≫ τ = χ'') :
    tmap jU τ h' ≫ tmap jU σ h = tmap jU (σ ≫ τ) (by rw [← Category.assoc, h, h']) := by
  ext1
  change Spec.map τ ≫ Spec.map σ = Spec.map (σ ≫ τ)
  rw [Spec.map_comp]

theorem pt_inj (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) [IsOpenImmersion jW] {G : Over S'} (i : Z ⟶ G)
    [Mono i] {R : CommRingCat.{0}} {χ : A ⟶ R} (ψ ψ' : B ⟶ R) (h : φ ≫ ψ = χ) (h' : φ ≫ ψ' = χ)
    (e : pt hc ψ h ≫ i = pt hc ψ' h' ≫ i) : ψ = ψ' := by
  have e1 := congrArg CommaMorphism.left (cancel_mono i |>.mp e)
  simp only [pt, Over.homMk_left] at e1
  exact Spec.map_injective ((cancel_mono jW).mp e1)

end GlobalTheory.FiniteKilled

end

noncomputable section

namespace GlobalTheory.FiniteKilled

noncomputable def powAlg {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A)
    (Δ : B →ₐ[A] B ⊗[A] B) (n : ℕ) : B →ₐ[A] B :=
  Nat.rec ((Algebra.ofId A B).comp ε)
    (fun _ a => (Algebra.TensorProduct.lift a (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) n

variable {S' : Scheme.{0}} {A B : CommRingCat.{0}} {jU : Spec A ⟶ S'} {Z : Over S'}
  {jW : Spec B ⟶ Z.left} {φ : A ⟶ B}

theorem pt_congr (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) {R : CommRingCat.{0}} {χ : A ⟶ R} {ψ ψ' : B ⟶ R}
    (h : φ ≫ ψ = χ) (e : ψ = ψ') : pt hc ψ h = pt hc ψ' (e ▸ h) := by
  subst e; rfl

theorem exists_alg [Algebra A B] (hφ : φ = CommRingCat.ofHom (algebraMap A B))
    (hc : Spec.map φ ≫ jU = jW ≫ Z.hom) [IsOpenImmersion jW] {G : Over S'} [GrpObj G] (i : Z ⟶ G) [Mono i]
    (hone : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R), ∃ z : tst jU χ ⟶ Z, z ≫ i = 1)
    (hmul : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (a b : tst jU χ ⟶ Z), ∃ c : tst jU χ ⟶ Z,
      c ≫ i = (a ≫ i) * (b ≫ i))
    (hfac : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (z : tst jU χ ⟶ Z), ∃ (ψ : B ⟶ R) (h : φ ≫ ψ = χ),
      z = pt hc ψ h) :
    ∃ (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B),
      (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
        (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B ∧
      (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B ∧
      ∀ n (h : φ ≫ CommRingCat.ofHom (powAlg ε Δ n).toRingHom = φ),
        pt hc (CommRingCat.ofHom (powAlg ε Δ n).toRingHom) h ≫ i =
          (pt hc (𝟙 B) (Category.comp_id φ) ≫ i) ^ n := by
  subst hφ

  have und : ∀ {R : Type} [CommRing R] [Algebra A R] (f : B →ₐ[A] R),
      CommRingCat.ofHom (algebraMap A B) ≫ CommRingCat.ofHom f.toRingHom =
        CommRingCat.ofHom (algebraMap A R) := by
    intro R _ _ f; ext a; simp

  obtain ⟨e0, he0⟩ := hone A (𝟙 A)
  obtain ⟨εc, hε, rfl⟩ := hfac A (𝟙 A) e0
  let ε : B →ₐ[A] A :=
    { εc.hom with commutes' := fun a => congrArg (fun f => f.hom a) hε }
  have hεc : CommRingCat.ofHom ε.toRingHom = εc := rfl
  have hunit : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (σ : A ⟶ R) (h : CommRingCat.ofHom (algebraMap A B) ≫ εc ≫ σ = χ),
      pt hc (εc ≫ σ) h ≫ i = 1 := by
    intro R χ σ h
    have h1 : 𝟙 A ≫ σ = χ := by rw [← h, ← Category.assoc, hε]
    rw [← tmap_pt hc σ h1 εc hε, Category.assoc, he0, comp_one]

  let R2 := CommRingCat.of (B ⊗[A] B)
  let χ2 : A ⟶ R2 := CommRingCat.ofHom (algebraMap A (B ⊗[A] B))
  let inl : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let inr : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  obtain ⟨c, hcm⟩ := hmul R2 χ2 (pt hc (CommRingCat.ofHom inl.toRingHom) (und inl))
    (pt hc (CommRingCat.ofHom inr.toRingHom) (und inr))
  obtain ⟨Δc, hΔ, rfl⟩ := hfac R2 χ2 c
  let Δ : B →ₐ[A] B ⊗[A] B :=
    { Δc.hom with commutes' := fun a => congrArg (fun f => f.hom a) hΔ }

  have key : ∀ {R : Type} [CommRing R] [Algebra A R] (f g : B →ₐ[A] R),
      pt hc (CommRingCat.ofHom ((Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp Δ).toRingHom)
          (und _) ≫ i =
        (pt hc (CommRingCat.ofHom f.toRingHom) (und f) ≫ i) *
          (pt hc (CommRingCat.ofHom g.toRingHom) (und g) ≫ i) := by
    intro R _ _ f g
    let L : R2 ⟶ CommRingCat.of R :=
      CommRingCat.ofHom (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
    have hL : χ2 ≫ L = CommRingCat.ofHom (algebraMap A R) := by
      ext a; exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).commutes a
    have e1 : Δc ≫ L = CommRingCat.ofHom
        ((Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).comp Δ).toRingHom := rfl
    have e2 : CommRingCat.ofHom inl.toRingHom ≫ L = CommRingCat.ofHom f.toRingHom := by
      ext b; simp [L, inl]
    have e3 : CommRingCat.ofHom inr.toRingHom ≫ L = CommRingCat.ofHom g.toRingHom := by
      ext b; simp [L, inr]
    rw [pt_congr hc _ e1.symm, ← tmap_pt hc L hL Δc hΔ, Category.assoc, hcm, comp_mul,
      ← Category.assoc, ← Category.assoc, tmap_pt, tmap_pt, pt_congr hc _ e2, pt_congr hc _ e3]
  have hηε : ∀ (h : CommRingCat.ofHom (algebraMap A B) ≫
      CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom = CommRingCat.ofHom (algebraMap A B)),
      pt hc (CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom) h ≫ i = 1 := by
    intro h
    have e : CommRingCat.ofHom ((Algebra.ofId A B).comp ε).toRingHom = εc ≫ CommRingCat.ofHom (algebraMap A B) := by
      ext b; rfl
    rw [pt_congr hc h e]
    exact hunit _ _ _ _
  have hid : CommRingCat.ofHom (AlgHom.id A B).toRingHom = 𝟙 B := by ext b; rfl
  have hu : ∀ h, pt hc (CommRingCat.ofHom (AlgHom.id A B).toRingHom) h = pt hc (𝟙 B) (Category.comp_id _) :=
    fun h => pt_congr hc h hid
  refine ⟨ε, Δ, ?_, ?_, ?_⟩
  · have k := key ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
    rw [hηε, _root_.one_mul] at k
    have := pt_inj hc i _ _ (und _) (und _) k
    ext b
    exact congrArg (fun f => f.hom b) this
  · have k := key (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
    rw [hηε, _root_.mul_one] at k
    have := pt_inj hc i _ _ (und _) (und _) k
    ext b
    exact congrArg (fun f => f.hom b) this
  · intro n
    induction n with
    | zero => intro h; rw [pow_zero]; exact hηε h
    | succ n ih =>
      intro h
      have k := key (powAlg ε Δ n) (AlgHom.id A B)
      rw [ih (und _), hu (und _), ← pow_succ] at k
      exact k

end GlobalTheory.FiniteKilled

end

namespace GlobalTheory.FiniteKilled

theorem isUnit_of_basicOpen_eq_top' (X : Scheme.{0}) (r : Γ(X, ⊤)) (h : X.basicOpen r = ⊤) : IsUnit r := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen r
  have := hu.map (X.presheaf.map (homOfLE h.ge).op).hom
  have e : ∀ y, (X.presheaf.map (homOfLE h.ge).op).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom y) = y := by
    intro y
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rw [show (homOfLE (X.basicOpen_le r)).op ≫ (homOfLE h.ge).op = 𝟙 (Opposite.op (⊤ : X.Opens)) from
      Quiver.Hom.unop_inj (Subsingleton.elim _ _), CategoryTheory.Functor.map_id]
    rfl
  exact (e r) ▸ this

theorem spec_inv_appTop {B : CommRingCat.{0}} (t : B ⟶ B) :
    (Scheme.ΓSpecIso B).inv ≫ (Spec.map t).appTop = t ≫ (Scheme.ΓSpecIso B).inv := by
  have := Scheme.ΓSpecIso_naturality t
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  simp

theorem spec_eq_of_unit {X : Scheme.{0}} {B : CommRingCat.{0}} (k : X ⟶ Spec B) (α β : B ⟶ B) (b0 : B)
    (hu : IsUnit (((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom b0))
    (h : ∀ b, b0 * (α.hom b - β.hom b) = 0) : k ≫ Spec.map α = k ≫ Spec.map β := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, ← cancel_epi (Scheme.ΓSpecIso B).inv,
    ← Category.assoc, ← Category.assoc, spec_inv_appTop, spec_inv_appTop, Category.assoc, Category.assoc]
  ext b
  have e := congrArg ((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (h b)
  rw [map_mul, map_sub, map_zero, hu.mul_right_eq_zero, sub_eq_zero] at e
  exact e

theorem isUnit_of_range {X S : Scheme.{0}} {U : S.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (k : X ⟶ Spec B) (φ : Γ(S, U) ⟶ B) (g : Γ(S, U))
    (hr : ∀ x, (k ≫ Spec.map φ ≫ hU.fromSpec).base x ∈ S.basicOpen g) :
    IsUnit (((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (φ.hom g)) := by
  have e1 : ((Scheme.ΓSpecIso B).inv ≫ k.appTop).hom (φ.hom g) =
      (k ≫ Spec.map φ).appTop.hom ((Scheme.ΓSpecIso Γ(S, U)).inv.hom g) := by
    have := Scheme.ΓSpecIso_naturality φ
    rw [← Iso.eq_comp_inv] at this
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [this]
    simp only [CommRingCat.comp_apply]
    congr 2
    exact congrArg φ.hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso Γ(S, U)) g).symm
  rw [e1]
  apply isUnit_of_basicOpen_eq_top'
  have e2 := Scheme.preimage_basicOpen (k ≫ Spec.map φ) ((Scheme.ΓSpecIso Γ(S, U)).inv.hom g)
  have e3 := Scheme.preimage_basicOpen hU.fromSpec g
  rw [IsAffineOpen.fromSpec_app_self, CommRingCat.comp_apply, Scheme.basicOpen_res_eq] at e3
  change X.basicOpen ((k ≫ Spec.map φ).app ⊤ _) = ⊤
  rw [← e2, ← e3, eq_top_iff]
  intro x _
  exact hr x

end GlobalTheory.FiniteKilled

namespace GlobalTheory.FiniteKilled

theorem killed_near : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (Z : Over S') (i : Z ⟶ G) (V₀ : S'.Opens) (d : ℕ) (s : S'), Mono i → s ∈ V₀ → IsFinite (Z.hom ∣_ V₀) → (∀ T : Over S', Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ z : T ⟶ Z, z ≫ i = 1) → (∀ (T : Over S') (a b : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i) * (b ≫ i)) → (∀ (T : Over S') (a : T ⟶ Z), Set.range T.hom.base ⊆ (V₀ : Set S') → ∃ c : T ⟶ Z, c ≫ i = (a ≫ i)⁻¹) → IsUnit ((d : ℕ) : S'.residueField s) → (∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s), T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1) → ∃ V : S'.Opens, s ∈ V ∧ V ≤ V₀ ∧ ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (V : Set S') → (z ≫ i) ^ d = 1 := by
  intro S' _ G _ _ Z i V₀ d s hi hs hfin hone hmul hinv hd hfib

  obtain ⟨U, hU, hsU, hUV⟩ := exists_isAffineOpen_mem_and_subset hs
  have hUV : U ≤ V₀ := hUV
  have hfU : IsFinite (Z.hom ∣_ U) := by
    haveI : MorphismProperty.RespectsIso @IsFinite :=
      MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ f (_ : IsIso f) => inferInstance)
    have h1 : IsFinite (Z.hom ∣_ V₀ ∣_ (V₀.ι ⁻¹ᵁ U)) := inferInstance
    rw [MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) (morphismRestrictRestrict _ _ _),
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hUV] at h1
    exact h1
  haveI : IsAffine U := hU
  set W : Z.left.Opens := Z.hom ⁻¹ᵁ U with hWdef
  have hW : IsAffineOpen W := by
    have h1 := (IsAffineHom.isAffine_preimage (f := Z.hom ∣_ U) ⊤ (isAffineOpen_top _)).image_of_isOpenImmersion
      (Z.hom ⁻¹ᵁ U).ι
    rwa [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top] at h1
  let A : CommRingCat.{0} := Γ(S', U)
  let B : CommRingCat.{0} := Γ(Z.left, W)
  let φ : A ⟶ B := Z.hom.appLE U W le_rfl
  letI : Algebra A B := φ.hom.toAlgebra
  have hφ : φ = CommRingCat.ofHom (algebraMap A B) := rfl
  haveI hfinAB : Module.Finite A B := by
    have h1 := IsFinite.finite_app (Z.hom ∣_ U) ⊤ (isAffineOpen_top _)
    rw [morphismRestrict_app'] at h1
    have gen : ∀ (U₁ : S'.Opens) (W₁ : Z.left.Opens) (e₁ : U₁ = U) (e₂ : W₁ = W) (hle : W₁ ≤ Z.hom ⁻¹ᵁ U₁),
        (Z.hom.appLE U₁ W₁ hle).hom.Finite → φ.hom.Finite := by
      rintro _ _ rfl rfl _ h; exact h
    exact gen _ _ (Scheme.Opens.ι_image_top U) (by simp [W]) _ h1
  have hS : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let jU := hU.fromSpec
  let jW := hW.fromSpec
  have hc : Spec.map φ ≫ jU = jW ≫ Z.hom := IsAffineOpen.SpecMap_appLE_fromSpec Z.hom hU hW le_rfl

  have hrange : ∀ (T : Over S') (z : T ⟶ Z), Set.range T.hom.base ⊆ (U : Set S') →
      ∃ k : T.left ⟶ Spec B, k ≫ jW = z.left := by
    intro T z hT
    refine ⟨IsOpenImmersion.lift jW z.left ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    rw [hW.range_fromSpec]
    show Z.hom.base (z.left.base x) ∈ U
    rw [← Scheme.Hom.comp_apply, Over.w z]
    exact hT ⟨x, rfl⟩
  have hrT : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R), Set.range (tst jU χ).hom.base ⊆ (U : Set S') := by
    rintro R χ _ ⟨x, rfl⟩
    rw [← hU.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ x).symm⟩
  have hfac : ∀ (R : CommRingCat.{0}) (χ : A ⟶ R) (z : tst jU χ ⟶ Z), ∃ (ψ : B ⟶ R) (h : φ ≫ ψ = χ),
      z = pt hc ψ h := by
    intro R χ z
    obtain ⟨k, hk⟩ := hrange _ z (hrT R χ)
    have hk' : Spec.map (Spec.preimage (k : Spec R ⟶ Spec B)) = k := Spec.map_preimage _
    have h : φ ≫ Spec.preimage k = χ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hk', ← cancel_mono jU]
      erw [Category.assoc, hc, ← Category.assoc, hk, Over.w z]
      rfl
    refine ⟨Spec.preimage k, h, ?_⟩
    ext1
    change z.left = Spec.map (Spec.preimage k) ≫ jW
    rw [hk']
    exact hk.symm
  obtain ⟨ε, Δ, hc1, hc2, hpow⟩ := exists_alg hφ hc i
    (fun R χ => hone _ ((hrT R χ).trans hUV)) (fun R χ a b => hmul _ a b ((hrT R χ).trans hUV)) hfac
  let α := powAlg ε Δ
  have hund : ∀ n, φ ≫ CommRingCat.ofHom (α n).toRingHom = φ := fun n => by
    ext a; exact (α n).commutes a
  have hcot := GlobalTheory.convPow_sub_nsmul_mem_augIdeal_sq A B ε Δ α hc1 hc2 rfl (fun n => rfl)

  let κ := S'.residueField s
  let χκ : A ⟶ κ := S'.presheaf.germ U s hsU ≫ S'.residue s
  letI : Algebra A κ := χκ.hom.toAlgebra
  let R := CommRingCat.of (κ ⊗[A] B)
  let incl : B →ₐ[A] κ ⊗[A] B := Algebra.TensorProduct.includeRight
  let incL : κ →ₐ[A] κ ⊗[A] B := Algebra.TensorProduct.includeLeft
  let χR : A ⟶ R := CommRingCat.ofHom (algebraMap A (κ ⊗[A] B))
  have hincl : φ ≫ CommRingCat.ofHom incl.toRingHom = χR := by ext a; exact incl.commutes a
  have hTk : (tst jU χR).hom = Spec.map (CommRingCat.ofHom incL.toRingHom) ≫ S'.fromSpecResidueField s := by
    rw [Scheme.fromSpecResidueField, ← hU.fromSpecStalk_eq_fromSpecStalk hsU, IsAffineOpen.fromSpecStalk]
    change Spec.map χR ≫ jU = _
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    congr 2
  have hfibk : (pt hc (CommRingCat.ofHom incl.toRingHom) hincl ≫ i) ^ d = 1 := hfib _ _ ⟨_, hTk⟩
  have hpt : ∀ n, pt hc (CommRingCat.ofHom (α n).toRingHom ≫ CommRingCat.ofHom incl.toRingHom)
      (by rw [← Category.assoc, hund n, hincl]) ≫ i = (pt hc (CommRingCat.ofHom incl.toRingHom) hincl ≫ i) ^ n := by
    intro n
    rw [← tmap_pt hc _ hincl _ (hund n), Category.assoc, hpow n (hund n), comp_pow, ← Category.assoc, tmap_pt,
      pt_congr hc _ (Category.id_comp _)]
  have heq : CommRingCat.ofHom (α d).toRingHom ≫ CommRingCat.ofHom incl.toRingHom =
      CommRingCat.ofHom (α 0).toRingHom ≫ CommRingCat.ofHom incl.toRingHom :=
    pt_inj hc i _ _ _ _ (by rw [hpt d, hpt 0, hfibk, pow_zero])
  have hzero : ∀ b : B, (1 : κ) ⊗ₜ[A] (α d b - algebraMap A B (ε b)) = 0 := by
    intro b
    have := congrArg (fun f => f.hom b) heq
    rw [TensorProduct.tmul_sub, sub_eq_zero]
    exact this
  let P : Ideal A := RingHom.ker (algebraMap A κ)
  have hfibP : ∀ b, ∃ f : A, f ∉ P ∧ f • (α d b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B) :=
    fun b => GlobalTheory.exists_not_mem_ker_smul_mem_map_of_one_tmul_eq_zero A B κ _ (hzero b)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hdP : (d : A) ∉ P := by
    rw [RingHom.mem_ker, map_natCast]; exact hd.ne_zero
  obtain ⟨g, hgP, hg⟩ := GlobalTheory.NakAug.augmentation_agrees_after_inverting A B P ε (α d) d hdP (hcot d) hfibP
  refine ⟨S'.basicOpen g, ?_, (S'.basicOpen_le g).trans hUV, ?_⟩
  · rw [Scheme.mem_basicOpen S' g s hsU, ← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    exact hgP (RingHom.mem_ker.mpr h0)
  · intro T z hT
    have hTU : Set.range T.hom.base ⊆ (U : Set S') := hT.trans (S'.basicOpen_le g)
    obtain ⟨k, hk⟩ := hrange T z hTU
    have hkT : k ≫ Spec.map φ ≫ jU = T.hom := by rw [hc, ← Category.assoc, hk, Over.w z]
    let H : T ⟶ tst jU φ := Over.homMk k hkT
    have hz : z = H ≫ pt hc (𝟙 B) (Category.comp_id φ) := by
      ext1
      change z.left = k ≫ Spec.map (𝟙 B) ≫ jW
      rw [Spec.map_id, Category.id_comp, hk]
    have hkey : k ≫ Spec.map (CommRingCat.ofHom (α d).toRingHom) =
        k ≫ Spec.map (CommRingCat.ofHom (α 0).toRingHom) := by
      refine spec_eq_of_unit k _ _ (φ.hom g) (isUnit_of_range hU k φ g ?_) ?_
      · intro x; rw [hkT]; exact hT ⟨x, rfl⟩
      · intro b; have := hg b; rwa [Algebra.smul_def] at this
    have hHeq : H ≫ pt hc (CommRingCat.ofHom (α d).toRingHom) (hund d) =
        H ≫ pt hc (CommRingCat.ofHom (α 0).toRingHom) (hund 0) := by
      ext1
      change k ≫ Spec.map _ ≫ jW = k ≫ Spec.map _ ≫ jW
      rw [← Category.assoc, hkey, Category.assoc]
    rw [hz, Category.assoc, ← comp_pow, ← hpow d (hund d), ← Category.assoc, hHeq, Category.assoc,
      hpow 0 (hund 0), pow_zero, comp_one]

end GlobalTheory.FiniteKilled
