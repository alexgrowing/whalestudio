import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.CharMul

variable {R : Type} [CommRing R] [IsDomain R]

theorem tensor_sep {K B₁ B₂ I J : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B₁] [CommRing B₂] [Algebra R B₁] [Algebra R B₂] [Module.Flat R B₁]
    [Finite I] [Finite J] (e : I → B₁ →ₐ[R] K) (f : J → B₂ →ₐ[R] K)
    (he : ∀ b, (∀ i, e i b = 0) → b = 0) (hf : ∀ b, (∀ j, f j b = 0) → b = 0)
    (x : B₁ ⊗[R] B₂) (h : ∀ i j, Algebra.TensorProduct.productMap (e i) (f j) x = 0) : x = 0 := by
  classical
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  haveI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  haveI : Module.Flat R (J → K) := Module.Flat.trans R K (J → K)
  let E : B₁ →ₗ[R] (I → K) := LinearMap.pi fun i => (e i).toLinearMap
  let F : B₂ →ₗ[R] (J → K) := LinearMap.pi fun j => (f j).toLinearMap
  have hE : Function.Injective E :=
    (injective_iff_map_eq_zero E).2 fun b hb => he b fun i => congrFun hb i
  have hF : Function.Injective F :=
    (injective_iff_map_eq_zero F).2 fun b hb => hf b fun j => congrFun hb j
  have inj1 := Module.Flat.lTensor_preserves_injective_linearMap (M := B₁) F hF
  have inj2 := Module.Flat.rTensor_preserves_injective_linearMap (M := J → K) E hE
  let y : (I → K) ⊗[R] (J → K) := LinearMap.rTensor (J → K) E (LinearMap.lTensor B₁ F x)
  have key0 : ∀ i j (x : B₁ ⊗[R] B₂), TensorProduct.lift (LinearMap.mul R K)
      (TensorProduct.map (LinearMap.proj i) (LinearMap.proj j)
        (LinearMap.rTensor (J → K) E (LinearMap.lTensor B₁ F x))) =
      Algebra.TensorProduct.productMap (e i) (f j) x := by
    intro i j x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, F]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key : ∀ i j, TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) y = (0 : K ⊗[R] K) := by
    intro i j
    apply Algebra.IsEpi.injective_lift_mul (R := R) (A := K)
    rw [map_zero, ← h i j]
    exact key0 i j x
  have key1 : ∀ i j (y : (I → K) ⊗[R] (J → K)),
      TensorProduct.piRight R R K (fun _ : J => K) (TensorProduct.piLeft R (J → K) (fun _ : I => K) y i) j =
      TensorProduct.map (LinearMap.proj i) (LinearMap.proj j) y := by
    intro i j y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  have y0 : y = 0 := by
    apply (TensorProduct.piLeft R (J → K) (fun _ : I => K)).injective
    rw [map_zero]
    funext i
    apply (TensorProduct.piRight R R K (fun _ : J => K)).injective
    rw [Pi.zero_apply, map_zero]
    funext j
    rw [Pi.zero_apply, ← key i j]
    exact key1 i j y
  exact inj1 (inj2 (by simpa [y] using y0))

theorem pullback_sep {K B₁ B₂ I J : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B₁] [CommRing B₂] [Algebra R B₁] [Algebra R B₂] [Module.Flat R B₁]
    [Finite I] [Finite J] (e : I → B₁ →ₐ[R] K) (f : J → B₂ →ₐ[R] K)
    (he : ∀ b, (∀ i, e i b = 0) → b = 0) (hf : ∀ b, (∀ j, f j b = 0) → b = 0)
    (a₁ : Spec (CommRingCat.of B₁) ⟶ Spec (CommRingCat.of R))
    (a₂ : Spec (CommRingCat.of B₂) ⟶ Spec (CommRingCat.of R))
    (h₁ : a₁ = Spec.map (CommRingCat.ofHom (algebraMap R B₁)))
    (h₂ : a₂ = Spec.map (CommRingCat.ofHom (algebraMap R B₂)))
    (u : Γ(pullback a₁ a₂, ⊤))
    (hz : ∀ i j (w : Spec (CommRingCat.of K) ⟶ pullback a₁ a₂),
      w ≫ pullback.fst a₁ a₂ = Spec.map (CommRingCat.ofHom (e i).toRingHom) →
      w ≫ pullback.snd a₁ a₂ = Spec.map (CommRingCat.ofHom (f j).toRingHom) → w.appTop u = 0) :
    u = 0 := by
  subst h₁ h₂
  set iso := pullbackSpecIso R B₁ B₂ with hiso
  let x : B₁ ⊗[R] B₂ := (Scheme.ΓSpecIso (CommRingCat.of (B₁ ⊗[R] B₂))).hom (iso.inv.appTop u)
  have x0 : x = 0 := by
    refine tensor_sep e f he hf x fun i j => ?_
    let pm := Algebra.TensorProduct.productMap (e i) (f j)
    let w : Spec (CommRingCat.of K) ⟶ _ := Spec.map (CommRingCat.ofHom pm.toRingHom) ≫ iso.inv
    have hw1 : w ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (e i).toRingHom) := by
      simp only [w, Category.assoc, hiso, pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext b
      simp [pm]
    have hw2 : w ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (f j).toRingHom) := by
      simp only [w, Category.assoc, hiso, pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext b
      simp [pm]
    have h0 := hz i j w hw1 hw2
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of K)).hom (w.appTop u) = pm x := by
      have := congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom pm.toRingHom)) (iso.inv.appTop u))
      simp only [w, Scheme.Hom.comp_appTop]
      exact this
    rw [h0, map_zero] at h1
    exact h1.symm
  have h2 : iso.inv.appTop u = 0 := by
    have := congr((Scheme.ΓSpecIso (CommRingCat.of (B₁ ⊗[R] B₂))).inv $x0)
    simpa [x] using this
  have h3 : u = iso.hom.appTop (iso.inv.appTop u) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, iso.hom_inv_id]
    simp
  rw [h3, h2, map_zero]

variable {T : Type} [CommGroup T]

theorem valAt_chart {B C : Type} [CommRing B] [CommRing C] {X : Scheme.{0}} (c : Spec (CommRingCat.of B) ⟶ X)
    [IsOpenImmersion c] (φ : B →+* C) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ c) ⁻¹ᵁ (c ''ᵁ ⊤)) (b : B) :
    valAt (Spec.map (CommRingCat.ofHom φ) ≫ c) (c ''ᵁ ⊤) h
      ((c.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) = φ b := by
  have h1 : (Spec.map (CommRingCat.ofHom φ) ≫ c).appLE (c ''ᵁ ⊤) ⊤ h =
      (c.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.appIso_hom', ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ _ le_rfl]
    rfl
  unfold valAt
  rw [h1]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of C)).hom ((Spec.map (CommRingCat.ofHom φ)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) :=
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))
  have h3 : (c.appIso ⊤).hom ((c.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv b := Iso.inv_hom_id_apply _ _
  have h4 : (Scheme.ΓSpecIso (CommRingCat.of B)).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) = b :=
    Iso.inv_hom_id_apply _ _
  rw [h4, ← h3] at h2
  exact h2

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  classical
  let I := {t : T // Set.range (Γ.pt t).left ⊆ Set.range c}
  have lift : ∀ i : I, ∃ e : B →ₐ[R] FractionRing R,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ c = (Γ.pt i.1).left := by
    intro i
    let g := IsOpenImmersion.lift c (Γ.pt i.1).left i.2
    have hg : g ≫ c = (Γ.pt i.1).left := IsOpenImmersion.lift_fac _ _ _
    let φ : B →+* FractionRing R := (Spec.preimage g).hom
    have hφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
    have hcomp : φ.comp (algebraMap R B) = algebraMap R (FractionRing R) := by
      have h1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R B))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, ← hc, ← Category.assoc, hg]
        exact Over.w (Γ.pt i.1)
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    refine ⟨{ φ with commutes' := fun r => congr($hcomp r) }, ?_⟩
    exact (congrArg (· ≫ c) hφ).trans hg
  choose e he using lift
  refine ⟨I, inferInstance, Subtype.val, e, he, fun b hb => ?_⟩
  have hs := GlobalTheory.T.section_eq_zero_of_values R T Γ (c ''ᵁ ⊤)
    ((c.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) (fun t h => by
      have hr : Set.range (Γ.pt t).left ⊆ Set.range c := by
        rintro _ ⟨x, rfl⟩
        have := h (show x ∈ (⊤ : (Spec (CommRingCat.of (FractionRing R))).Opens) from trivial)
        obtain ⟨y, -, hy⟩ := this
        exact ⟨y, hy⟩
      have key : ∀ (p : Spec (CommRingCat.of (FractionRing R)) ⟶ Γ.G.left)
          (hp : Spec.map (CommRingCat.ofHom (e ⟨t, hr⟩).toRingHom) ≫ c = p) (h' : ⊤ ≤ p ⁻¹ᵁ (c ''ᵁ ⊤)),
          valAt p (c ''ᵁ ⊤) h' ((c.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) = 0 := by
        rintro p rfl h'
        rw [valAt_chart]
        exact hb ⟨t, hr⟩
      exact key _ (he ⟨t, hr⟩) h)
  have h1 := congr((c.appIso ⊤).hom $hs)
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of B)).hom $h1)
  simpa using h2

theorem chart_pair [Finite T] (Γ : QFGroup R T) (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂]
    (c₁ : Spec (CommRingCat.of A₁) ⟶ Γ.G.left) (c₂ : Spec (CommRingCat.of A₂) ⟶ Γ.G.left)
    (o₁ : IsOpenImmersion c₁) (o₂ : IsOpenImmersion c₂) (u : Γ(pullback (c₁ ≫ Γ.G.hom) (c₂ ≫ Γ.G.hom), ⊤))
    (hu : ∀ (a b : T) (w : Spec (CommRingCat.of (FractionRing R)) ⟶ pullback (c₁ ≫ Γ.G.hom) (c₂ ≫ Γ.G.hom)),
      w ≫ pullback.fst _ _ ≫ c₁ = (Γ.pt a).left → w ≫ pullback.snd _ _ ≫ c₂ = (Γ.pt b).left → w.appTop u = 0) :
    u = 0 := by
  letI : Algebra R A₁ := (Spec.preimage (c₁ ≫ Γ.G.hom)).hom.toAlgebra
  letI : Algebra R A₂ := (Spec.preimage (c₂ ≫ Γ.G.hom)).hom.toAlgebra
  have h₁ : c₁ ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R A₁)) :=
    (Spec.map_preimage (c₁ ≫ Γ.G.hom)).symm
  have h₂ : c₂ ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R A₂)) :=
    (Spec.map_preimage (c₂ ≫ Γ.G.hom)).symm
  haveI : Flat Γ.G.hom := Γ.flat
  haveI : Module.Flat R A₁ := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) := h₁ ▸ inferInstance
    rw [Flat.SpecMap_iff] at this
    exact (RingHom.flat_algebraMap_iff).1 this
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ A₁ c₁ h₁
  obtain ⟨J, _, τ', f, hf, hj⟩ := chart_sep Γ A₂ c₂ h₂
  refine pullback_sep e f hi hj _ _ h₁ h₂ u fun i j w hw₁ hw₂ => hu (τ i) (τ' j) w ?_ ?_
  · rw [← Category.assoc, hw₁, he]
  · rw [← Category.assoc, hw₂, hf]

theorem sec_prod_zero [Finite T] (Γ : QFGroup R T) (u : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hu : ∀ a b, (lift (Γ.pt a) (Γ.pt b)).left.appTop u = 0) : u = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem (X := pullback Γ.G.hom Γ.G.hom) u 0
    (Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom) fun ij => ?_
  rw [map_zero]
  obtain ⟨i, j⟩ := ij
  refine chart_pair Γ (𝒰.X i) (𝒰.X j) (𝒰.f i) (𝒰.f j) (𝒰.openCover.map_prop i) (𝒰.openCover.map_prop j) _
    fun a b w h₁ h₂ => ?_
  have hw : w ≫ (Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom).f (i, j) =
      (lift (Γ.pt a) (Γ.pt b)).left := by
    rw [Over.lift_left, Scheme.Pullback.openCoverOfLeftRight_f]
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (pullback.lift_fst _ _ _).symm)
      exact (congrArg (w ≫ ·) (pullback.lift_fst _ _ _)).trans h₁
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm)
      exact (congrArg (w ≫ ·) (pullback.lift_snd _ _ _)).trans h₂
  have h0 := hu a b
  rw [← hw] at h0
  have e := congr($(Scheme.Hom.comp_appTop w
    ((Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom).f (i, j))) u)
  exact e.symm.trans h0

theorem pull {S : Scheme.{0}} {Y Y' G : Over S} (q : Y' ⟶ Y) (g : Y ⟶ G) (s : Γ(G.left, ⊤)) :
    q.left.appTop (g.left.appTop s) = (q ≫ g).left.appTop s := by
  rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

theorem appTop_pt (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤)) (f : T → R) (hs : Γ.HasValues s f) (t : T) :
    (Γ.pt t).left.appTop s =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv (algebraMap R (FractionRing R) (f t)) := by
  have h := congr((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv $(hs t))
  rw [← h]
  unfold valAt
  simp
  rfl

theorem mul_univ [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) :
    (fst Γ.G Γ.G * snd Γ.G Γ.G).left.appTop s =
      (fst Γ.G Γ.G).left.appTop s * (snd Γ.G Γ.G).left.appTop s := by
  rw [← sub_eq_zero]
  refine sec_prod_zero Γ _ fun a b => ?_
  rw [map_sub, map_mul, pull, pull, pull, comp_mul, lift_fst, lift_snd, ← map_mul, appTop_pt Γ s _ hs,
    appTop_pt Γ s _ hs, appTop_pt Γ s _ hs, ← map_mul, ← map_mul, map_mul χ, Units.val_mul, sub_self]

theorem appTop_gen_injective :
    Function.Injective (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop := by
  intro x y hxy
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have hx : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom
      ((Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))).appTop x) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom x) := fun x => congr($n x)
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom $hxy)
  rw [hx, hx] at h2
  have h3 := IsFractionRing.injective R (FractionRing R) h2
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective h3

theorem one_univ (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤))
    (hs : Γ.HasValues s (fun t => ((χ t : Rˣ) : R))) :
    (η[Γ.G]).left.appTop s = 1 := by
  let g : genPt R ⟶ 𝟙_ (Over (Spec (CommRingCat.of R))) := toUnit _
  have hg : g.left = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
    have := Over.w g
    simpa using this
  have h1 : g.left.appTop ((η[Γ.G]).left.appTop s) = 1 := by
    rw [pull]
    have : g ≫ η[Γ.G] = Γ.pt 1 := by
      rw [map_one, Hom.one_def]
    rw [this, appTop_pt Γ s _ hs, map_one χ, Units.val_one, map_one, map_one]
  have inj : Function.Injective (g.left.appTop) := by
    rw [hg]
    exact appTop_gen_injective
  exact inj (h1.trans (map_one _).symm)

end GlobalTheory.CompanionTheory.Ar.BT.CharMul

open GlobalTheory.CompanionTheory.Ar.BT.CharMul in

theorem GlobalTheory.CompanionTheory.Ar.BT.charValues_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) → ∀ (Y : Over (Spec (CommRingCat.of R))), (∀ y z : Y ⟶ Γ.G, (y * z).left.appTop s = y.left.appTop s * z.left.appTop s) ∧ (1 : Y ⟶ Γ.G).left.appTop s = 1 := by
  intro R _ _ T _ _ Γ χ s hs Y
  refine ⟨fun y z => ?_, ?_⟩
  · have h := congrArg (lift y z).left.appTop (mul_univ Γ χ s hs)
    rw [pull, map_mul, pull, pull, comp_mul, lift_fst, lift_snd] at h
    exact h
  · rw [Hom.one_def, ← pull, one_univ Γ χ s hs, map_one]
