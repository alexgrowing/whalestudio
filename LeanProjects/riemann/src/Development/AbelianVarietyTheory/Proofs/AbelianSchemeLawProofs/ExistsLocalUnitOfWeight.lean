import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsorUnit

section Algebra

variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']

noncomputable def ev (θ : C →+* R) (φ : Multiplicative X →* Rˣ) : AddMonoidAlgebra C X →+* R :=
  AddMonoidAlgebra.liftNCRingHom θ ((Units.coeHom R).comp φ) fun _ _ => Commute.all _ _

theorem ev_single (θ : C →+* R) (φ : Multiplicative X →* Rˣ) (x : X) (c : C) :
    ev θ φ (AddMonoidAlgebra.single x c) = θ c * (φ (Multiplicative.ofAdd x)).val := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom]

theorem comp_ev (f : R →+* R') (θ : C →+* R) (φ : Multiplicative X →* Rˣ) :
    f.comp (ev θ φ) = ev (f.comp θ) ((Units.map f.toMonoidHom).comp φ) := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro a <;> simp [ev_single]

variable (C X) in

noncomputable def univ : Multiplicative X →* (AddMonoidAlgebra C X)ˣ :=
  (AddMonoidAlgebra.of C X).toHomUnits

theorem univ_val (x : X) :
    (univ X C (Multiplicative.ofAdd x)).val = AddMonoidAlgebra.single x 1 := rfl

variable (C X) in

noncomputable abbrev cst : C →+* AddMonoidAlgebra C X := AddMonoidAlgebra.singleZeroRingHom

theorem cst_apply (c : C) : cst X C c = AddMonoidAlgebra.single 0 c := rfl

theorem ev_univ : ev (cst X C) (univ X C) = RingHom.id _ := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro a <;>
    simp [ev_single, univ_val, AddMonoidAlgebra.single_mul_single]

theorem ev_comp_cst (θ : C →+* R) (φ : Multiplicative X →* Rˣ) : (ev θ φ).comp (cst X C) = θ := by
  ext a; simp [ev_single]

theorem ev_comp_univ (θ : C →+* R) (φ : Multiplicative X →* Rˣ) :
    (Units.map (ev θ φ).toMonoidHom).comp (univ X C) = φ := by
  ext x
  change ev θ φ (univ X C (Multiplicative.ofAdd x)).val = _
  simp [univ_val, ev_single]

theorem coeff_ev (δ : C →+* R) (ψ : Multiplicative X →* Rˣ) (f : AddMonoidAlgebra C X) (x : X) :
    (ev ((cst X R).comp δ) (univ X R * (Units.map (cst X R).toMonoidHom).comp ψ) f).coeff x =
      δ (f.coeff x) * (ψ (Multiplicative.ofAdd x)).val := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, add_mul]
  | single y c =>
    rw [ev_single]
    change (AddMonoidAlgebra.single 0 (δ c) * (AddMonoidAlgebra.single y 1 *
      AddMonoidAlgebra.single 0 (ψ (Multiplicative.ofAdd y)).val)).coeff x = _
    simp only [AddMonoidAlgebra.single_mul_single, zero_add, add_zero, _root_.one_mul,
      AddMonoidAlgebra.coeff_single]
    by_cases h : y = x
    · subst h; simp
    · simp [Finsupp.single_eq_of_ne' h]

variable (R) in

def IsTorsorOn (α : A →+* C) (ρ : C →+* AddMonoidAlgebra C X) : Prop :=
  (∀ (θ : C →+* R) (φ φ' : Multiplicative X →* Rˣ),
    (ev θ (φ * φ')).comp ρ = (ev ((ev θ φ').comp ρ) φ).comp ρ) ∧
  (∀ (θ : C →+* R) (φ : Multiplicative X →* Rˣ), ((ev θ φ).comp ρ).comp α = θ.comp α) ∧
  (∀ (θ : C →+* R) (φ φ' : Multiplicative X →* Rˣ),
    (ev θ φ).comp ρ = (ev θ φ').comp ρ → φ = φ') ∧
  (∀ θ θ' : C →+* R, θ.comp α = θ'.comp α → ∃ φ : Multiplicative X →* Rˣ, θ' = (ev θ φ).comp ρ)

theorem IsTorsorOn.of_equiv {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X} (e : R ≃+* R')
    (h : IsTorsorOn R' α ρ) : IsTorsorOn R α ρ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have inj : ∀ {T : Type} [CommRing T] {a b : T →+* R},
      e.toRingHom.comp a = e.toRingHom.comp b → a = b := fun h =>
    RingHom.ext fun x => e.injective (RingHom.congr_fun h x)
  have nat : ∀ (θ : C →+* R) (φ : Multiplicative X →* Rˣ), e.toRingHom.comp ((ev θ φ).comp ρ) =
      (ev (e.toRingHom.comp θ) ((Units.map e.toRingHom.toMonoidHom).comp φ)).comp ρ :=
    fun θ φ => by rw [← RingHom.comp_assoc, comp_ev]
  refine ⟨fun θ φ φ' => inj ?_, fun θ φ => inj ?_, fun θ φ φ' h => ?_, fun θ θ' h => ?_⟩
  · rw [nat, nat, nat, ← h1, MonoidHom.comp_mul]
  · rw [← RingHom.comp_assoc, nat, h2, RingHom.comp_assoc]
  · have := h3 _ _ _ ((nat θ φ).symm.trans ((congrArg _ h).trans (nat θ φ')))
    ext x
    exact e.injective (congrArg Units.val (DFunLike.congr_fun this x))
  · obtain ⟨φ, hφ⟩ := h4 (e.toRingHom.comp θ) (e.toRingHom.comp θ')
      (by rw [RingHom.comp_assoc, h, RingHom.comp_assoc])
    refine ⟨(Units.map e.symm.toRingHom.toMonoidHom).comp φ, inj ?_⟩
    rw [nat, hφ]
    congr 2
    ext x
    simp

theorem coaction_coeff {α : A →+* C} {ρ : C →+* AddMonoidAlgebra C X}
    (h : IsTorsorOn (AddMonoidAlgebra (AddMonoidAlgebra C X) X) α ρ) (c : C) (x : X) :
    ρ ((ρ c).coeff x) = AddMonoidAlgebra.single x ((ρ c).coeff x) := by
  have h1 := RingHom.congr_fun (h.1 ((cst X _).comp (cst X C)) (univ X _)
    ((Units.map (cst X _).toMonoidHom).comp (univ X C))) c
  rw [← comp_ev, ev_univ, RingHom.comp_id] at h1
  have h2 := congrArg (fun f => AddMonoidAlgebra.coeff f x) h1
  have h3 := coeff_ev ρ 1 (ρ c) x
  simp only [RingHom.comp_apply] at h2
  rw [coeff_ev, univ_val, cst_apply, AddMonoidAlgebra.single_mul_single] at h2
  rw [MonoidHom.comp_one, _root_.mul_one, ← h2] at h3
  simpa using h3.symm

theorem exists_homogeneous {α : A →+* C} (hα : α.FaithfullyFlat) {ρ : C →+* AddMonoidAlgebra C X}
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (χ : X) (p : Ideal A) (hp : p ≠ ⊤) :
    ∃ a ∉ p, ∃ c c' : C, c * c' = α a ∧ ρ c = AddMonoidAlgebra.single χ c := by
  letI : Algebra A C := α.toAlgebra
  haveI : Module.FaithfullyFlat A C := hα
  have hco := coaction_coeff (h _)
  obtain ⟨φ, hφ⟩ := (h (C ⊗[A] C)).2.2.2
    (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom
    Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := C) (B := C)).symm
  have h0 : ∀ c : C, ρ c = AddMonoidAlgebra.single 0 c → ∃ a, α a = c := by
    intro c hc
    have h1 := RingHom.congr_fun hφ c
    rw [RingHom.comp_apply, hc, ev_single] at h1
    refine (Algebra.IsEffective.of_faithfullyFlat A C c).1 ?_
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using h1
  have hρα : ∀ a, ρ (α a) = AddMonoidAlgebra.single 0 (α a) := by
    intro a
    have := RingHom.congr_fun ((h _).2.1 (cst X C) (univ X C)) a
    rwa [ev_univ] at this
  let ρ' : C →ₐ[A] AddMonoidAlgebra C X := { ρ with commutes' := hρα }
  let κ : C →ₐ[A] AddMonoidAlgebra C X := { cst X C with commutes' := fun _ => rfl }
  let Φ : C ⊗[A] C →ₐ[A] AddMonoidAlgebra C X :=
    Algebra.TensorProduct.lift ρ' κ fun _ _ => Commute.all _ _
  have hΦ : ∀ c c' : C, Φ (c ⊗ₜ c') = ρ c * AddMonoidAlgebra.single 0 c' := fun _ _ => rfl
  have hu : (Units.map Φ.toRingHom.toMonoidHom).comp φ = univ X C := by
    apply (h _).2.2.1 (cst X C)
    have h1 := congrArg (Φ.toRingHom.comp ·) hφ
    simp only [← RingHom.comp_assoc, comp_ev] at h1
    have h2 : Φ.toRingHom.comp
        (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom = cst X C := by
      refine RingHom.ext fun c => ?_
      change Φ (1 ⊗ₜ c) = _
      rw [hΦ, map_one, _root_.one_mul, cst_apply]
    rw [h2] at h1
    rw [← h1, ev_univ]
    refine RingHom.ext fun c => ?_
    change Φ (c ⊗ₜ 1) = ρ c
    rw [hΦ, ← AddMonoidAlgebra.one_def, _root_.mul_one]
  have hχ : Φ (φ (Multiplicative.ofAdd χ)).val = AddMonoidAlgebra.single χ 1 :=
    congrArg Units.val (DFunLike.congr_fun hu (Multiplicative.ofAdd χ))
  by_contra! hcon
  have key : ∀ e : C ⊗[A] C, ∃ a ∈ p, α a = (ρ ((Φ e).coeff χ)).coeff 0 := by
    intro e
    induction e using TensorProduct.induction_on with
    | zero => exact ⟨0, p.zero_mem, by simp⟩
    | add e e' he he' =>
      obtain ⟨a, ha, h1⟩ := he
      obtain ⟨a', ha', h1'⟩ := he'
      exact ⟨a + a', p.add_mem ha ha', by simp [h1, h1']⟩
    | tmul c c' =>
      have h1 : (Φ (c ⊗ₜ c')).coeff χ = (ρ c).coeff χ * c' := by
        rw [hΦ]; simp
      have h2 : (ρ ((ρ c).coeff χ * c')).coeff 0 = (ρ c).coeff χ * (ρ c').coeff (-χ) := by
        rw [map_mul, hco]; simp
      obtain ⟨a, ha⟩ := h0 ((ρ c).coeff χ * (ρ c').coeff (-χ)) (by
        rw [map_mul, hco, hco, AddMonoidAlgebra.single_mul_single, add_neg_cancel])
      refine ⟨a, ?_, by rw [h1, h2, ha]⟩
      by_contra hap
      exact hcon a hap _ _ ha.symm (hco c χ)
  obtain ⟨a, ha, h1⟩ := key (φ (Multiplicative.ofAdd χ)).val
  rw [hχ] at h1
  have h2 : α a = α 1 := by simpa [AddMonoidAlgebra.one_def] using h1
  exact hp ((Ideal.eq_top_iff_one p).2 (hα.injective h2 ▸ ha))

end Algebra

section Points

variable {Y Z Z' : Scheme.{0}} {U : Y.Opens}

noncomputable def pt (hU : IsAffineOpen U) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) : Z ⟶ Y :=
  Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ) ≫ hU.fromSpec

theorem toSpec_appTop {R : CommRingCat.{0}} (θ : R →+* Γ(Z, ⊤)) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom =
      θ := by
  have := SplitTorusPoints.ΓSpecIso_inv_comp_specMap Z.toSpecΓ (CommRingCat.ofHom θ)
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id] at this
  exact congrArg CommRingCat.Hom.hom this

theorem comp_pt (hU : IsAffineOpen U) (f : Z' ⟶ Z) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    f ≫ pt hU θ = pt hU (f.appTop.hom.comp θ) := by
  rw [pt, pt, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc]
  rfl

theorem pt_comp {B : Scheme.{0}} {V : B.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (q : Y ⟶ B) (e : U ≤ q ⁻¹ᵁ V) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    pt hU θ ≫ q = pt hV (θ.comp (q.appLE V U e).hom) := by
  rw [pt, pt, Category.assoc, Category.assoc, ← hV.SpecMap_appLE_fromSpec q hU e,
    ← Spec.map_comp_assoc]
  rfl

theorem le_pt_preimage (hU : IsAffineOpen U) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) :
    ⊤ ≤ pt hU θ ⁻¹ᵁ U := by
  rw [pt, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
  exact le_rfl

theorem pt_appLE (hU : IsAffineOpen U) (θ : Γ(Y, U) →+* Γ(Z, ⊤)) (e : ⊤ ≤ pt hU θ ⁻¹ᵁ U) :
    ((pt hU θ).appLE U ⊤ e).hom = θ := by
  have h1 : hU.fromSpec.appLE U ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ _)).trans
      (CategoryTheory.Functor.map_id _ _))).trans (Category.comp_id _)
  have h2 := Scheme.Hom.appLE_comp_appLE (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)) hU.fromSpec
    U ⊤ ⊤ hU.fromSpec_preimage_self.ge le_rfl
  rw [h1] at h2
  have h3 : (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appLE ⊤ ⊤ le_rfl =
      (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom θ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [h3] at h2
  exact (congrArg CommRingCat.Hom.hom h2).symm.trans (toSpec_appTop θ)

theorem pt_injective (hU : IsAffineOpen U) {θ θ' : Γ(Y, U) →+* Γ(Z, ⊤)} (h : pt hU θ = pt hU θ') :
    θ = θ' := by
  have h1 := pt_appLE hU θ (le_pt_preimage hU θ)
  have h2 := pt_appLE hU θ' (le_pt_preimage hU θ')
  rw [← h1, ← h2]
  congr 2

theorem exists_eq_pt (hU : IsAffineOpen U) (g : Z ⟶ Y) (e : ⊤ ≤ g ⁻¹ᵁ U) :
    ∃ θ, g = pt hU θ := by
  have hr : Set.range g ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact e trivial
  let l := IsOpenImmersion.lift hU.fromSpec g hr
  refine ⟨((Scheme.ΓSpecIso _).inv ≫ l.appTop).hom, ?_⟩
  rw [pt, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp_assoc,
    Iso.inv_hom_id, Spec.map_id]
  exact (IsOpenImmersion.lift_fac _ _ hr).symm.trans (congrArg (l ≫ ·) (Category.id_comp _).symm)

end Points

section Action

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G}

open SplitTorusPoints

theorem toHom_comp {Z Z' : Over S} (f : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) :
    toHom (f ≫ t) = (Units.map f.left.appTop.hom.toMonoidHom).comp (toHom t) := by
  ext x
  change (toHom (f ≫ t) (Multiplicative.ofAdd x)).val =
    f.left.appTop.hom (toHom t (Multiplicative.ofAdd x)).val
  rw [toHom_val, toHom_val, coord_single, coord_single, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

theorem act_comp [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ i) * g) ≫ q = g ≫ q := by
  have : (t ≫ i) ≫ q = 1 := by
    rw [Category.assoc, hi.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  rw [MonObj.mul_comp, this, _root_.one_mul]

theorem exists_coaction [IsMonHom q] (hi : IsPullback i (toUnit _) q η[B]) {V : B.left.Opens}
    (hU : IsAffineOpen (q.left ⁻¹ᵁ V)) :
    ∃ ρ : Γ(G.left, q.left ⁻¹ᵁ V) →+* AddMonoidAlgebra Γ(G.left, q.left ⁻¹ᵁ V) X,
      ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (θ), g.left = pt hU θ →
        ((t ≫ i) * g).left = pt hU ((ev θ (toHom t)).comp ρ) := by
  let C := Γ(G.left, q.left ⁻¹ᵁ V)
  let D : CommRingCat.{0} := .of (AddMonoidAlgebra C X)
  let j : AddMonoidAlgebra C X →+* Γ(Spec D, ⊤) := (Scheme.ΓSpecIso D).inv.hom
  let Z₀ : Over S := Over.mk (pt hU (j.comp (cst X C)) ≫ G.hom)
  let g₀ : Z₀ ⟶ G := Over.homMk (pt hU (j.comp (cst X C))) rfl
  obtain ⟨t₀, ht₀⟩ := (toHom_bijective (Z := Z₀) (X := X)).2
    ((Units.map j.toMonoidHom).comp (univ X C))
  have e : ⊤ ≤ ((t₀ ≫ i) * g₀).left ⁻¹ᵁ q.left ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, act_comp hi, Over.comp_left,
      Scheme.Hom.comp_preimage]
    exact le_pt_preimage hU _
  obtain ⟨ρ₀, hρ₀⟩ := exists_eq_pt hU _ e
  refine ⟨(Scheme.ΓSpecIso D).hom.hom.comp ρ₀, fun Z t g θ hg => ?_⟩
  let π₀ : Z.left ⟶ Spec D := Z.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (ev θ (toHom t)))
  have hπ : π₀.appTop.hom.comp j = ev θ (toHom t) := toSpec_appTop (R := D) _
  have h1 : π₀ ≫ g₀.left = g.left := by
    refine (comp_pt hU π₀ _).trans ?_
    rw [← RingHom.comp_assoc, hπ, ev_comp_cst, hg]
  let π : Z ⟶ Z₀ := Over.homMk π₀ (by
    rw [← Over.w g, ← h1, Category.assoc]; rfl)
  have h2 : π ≫ g₀ = g := Over.OverMorphism.ext h1
  have h3 : π ≫ t₀ = t := by
    apply toHom_bijective.1
    rw [toHom_comp, ht₀, ← ev_comp_univ θ (toHom t), ← hπ]
    rfl
  have h4 : (t ≫ i) * g = π ≫ ((t₀ ≫ i) * g₀) := by
    rw [MonObj.comp_mul, h2, ← Category.assoc, h3]
  rw [h4, Over.comp_left, hρ₀]
  refine (comp_pt hU π₀ _).trans ?_
  rw [← hπ]
  congr 1
  refine RingHom.ext fun c => ?_
  change π₀.appTop.hom (ρ₀ c) = π₀.appTop.hom (((Scheme.ΓSpecIso D).hom ≫
    (Scheme.ΓSpecIso D).inv).hom (ρ₀ c))
  rw [Iso.hom_inv_id]
  rfl

theorem isTorsorOn [IsMonHom q] [IsMonHom i] (hi : IsPullback i (toUnit _) q η[B])
    {V : B.left.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen (q.left ⁻¹ᵁ V))
    {ρ : Γ(G.left, q.left ⁻¹ᵁ V) →+* AddMonoidAlgebra Γ(G.left, q.left ⁻¹ᵁ V) X}
    (hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (θ), g.left = pt hU θ →
        ((t ≫ i) * g).left = pt hU ((ev θ (toHom t)).comp ρ)) (Z : Scheme.{0}) :
    IsTorsorOn Γ(Z, ⊤) (q.left.appLE V _ le_rfl).hom ρ := by
  let FinalForm : (Γ(G.left, q.left ⁻¹ᵁ V) →+* Γ(Z, ⊤)) → Over S := fun θ => Over.mk (pt hU θ ≫ G.hom)
  let g : ∀ θ, FinalForm θ ⟶ G := fun θ => Over.homMk (pt hU θ) rfl
  have ex : ∀ θ (φ : Multiplicative X →* Γ(Z, ⊤)ˣ), ∃ t : FinalForm θ ⟶ splitTorus S X, toHom t = φ :=
    fun θ φ => (toHom_bijective (Z := FinalForm θ) (X := X)).2 φ
  refine ⟨fun θ φ φ' => ?_, fun θ φ => ?_, fun θ φ φ' h => ?_, fun θ θ' h => ?_⟩
  · obtain ⟨t, rfl⟩ := ex θ φ
    obtain ⟨t', rfl⟩ := ex θ φ'
    have h1 := hρ _ (t * t') (g θ) θ rfl
    have h2 := hρ _ t _ _ (hρ _ t' (g θ) θ rfl)
    rw [toHom_mul, MonObj.mul_comp, _root_.mul_assoc, h2] at h1
    exact (pt_injective hU h1).symm
  · obtain ⟨t, rfl⟩ := ex θ φ
    have h1 := congrArg Over.Hom.left (act_comp hi t (g θ))
    rw [Over.comp_left, Over.comp_left, hρ _ t (g θ) θ rfl] at h1
    exact pt_injective hV ((pt_comp hU hV q.left le_rfl _).symm.trans
      (h1.trans (pt_comp hU hV q.left le_rfl _)))
  · obtain ⟨t, rfl⟩ := ex θ φ
    obtain ⟨t', rfl⟩ := ex θ φ'
    have h1 : (t ≫ i) * g θ = (t' ≫ i) * g θ := Over.OverMorphism.ext
      ((hρ _ t (g θ) θ rfl).trans ((congrArg (pt hU) h).trans (hρ _ t' (g θ) θ rfl).symm))
    rw [hi.hom_ext (mul_right_cancel h1) (toUnit_unique _ _)]
  · have h1 : pt hU θ' ≫ q.left = pt hU θ ≫ q.left := by
      rw [pt_comp hU hV q.left le_rfl, pt_comp hU hV q.left le_rfl, h]
    let g' : FinalForm θ ⟶ G := Over.homMk (pt hU θ') (by
      change _ = pt hU θ ≫ G.hom
      rw [← Over.w q, ← Category.assoc, h1, Category.assoc])
    have h2 : g' ≫ q = g θ ≫ q := Over.OverMorphism.ext h1
    have h3 : (g' * (g θ)⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h2, mul_inv_cancel, Hom.one_def]
    refine ⟨toHom (hi.lift _ _ h3), pt_injective hU ?_⟩
    refine Eq.trans ?_ (hρ _ (hi.lift _ _ h3) (g θ) θ rfl)
    rw [hi.lift_fst, inv_mul_cancel_right]
    rfl

end Action

theorem faithfullyFlat_appLE {Y B : Scheme.{0}} (q : Y ⟶ B) [Flat q] [Surjective q] {V : B.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen (q ⁻¹ᵁ V)) :
    (q.appLE V (q ⁻¹ᵁ V) le_rfl).hom.FaithfullyFlat := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨HasRingHomProperty.appLE @Flat q inferInstance ⟨V, hV⟩ ⟨_, hU⟩ le_rfl, fun p => ?_⟩
  obtain ⟨y, hy⟩ := q.surjective (hV.fromSpec p)
  have hyU : y ∈ q ⁻¹ᵁ V := by
    change q y ∈ V
    rw [hy]
    exact hV.range_fromSpec.le ⟨p, rfl⟩
  obtain ⟨P, rfl⟩ := hU.range_fromSpec.ge hyU
  refine ⟨P, hV.fromSpec.isOpenEmbedding.injective ?_⟩
  exact (congr($(hV.SpecMap_appLE_fromSpec q hU le_rfl) P)).trans hy

end TorsorUnit

open TorsorUnit SplitTorusPoints in

theorem exists_local_unit_of_weight :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → IsAffineHom q.left → ∀ (χ : X) (b : B.left), ∃ (V : B.left.Opens) (_ : b ∈ V) (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ), ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)), (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val = t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val := by
  intro S X _ G B _ _ q i _ _ _ _ _ hi _ χ b
  obtain ⟨V, hV, hbV, -⟩ := exists_isAffineOpen_mem_and_subset (x := b) (U := ⊤) trivial
  have hU : IsAffineOpen (q.left ⁻¹ᵁ V) := hV.preimage q.left
  obtain ⟨ρ, hρ⟩ := exists_coaction hi hU
  have htor : ∀ (R : Type) [CommRing R], IsTorsorOn R (q.left.appLE V _ le_rfl).hom ρ :=
    fun R _ => (isTorsorOn hi hV hU hρ (Spec (.of R))).of_equiv
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  obtain ⟨p, rfl⟩ := hV.range_fromSpec.ge hbV
  obtain ⟨a, ha, c, c', hcc, hc⟩ := exists_homogeneous (faithfullyFlat_appLE q.left hV hU) htor χ
    p.asIdeal p.isPrime.ne_top
  have hle : q.left ⁻¹ᵁ B.left.basicOpen a ≤ q.left ⁻¹ᵁ V :=
    fun _ hx => B.left.basicOpen_le a hx
  let r := (G.left.presheaf.map (homOfLE hle).op).hom
  have hunit : IsUnit (r c) := by
    apply isUnit_of_mul_isUnit_left (y := r c')
    rw [← map_mul, hcc]
    have h1 := (B.left.toRingedSpace.isUnit_res_basicOpen a).map
      (q.left.app (B.left.basicOpen a)).hom
    have h2 := q.left.appLE_map (U := V) le_rfl (homOfLE hle).op
    have h3 := q.left.map_appLE (V := q.left ⁻¹ᵁ B.left.basicOpen a) le_rfl
      (homOfLE (B.left.basicOpen_le a)).op
    have h4 := congr($(h2.trans h3.symm).hom a)
    rw [Scheme.Hom.app_eq_appLE] at h1
    exact h4 ▸ h1
  have hr : ∀ {Z : Scheme.{0}} (g : Z ⟶ G.left) (θ) (_ : g = pt hU θ)
      (h : ⊤ ≤ g ⁻¹ᵁ q.left ⁻¹ᵁ B.left.basicOpen a), (g.appLE _ ⊤ h).hom (r c) = θ c := by
    rintro Z g θ rfl h
    have h1 := congr($((pt hU θ).map_appLE h (homOfLE hle).op).hom c)
    rw [pt_appLE] at h1
    exact h1
  refine ⟨B.left.basicOpen a, ?_, hunit.unit, fun Z t g h₁ h₂ => ?_⟩
  · have : p ∈ hV.fromSpec ⁻¹ᵁ B.left.basicOpen a := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact ha
    exact this
  · obtain ⟨θ, hθ⟩ := exists_eq_pt hU g.left (h₂.trans fun _ hx => hle hx)
    rw [IsUnit.unit_spec, hr _ _ (hρ Z t g θ hθ), hr _ _ hθ, RingHom.comp_apply, hc, ev_single,
      toHom_val, coord_single, mul_comm]

end GlobalTheory
