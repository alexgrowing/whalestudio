import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AffDesc

open TensorProduct

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem isoPushout_desc_tmul {R0 A B : Type} [CommRing R0] [CommRing A] [CommRing B] [Algebra R0 A]
    [Algebra R0 B] {D : CommRingCat.{0}} (u : CommRingCat.of A ⟶ D) (v : CommRingCat.of B ⟶ D)
    (w : CommRingCat.ofHom (algebraMap R0 A) ≫ u = CommRingCat.ofHom (algebraMap R0 B) ≫ v) (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R0 A B).isoPushout.hom ≫ pushout.desc u v w).hom (a ⊗ₜ b) =
      u.hom a * v.hom b := by
  have e : a ⊗ₜ[R0] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul]
  have h1 := congrArg (fun φ => φ.hom a)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inl_isoPushout_hom =≫ pushout.desc u v w)
  have h2 := congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inr_isoPushout_hom =≫ pushout.desc u v w)
  simp only [Category.assoc, pushout.inl_desc, pushout.inr_desc, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem appLE_apply_appLE {X Y Y' Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (f'.appLE V' W e₂').hom ((g'.appLE U V' e₁').hom x) := by
  have a := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  have b := Scheme.Hom.appLE_comp_appLE f' g' U V' W e₁' e₂'
  have c := appLE_eq_of_eq h U W (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂ (Scheme.Hom.preimage_mono f e₁))
    (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂' (Scheme.Hom.preimage_mono f' e₁'))
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) (a.trans (c.trans b.symm))

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appTop = f.appLE ⊤ ⊤ le_top :=
  Scheme.Hom.app_eq_appLE f

end GlobalTheory.Mum.AffDesc

namespace GlobalTheory.Mum.AffDesc
open TensorProduct

theorem mem_range_app_of_flat : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ S Y Z π y p q hπ hy H r h1 h2 hP hx V hV f hf
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace S := (quasiSeparated_iff_quasiSeparatedSpace π).1 inferInstance
  haveI : CompactSpace (pullback π π : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π ≫ π)
  have hUY1 : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hUY2 : pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) = r ⁻¹ᵁ ⊤ ⊓ (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    simp [Scheme.Hom.comp_preimage]
  have i1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY1 (isAffineOpen_top _) hV isCompact_univ isQuasiSeparated_univ
  have m2 := mono_pushoutSection_of_isCompact_of_flat_right hP (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY2 (isAffineOpen_top _) hV isCompact_univ
  letI aB : Algebra Γ(Sp R, ⊤) Γ(S, ⊤) := (π.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI aA : Algebra Γ(Sp R, ⊤) Γ(Y, V) := (y.appLE ⊤ V le_top).hom.toAlgebra
  letI aC : Algebra Γ(Sp R, ⊤) Γ(pullback π π, ⊤) := ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V) := y.flat_appLE (isAffineOpen_top _) hV le_top
  let ΦB := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(S, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection H.flip (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY1
  let ΦC := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(pullback π π, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection hP (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY2
  have hB : Function.Surjective ΦB.hom := by
    have : IsIso ΦB := by dsimp only [ΦB]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso ΦB).2
  have hC : Function.Injective ΦC.hom := by
    have : Mono ΦC := by dsimp only [ΦC]; infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback ΦC).1 this
  have fB : ∀ (b : Γ(S, ⊤)) (a : Γ(Y, V)), ΦB.hom (b ⊗ₜ a) =
      (q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b * (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a :=
    fun b a => isoPushout_desc_tmul _ _ _ b a
  have fC : ∀ (c : Γ(pullback π π, ⊤)) (a : Γ(Y, V)), ΦC.hom (c ⊗ₜ a) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom c *
        ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun c a => isoPushout_desc_tmul _ _ _ c a
  have k1 : ∀ x, (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.fst π π) π ⊤ ⊤ ⊤ le_top le_top)
  have k2 : ∀ x, (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.snd π π) π ⊤ ⊤ ⊤ le_top le_top)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ x) (appLE_eq_of_eq (pullback.condition (f := π) (g := π)).symm _ _ _ _))
  let d : Γ(S, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(pullback π π, ⊤) :=
    { toFun := fun x => (pullback.fst π π).appLE ⊤ ⊤ le_top x - (pullback.snd π π).appLE ⊤ ⊤ le_top x
      map_add' := fun x x' => by simp only [map_add]; abel
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, k1, k2, RingHom.id_apply]
        ring }
  have hex : Function.Exact (Algebra.linearMap Γ(Sp R, ⊤) Γ(S, ⊤)) d := by
    intro x
    constructor
    · intro h0
      have e0 : (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x := by
        rw [appTop_eq_appLE, appTop_eq_appLE]; exact sub_eq_zero.1 h0
      obtain ⟨c, hc⟩ := hx x e0
      refine ⟨c, ?_⟩
      rw [appTop_eq_appLE] at hc
      exact hc
    · rintro ⟨c, rfl⟩
      show (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) -
        (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) = 0
      rw [k1, k2, sub_self]
  have hex' := Module.Flat.rTensor_exact Γ(Y, V) hex
  have hEq : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have c1 : ∀ b, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b) :=
    fun b => by
      rw [Scheme.Hom.app_eq_appLE]
      exact appLE_apply_appLE (pullback.fst p p) q r (pullback.fst π π) h1.symm ⊤ (p ⁻¹ᵁ V) ⊤
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) le_rfl le_top (by simp) b
  have c2 : ∀ b, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.snd π π).appLE ⊤ ⊤ le_top b) :=
    fun b => appLE_apply_appLE (pullback.snd p p) q r (pullback.snd π π) h2.symm ⊤ (p ⁻¹ᵁ V) ⊤
      (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) hEq.ge le_top (by simp) b
  have c3 : ∀ a, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => by
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun φ => CommRingCat.Hom.hom φ a)
        (Scheme.Hom.appLE_comp_appLE (pullback.fst p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl le_rfl)
  have c4 : ∀ a, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => (congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl hEq.ge)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ a) (appLE_eq_of_eq (pullback.condition (f := p) (g := p)).symm V
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) _ _))
  have key : ∀ t, ΦC.hom (d.rTensor Γ(Y, V) t) = ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom (ΦB.hom t) -
      ((pullback.snd p p).appLE _ _ hEq.ge).hom (ΦB.hom t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [LinearMap.rTensor_tmul, fC, fB, map_mul, map_mul, c1, c2, c3, c4]
      change (r.appLE _ _ _).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b - (pullback.snd π π).appLE ⊤ ⊤ le_top b) * _ = _
      rw [map_sub, sub_mul]
    | add t t' ht ht' =>
      rw [map_add, map_add, ht, ht', map_add, map_add, map_add]
      abel
  obtain ⟨t, rfl⟩ := hB f
  have hz : d.rTensor Γ(Y, V) t = 0 := hC (by rw [key, map_zero, hf hEq, sub_self])
  obtain ⟨s, rfl⟩ := (hex' t).1 hz
  clear hf hz key
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c a =>
    rw [LinearMap.rTensor_tmul, fB]
    refine ⟨(y.appLE ⊤ V le_top).hom c * a, ?_⟩
    rw [map_mul, Scheme.Hom.app_eq_appLE]
    congr 1
    exact appLE_apply_appLE p y q π H.w ⊤ V ⊤ (p ⁻¹ᵁ V) le_top le_rfl le_top (by simp) c
  | add s s' hs hs' =>
    obtain ⟨u, hu⟩ := hs
    obtain ⟨u', hu'⟩ := hs'
    exact ⟨u + u', by rw [map_add, hu, hu', map_add, map_add]⟩

end GlobalTheory.Mum.AffDesc
