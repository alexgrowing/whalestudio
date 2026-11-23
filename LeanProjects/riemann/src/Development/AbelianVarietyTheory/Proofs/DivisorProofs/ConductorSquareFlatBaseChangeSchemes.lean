import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem inj_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : f.Flat) (hg : Function.Injective g) : Function.Injective h := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  haveI : Module.Flat A F := hf
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  rw [injective_iff_map_eq_zero]
  intro x hx
  have e1 : Algebra.IsPushout.equiv A B F G ((1 : B) ⊗ₜ x) = 0 := by
    rw [Algebra.IsPushout.equiv_tmul]; simpa [RingHom.algebraMap_toAlgebra] using hx
  have e2 : ((1 : B) ⊗ₜ[A] x) = 0 := by
    simpa using (Algebra.IsPushout.equiv A B F G).injective (e1.trans (map_zero _).symm)
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap A B) hg
  have e3 : LinearMap.rTensor F (Algebra.linearMap A B) ((1 : A) ⊗ₜ x) = 0 := by simpa using e2
  have e4 : ((1 : A) ⊗ₜ[A] x) = 0 := hinj (e3.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid A F) e4

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem ideal_mul_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (J : Ideal A) (hJ : ∀ a ∈ J, ∀ b : B, ∃ a' ∈ J, g a' = g a * b) :
    ∀ x ∈ J.map f, ∀ r : G, ∃ y ∈ J.map f, h y = h x * r := by
  have hw : ∀ a, k (g a) = h (f a) := fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa using this.symm
  have hQ : ∀ x ∈ J.map f, ∀ b : B, ∃ y ∈ J.map f, h y = h x * k b := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro b
      obtain ⟨a', ha', e⟩ := hJ a ha b
      refine ⟨f a', Ideal.mem_map_of_mem f ha', ?_⟩
      rw [← hw, ← hw, e, map_mul]
    | zero => intro b; exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add z w _ _ hz hw' =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      obtain ⟨y2, hy2, e2⟩ := hw' b
      exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add, e1, e2, map_add, add_mul]⟩
    | smul m z _ hz =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      refine ⟨m * y1, Ideal.mul_mem_left _ m hy1, ?_⟩
      rw [smul_eq_mul, map_mul, e1, map_mul]; ring
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => (hw a).symm)
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  intro x hx r
  induction r using hP'.out.inductionOn with
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | tmul m =>
    refine ⟨x * m, Ideal.mul_mem_right _ _ hx, ?_⟩
    rw [map_mul]; rfl
  | smul b n hn =>
    obtain ⟨y1, hy1, e1⟩ := hn
    obtain ⟨y, hy, e⟩ := hQ y1 hy1 b
    refine ⟨y, hy, ?_⟩
    rw [e, e1, Algebra.smul_def, RingHom.algebraMap_toAlgebra]; ring
  | add n1 n2 h1 h2 =>
    obtain ⟨y1, hy1, e1⟩ := h1
    obtain ⟨y2, hy2, e2⟩ := h2
    exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add, e1, e2, mul_add]⟩

theorem ker_le_of_isPushout {A Q F G : Type} [CommRing A] [CommRing Q] [CommRing F] [CommRing G]
    (f : A →+* F) (q : A →+* Q) (h : F →+* G) (k : Q →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom q) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hq : Function.Surjective q) (x : F) (hx : h x = 0) : x ∈ (RingHom.ker q).map f := by
  letI := f.toAlgebra
  letI := q.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A Q G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  have hP : Algebra.IsPushout A F Q G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hs : Function.Surjective (Algebra.ofId A Q) := hq
  let e1 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot F (RingHom.ker (Algebra.ofId A Q))
  let e2 : F ⊗[A] (A ⧸ RingHom.ker (Algebra.ofId A Q)) ≃ₐ[A] F ⊗[A] Q :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hs)
  let e3 := Algebra.IsPushout.equiv A F Q G
  have key : e3 (e2 (e1 (Ideal.Quotient.mk _ x))) = 0 := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp only [e2, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, map_one]
    rw [Algebra.IsPushout.equiv_tmul]
    simpa [RingHom.algebraMap_toAlgebra] using hx
  have : Ideal.Quotient.mk (Ideal.map (algebraMap A F) (RingHom.ker (Algebra.ofId A Q))) x = 0 := by
    apply e1.injective; apply e2.injective; apply e3.injective
    rw [key]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

theorem spMap_appLE_apply {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom (((spMap φ).appLE ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ e = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  have := congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [h1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem cond_of_flat (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r)
    (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c))
    (hu : Flat u) (hp : IsPullback p u' u (spMap (algebraMap R R')))
    (hi : IsPullback i v u (spMap (Ideal.Quotient.mk c))) : GlobalTheory.Pinch.Cond p i := by
  intro W hW
  have poP := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := W) (UY := p ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have poZ := (isIso_pushoutSection_iff hi (US := ⊤) (UT := ⊤) (UX := W) (UY := i ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hi _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have hfl : (u.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) u hu ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eR' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
  let eQ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).commRingCatIsoToRingEquiv
  let gA := ((spMap (algebraMap R R')).appLE ⊤ ⊤ le_top).hom
  let qA := ((spMap (Ideal.Quotient.mk c)).appLE ⊤ ⊤ le_top).hom
  have hg : ∀ a, eR' (gA a) = algebraMap R R' (eR a) := fun a => spMap_appLE_apply _ _ a
  have hq : ∀ a, eQ (qA a) = Ideal.Quotient.mk c (eR a) := fun a => spMap_appLE_apply _ _ a
  have gA_inj : Function.Injective gA := by
    intro a b hab
    apply eR.injective; apply hinj
    rw [← hg, ← hg, hab]
  have qA_surj : Function.Surjective qA := by
    intro t
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (eQ t)
    refine ⟨eR.symm z, eQ.injective ?_⟩
    rw [hq, RingEquiv.apply_symm_apply, hz]
  let J := RingHom.ker qA
  have hJ : ∀ a ∈ J, ∀ b, ∃ a' ∈ J, gA a' = gA a * b := by
    intro a ha b
    have hx : eR a ∈ c := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, RingHom.mem_ker.1 ha, map_zero]
    obtain ⟨y, hy, e⟩ := hc (eR a) hx (eR' b)
    refine ⟨eR.symm y, ?_, eR'.injective ?_⟩
    · rw [RingHom.mem_ker]; apply eQ.injective
      rw [hq, RingEquiv.apply_symm_apply, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hy
    · rw [hg, RingEquiv.apply_symm_apply, e, map_mul, hg]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.app_eq_appLE]
    exact inj_of_isPushout _ _ _ _ poP hfl gA_inj
  · intro x hx r
    rw [Scheme.Hom.app_eq_appLE] at hx
    have hxJ := ker_le_of_isPushout _ _ _ _ poZ qA_surj x hx
    obtain ⟨y, hy, e⟩ := ideal_mul_of_isPushout _ _ _ _ poP J hJ x hxJ r
    refine ⟨y, ?_, ?_⟩
    · rw [Scheme.Hom.app_eq_appLE]
      have hle : J.map (u.appLE ⊤ W le_top).hom ≤ RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) poZ.w
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        have h0 : qA a = 0 := RingHom.mem_ker.1 ha
        simp only [qA] at h0
        rw [this, h0, map_zero]
      exact hle hy
    · rw [Scheme.Hom.app_eq_appLE]; exact e

end GlobalTheory.Pinch.FlatSq
