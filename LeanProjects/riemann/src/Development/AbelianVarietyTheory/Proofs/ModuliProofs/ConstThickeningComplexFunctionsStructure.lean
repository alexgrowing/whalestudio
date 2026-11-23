import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.EpsThick

theorem existsUnique_of_isPushout {R : Type} [CommRing R] {A A' : CommRingCat.{0}} (s : R →+* A) (p : A ⟶ A')
    (s' : DualNumber R →+* A')
    (H : IsPushout (CommRingCat.ofHom s) (CommRingCat.ofHom (algebraMap R (DualNumber R))) p
      (CommRingCat.ofHom s')) :
    Function.Bijective fun ab : A × A => p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra R A := s.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber R) A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R (DualNumber R))).toAlgebra
  have : IsScalarTower R (DualNumber R) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R (DualNumber R) A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  let e : DualNumber R ⊗[R] A ≃+ A' := h.out.equiv.toAddEquiv
  have he : ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v :=
    fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)
  have key : ∀ ab : A × A, p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 =
      e ((1 : DualNumber R) ⊗ₜ ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ ab.2) := fun ab => by
    rw [map_add, he, he, map_one, _root_.one_mul]
  simp only [key]
  refine e.bijective.comp (f := fun ab : A × A =>
    ((1 : DualNumber R) ⊗ₜ[R] ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ[R] ab.2)) ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      ((TrivSqZeroExt.fstHom R R R).toLinearMap).rTensor A) hxy
    have h2 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      (TrivSqZeroExt.sndHom R R).rTensor A) hxy
    ext
    · simpa using h1
    · simpa using h2
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c v =>
      refine ⟨(c.fst • v, c.snd • v), ?_⟩
      dsimp only
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add]
      abel

variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}

def comb (π : Y' ⟶ Sp (DualNumber R)) (ρ : Y' ⟶ Y) (O : Y.Opens) (ab : Γ(Y, O) × Γ(Y, O)) : Γ(Y', ρ ⁻¹ᵁ O) :=
  (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2

theorem comb_bijective_of_isAffineOpen (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R))))
    {U : Y.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb π ρ U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine existsUnique_of_isPushout
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ U (fun _ _ => trivial)).hom (ρ.app U)
    ((Scheme.ΓSpecIso (.of (DualNumber R))).inv ≫ π.appLE ⊤ (ρ ⁻¹ᵁ U) (fun _ _ => trivial)).hom ?_
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp

theorem res_comb {U O : Y.Opens} (h : U ≤ O) (ab : Γ(Y, O) × Γ(Y, O)) :
    (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (comb π ρ O ab) =
      comb π ρ U ((Y.presheaf.map (homOfLE h).op).hom ab.1, (Y.presheaf.map (homOfLE h).op).hom ab.2) := by
  have h1 : ∀ a, (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom ((ρ.app O).hom a) =
      (ρ.app U).hom ((Y.presheaf.map (homOfLE h).op).hom a) := fun a =>
    (congrArg (fun φ => φ.hom a) (ρ.naturality (homOfLE h).op)).symm
  have h2 : (Y'.presheaf.map (homOfLE (ρ.preimage_mono h)).op).hom (constFn π _ DualNumber.eps) =
      constFn π (ρ ⁻¹ᵁ U) DualNumber.eps := by
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of (DualNumber R))).inv.hom DualNumber.eps))
      (π.appLE_map (U := ⊤) (V := ρ ⁻¹ᵁ O) le_top (homOfLE (ρ.preimage_mono h)).op)
  simp only [comb, map_add, map_mul, h1, h2]

theorem le_iSup_affine (O : Y.Opens) :
    O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem comb_injective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Injective (comb π ρ O) := by
  intro x y hxy
  have key : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom x.1, (Y.presheaf.map (homOfLE U.2.2).op).hom x.2) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom y.1, (Y.presheaf.map (homOfLE U.2.2).op).hom y.2) := fun U => by
    apply (comb_bijective_of_isAffineOpen H U.2.1).1
    rw [← res_comb, ← res_comb, hxy]
  ext
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.fst (key U)
  · exact Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) _ _
      fun U => congrArg Prod.snd (key U)

theorem comb_surjective (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) (O : Y.Opens) :
    Function.Surjective (comb π ρ O) := by
  intro F
  choose s hs using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (comb_bijective_of_isAffineOpen H U.2.1).2 ((Y'.presheaf.map (homOfLE (ρ.preimage_mono U.2.2)).op).hom F)
  have key : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).1,
        (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (s U).2) =
      ((Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).1,
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (s V).2) := fun U V => by
    apply comb_injective H
    rw [← res_comb, ← res_comb, hs, hs, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).1) fun U V => congrArg Prod.fst (key U V)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (s U).2) fun U V => congrArg Prod.snd (key U V)
  refine ⟨(a, b), ?_⟩
  refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
    (fun U => homOfLE (ρ.preimage_mono U.2.2)) ?_ _ _ fun U => ?_
  · rw [← Scheme.Hom.preimage_iSup]
    exact ρ.preimage_mono (le_iSup_affine O)
  · refine (res_comb U.2.2 (a, b)).trans (Eq.trans ?_ (hs U))
    exact congrArg _ (Prod.ext (ha U) (hb U))

theorem isPullback_special (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine (IsPullback.of_bot ?_ h₂.symm H.flip).flip
  have : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [h₁, this]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun r => ⟨TrivSqZeroExt.inl r, rfl⟩)]
    intro z hz
    have hz' : z.fst = 0 := hz
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have : z ^ 2 = 0 := by
      ext <;> simp [pow_two, hz']
    rw [this]
    exact zero_mem _
  exact h

theorem thickening_functions : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro Y Y' q π ρ j H h₁ h₂
  have P := isPullback_special H h₁ h₂
  refine ⟨fun O => ?_, P, fun O F => ?_⟩
  · have hj : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) P.flip surjective_spMap_fst
    ext x
    obtain ⟨y, rfl⟩ := hj.surj x
    have : ρ (j y) = y := by rw [← Scheme.Hom.comp_apply, h₁]; rfl
    change j (ρ (j y)) ∈ O ↔ j y ∈ O
    rw [this]
  · obtain ⟨ab, hab⟩ := comb_surjective H O F
    exact ⟨ab, hab.symm, fun y hy => comb_injective H O (hy.symm.trans hab.symm)⟩

end GlobalTheory.EpsThick
