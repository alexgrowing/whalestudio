import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres

open TensorProduct LinearMap

namespace GlobalTheory.FibreFlatGen

open LocalFlat

universe u

theorem rTensor_injective_of_flat_baseChange {A C B N' N : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [AddCommGroup B] [Module A B] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A N'] [Module A N]
    [IsScalarTower A C N'] [IsScalarTower A C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A).rTensor B) := by
  let e' := AlgebraTensorModule.cancelBaseChange A C C N' B
  let e := AlgebraTensorModule.cancelBaseChange A C C N B
  have h1 : Function.Injective (ι.rTensor (C ⊗[A] B)) :=
    Module.Flat.rTensor_preserves_injective_linearMap ι hι
  have key : ∀ z, (ι.restrictScalars A).rTensor B (e' z) = e (ι.rTensor (C ⊗[A] B) z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n t =>
      induction t with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem rTensor_injective_of_flat {A B L N' N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup L] [Module A L] [Module B L] [IsScalarTower A B L] [Module.Flat B L]
    [AddCommGroup N'] [AddCommGroup N] [Module A N'] [Module A N] (ι : N' →ₗ[A] N)
    (hι : Function.Injective (ι.rTensor B)) : Function.Injective (ι.lTensor L) := by
  let e' := AlgebraTensorModule.cancelBaseChange A B B L N'
  let e := AlgebraTensorModule.cancelBaseChange A B B L N
  have hι' : Function.Injective (ι.baseChange B) := by
    have := (LinearMap.lTensor_inj_iff_rTensor_inj (M := B) ι).mpr hι
    exact this
  have h1 : Function.Injective ((ι.baseChange B).lTensor L) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hι'
  have key : ∀ z, ι.lTensor L (e' z) = e ((ι.baseChange B).lTensor L z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n t =>
      induction t with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul c b => simp [e, e']
  intro x y h
  obtain ⟨x, rfl⟩ := e'.surjective x
  obtain ⟨y, rfl⟩ := e'.surjective y
  rw [key, key] at h
  rw [h1 (e.injective h)]

theorem relationsLift_succ {R : Type*} {A : Type u} {M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Flat R M] (J : Ideal R) (k : ℕ)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor M))
    (h : RelationsLift (J.map (algebraMap R A) ^ k) M) :
    RelationsLift (J.map (algebraMap R A) ^ (k + 1)) M := by
  set I := J.map (algebraMap R A) with hI
  let C := A ⧸ I
  have hC : Function.Surjective (algebraMap A C) := Ideal.Quotient.mk_surjective
  intro F _ _ f x hx
  let P : Ideal A := I ^ k
  let G : Submodule A F := Submodule.comap f P
  obtain ⟨x₁, rfl⟩ := h F f x
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ k)) hx)
  let f' : G →ₗ[A] P := (f.domRestrict G).codRestrict P fun g => g.2
  have hPeq : P = (J ^ k).map (algebraMap R A) := by rw [Ideal.map_pow]
  have hT : Function.Injective ((TensorProduct.rid A M).toLinearMap ∘ₗ P.subtype.lTensor M) := by
    rw [hPeq]
    exact (TensorProduct.rid A M).injective.comp (FiniteFibreFlat.lTensor_map_injective (J ^ k))
  have hsub : P.subtype ∘ₗ f' = f ∘ₗ G.subtype := rfl
  have hle : I ^ (k + 1) ≤ P := Ideal.pow_le_pow_right (Nat.le_succ k)
  let incl : ↥(I ^ (k + 1)) →ₗ[A] P := Submodule.inclusion hle
  have hsurj : ∀ v ∈ (I ^ (k + 1) • ⊤ : Submodule A M), ∃ z : M ⊗[A] ↥(I ^ (k + 1)),
      TensorProduct.rid A M ((I ^ (k + 1)).subtype.lTensor M z) = v := by
    intro v hv
    refine Submodule.smul_induction_on hv (fun r hr n _ => ?_) ?_
    · exact ⟨n ⊗ₜ ⟨r, hr⟩, by simp⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp only [map_add]⟩
  obtain ⟨z, hz⟩ := hsurj _ hx
  have hy : f'.lTensor M x₁ = incl.lTensor M z := by
    apply hT
    simp only [comp_apply, LinearEquiv.coe_coe, ← lTensor_comp_apply]
    have he : P.subtype ∘ₗ incl = (I ^ (k + 1)).subtype := rfl
    rw [hsub, he, hz, lTensor_comp_apply]
  let Q := C ⊗[A] P
  let p : P →ₗ[A] Q := TensorProduct.mk A C P 1
  have hker : ∀ t : P, p t = 0 ↔ (t : A) ∈ I ^ (k + 1) := by
    intro t
    have h1 : ker p = I • (⊤ : Submodule A P) := LinearMap.ker_tensorProductMk P
    rw [← mem_ker, h1, Submodule.mem_smul_top_iff, pow_succ', smul_eq_mul]
  let g : G →ₗ[A] Q := p ∘ₗ f'
  let Pc : Submodule C Q :=
    { carrier := Set.range g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        obtain ⟨c, rfl⟩ := hC c
        exact ⟨c • a, by rw [map_smul, algebraMap_smul]⟩ }
  let g' : G →ₗ[A] Pc := g.codRestrict (Pc.restrictScalars A) fun a => ⟨a, rfl⟩
  have hg' : Function.Surjective g' := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  have hι := hinj Pc Q Pc.subtype Subtype.val_injective
  have h0 : g'.lTensor M x₁ = 0 := by
    apply hι
    rw [map_zero, ← lTensor_comp_apply]
    have e1 : (Pc.subtype.restrictScalars A) ∘ₗ g' = p ∘ₗ f' := rfl
    rw [e1, lTensor_comp_apply, hy, ← lTensor_comp_apply]
    have e2 : p ∘ₗ incl = 0 := by
      ext t
      exact (hker _).2 t.2
    rw [e2]
    simp
  have hex := lTensor_exact M (LinearMap.exact_subtype_ker_map g') hg'
  obtain ⟨w, rfl⟩ := (hex x₁).1 h0
  rw [← lTensor_comp_apply]
  refine range_lTensor_le (M := M) (G.subtype ∘ₗ (ker g').subtype) _ (fun u => ?_) ⟨w, rfl⟩
  have hu : g' u.1 = 0 := u.2
  have hu' : p (f' u.1) = 0 := congrArg Subtype.val hu
  exact (hker _).1 hu'

theorem flat_of_injective_on_fibre {R : Type*} {A : Type u} {L : Type*} [CommRing R] [CommRing A]
    [CommRing L] [Algebra R A] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    [IsNoetherianRing A] [IsNoetherianRing L] [Module.Flat R L] (J : Ideal R)
    (hJ : (J.map (algebraMap R A)).map (algebraMap A L) ≤ Ideal.jacobson ⊥)
    (hinj : ∀ (N' N : Type u) [AddCommGroup N'] [AddCommGroup N]
      [Module (A ⧸ J.map (algebraMap R A)) N'] [Module (A ⧸ J.map (algebraMap R A)) N]
      [Module A N'] [Module A N] [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N']
      [IsScalarTower A (A ⧸ J.map (algebraMap R A)) N]
      (ι : N' →ₗ[A ⧸ J.map (algebraMap R A)] N), Function.Injective ι →
        Function.Injective ((ι.restrictScalars A).lTensor L)) :
    Module.Flat A L := by
  refine flat_of_relationsLift L hJ fun n => ?_
  induction n with
  | zero =>
    intro F _ _ f x _
    exact range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
  | succ k ih => exact relationsLift_succ J k hinj ih

theorem lTensor_injective_of_fibre {A B A' L C N' N : Type} [CommRing A] [CommRing B] [CommRing A']
    [CommRing L] [CommRing C] [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [Algebra A A'] (S : Submonoid A) [IsLocalization S A'] [Algebra A' L] [IsScalarTower A A' L]
    [Algebra A' C] [Algebra A C] [IsScalarTower A A' C]
    [Module.Flat B L] [Module.Flat C (C ⊗[A] B)]
    [AddCommGroup N'] [AddCommGroup N] [Module C N'] [Module C N] [Module A' N'] [Module A' N]
    [IsScalarTower A' C N'] [IsScalarTower A' C N] (ι : N' →ₗ[C] N) (hι : Function.Injective ι) :
    Function.Injective ((ι.restrictScalars A').lTensor L) := by
  letI : Module A N' := Module.compHom N' (algebraMap A A')
  letI : Module A N := Module.compHom N (algebraMap A A')
  haveI t₁ : IsScalarTower A A' N' := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [Algebra.smul_def, mul_smul]⟩
  haveI t₂ : IsScalarTower A A' N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [Algebra.smul_def, mul_smul]⟩
  haveI t₃ : IsScalarTower A C N' := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [← smul_assoc, algebraMap_smul]⟩
  haveI t₄ : IsScalarTower A C N := ⟨fun a b n => by
    change (a • b) • n = algebraMap A A' a • b • n
    rw [← smul_assoc, algebraMap_smul]⟩
  have s₁ := rTensor_injective_of_flat_baseChange (A := A) (C := C) (B := B) ι hι
  have s₂ := rTensor_injective_of_flat (A := A) (B := B) (L := L) (ι.restrictScalars A) s₁
  haveI c₁ := IsLocalization.tensorProduct_compatibleSMul S A' L N'
  haveI c₂ := IsLocalization.tensorProduct_compatibleSMul S A' L N
  let e' := TensorProduct.equivOfCompatibleSMul A A' A' L N'
  let e := TensorProduct.equivOfCompatibleSMul A A' A' L N
  have key : ∀ z, e ((ι.restrictScalars A').lTensor L z) =
      (ι.restrictScalars A).lTensor L (e' z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul l n => rfl
  intro x y h
  apply e'.injective
  apply s₂
  rw [← key, ← key, h]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal B B (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap B _) fun P _ => ?_
  let L := Localization.AtPrime P
  let q : Ideal A := P.under A
  haveI : P.LiesOver q := ⟨rfl⟩
  let A' := Localization.AtPrime q
  letI : Algebra A' L := Localization.AtPrime.algebraOfLiesOver q P
  haveI : IsScalarTower A A' L := inferInstance
  haveI : IsScalarTower R A' L := inferInstance
  haveI : Module.Flat A A' := IsLocalization.flat A' q.primeCompl
  haveI : Module.Flat B L := IsLocalization.flat L P.primeCompl
  haveI : Module.Flat R L := .trans R B L
  haveI : IsNoetherianRing A' := IsLocalization.isNoetherianRing q.primeCompl A' inferInstance
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl L inferInstance
  haveI hl : IsLocalHom (algebraMap A' L) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q P (algebraMap A B) Ideal.LiesOver.over))
  let p : Ideal R := (IsLocalRing.maximalIdeal A').comap (algebraMap R A')
  haveI hF : Module.Flat (A' ⧸ p.map (algebraMap R A')) ((A' ⧸ p.map (algebraMap R A')) ⊗[A] B) := by
    let I := p.map (algebraMap R A')
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  haveI : Module.Flat A' L := by
    refine flat_of_injective_on_fibre p ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      have h0 : (IsLocalRing.maximalIdeal A').map (algebraMap A' L) ≤ IsLocalRing.maximalIdeal L :=
        ((IsLocalRing.local_hom_TFAE (algebraMap A' L)).out 0 2).mp hl
      exact (Ideal.map_mono Ideal.map_comap_le).trans h0
    · intro N' N _ _ _ _ _ _ _ _ ι hι
      exact lTensor_injective_of_fibre (A := A) (B := B) (A' := A') (L := L)
        (C := A' ⧸ p.map (algebraMap R A')) q.primeCompl ι hι
  exact .trans A A' L

end GlobalTheory.FibreFlatGen
