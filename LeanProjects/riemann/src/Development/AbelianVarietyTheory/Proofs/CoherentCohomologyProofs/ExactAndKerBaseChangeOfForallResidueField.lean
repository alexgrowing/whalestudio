import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

open TensorProduct Function

namespace GlobalTheory

section LinearAlgebra

variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]

theorem exact_lTensor_iff_of_faithfullyFlat (k L : Type*) [CommRing k] [CommRing L] [Algebra R k]
    [Algebra R L] [Algebra k L] [IsScalarTower R k L] [Module.FaithfullyFlat k L]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔ Exact (f.lTensor k) (g.lTensor k) := by
  have h1 := Module.FaithfullyFlat.lTensor_exact_iff_exact k L (f.baseChange k) (g.baseChange k)
  have h2 : Exact (AlgebraTensorModule.lTensor k L f) (AlgebraTensorModule.lTensor k L g) ↔
      Exact ((f.baseChange k).lTensor L) ((g.baseChange k).lTensor L) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R k k L A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R k k L B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R k k L C)
      (by ext; simp) (by ext; simp)
  exact h2.trans h1

theorem exact_lTensor_iff_residueField (p : Ideal R) [p.IsPrime] (L : Type*) [Field L]
    [Algebra R L] (hL : RingHom.ker (algebraMap R L) = p) (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Exact (f.lTensor L) (g.lTensor L) ↔
      Exact (f.lTensor p.ResidueField) (g.lTensor p.ResidueField) := by
  let φ : p.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ p (Algebra.ofId R L) hL.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hL ▸ h0))
  letI : Algebra p.ResidueField L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R p.ResidueField L :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exact_lTensor_iff_of_faithfullyFlat p.ResidueField L f g

theorem split_injective_of_forall_lTensor_residueField_injective [Module.Finite R B]
    [Module.Finite R C] [Module.Projective R C] (l : B →ₗ[R] C)
    (h : ∀ (m : Ideal R) [m.IsMaximal], Injective (l.lTensor m.ResidueField)) :
    ∃ r : C →ₗ[R] B, r ∘ₗ l = LinearMap.id := by
  have hloc : ∀ (m : Ideal R) [m.IsMaximal], Injective ((l.baseChange (Localization.AtPrime m)).lTensor
      (IsLocalRing.ResidueField (Localization.AtPrime m))) := by
    intro m _
    have e : (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime m)
          (Localization.AtPrime m) m.ResidueField C) ∘
          ((l.baseChange (Localization.AtPrime m)).lTensor m.ResidueField) =
        (l.lTensor m.ResidueField) ∘ (AlgebraTensorModule.cancelBaseChange R
          (Localization.AtPrime m) (Localization.AtPrime m) m.ResidueField B) := by
      funext x
      exact (LinearMap.congr_fun (AlgebraTensorModule.lTensor_comp_cancelBaseChange R
        (Localization.AtPrime m) (Localization.AtPrime m) (M := m.ResidueField) l) x).symm
    exact Injective.of_comp (e ▸ (h m).comp (LinearEquiv.injective _))
  have hfree : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] C) := fun m _ =>
    Module.free_of_flat_of_isLocalRing
  have hinj : Injective l := by
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    refine Module.subsingleton_of_localization_maximal (R := R)
      (fun m _ => Localization.AtPrime m ⊗[R] LinearMap.ker l)
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    obtain ⟨r, hr⟩ := (IsLocalRing.split_injective_iff_lTensor_residueField_injective _).2 (hloc m)
    have h1 : Injective (l.lTensor (Localization.AtPrime m)) :=
      HasLeftInverse.injective ⟨r, LinearMap.congr_fun hr⟩
    have h2 : Injective ((LinearMap.ker l).subtype.lTensor (Localization.AtPrime m)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine (subsingleton_iff_forall_eq 0).2 fun y => h2 (h1 ?_)
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  have : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  have : Module.FinitePresentation R (C ⧸ LinearMap.range l) :=
    Module.finitePresentation_of_surjective (LinearMap.range l).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map l)
  have : Module.Projective R (C ⧸ LinearMap.range l) := by
    refine Module.projective_of_localization_maximal' (fun m _ => Localization.AtPrime m)
      (fun m _ => Localization.AtPrime m ⊗[R] (C ⧸ LinearMap.range l))
      (fun m _ => TensorProduct.mk R (Localization.AtPrime m) _ 1) (fun m _ => ?_)
    have := Module.free_of_lTensor_residueField_injective
      (l.baseChange (Localization.AtPrime m))
      ((LinearMap.range l).mkQ.baseChange (Localization.AtPrime m))
      (LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _))
      (lTensor_exact _ l.exact_map_mkQ_range (Submodule.mkQ_surjective _)) (hloc m)
    infer_instance
  have := (Exact.split_tfae l.exact_map_mkQ_range hinj (Submodule.mkQ_surjective _)).out 0 1
  rw [← this]
  exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

theorem lTensor_liftQ_injective_of_exact (N : Type*) [AddCommGroup N] [Module R N]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : LinearMap.range f ≤ LinearMap.ker g)
    (h : Exact (f.lTensor N) (g.lTensor N)) :
    Injective (((LinearMap.range f).liftQ g hfg).lTensor N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective N (Submodule.mkQ_surjective _) x
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ] at hx
  obtain ⟨z, rfl⟩ := (h y).1 hx
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    f.exact_map_mkQ_range.linearMap_comp_eq_zero, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem exists_homotopy_of_forall_exact_residueField [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField)) :
    ∃ (s : B →ₗ[R] A) (t : C →ₗ[R] B), f ∘ₗ s + t ∘ₗ g = LinearMap.id := by
  have hle : LinearMap.range f ≤ LinearMap.ker g := LinearMap.range_le_ker_iff.2 hfg
  obtain ⟨r, hr⟩ := split_injective_of_forall_lTensor_residueField_injective
    ((LinearMap.range f).liftQ g hle) fun m _ => lTensor_liftQ_injective_of_exact _ hle (h m)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property (LinearMap.range f).mkQ r
    (Submodule.mkQ_surjective _)
  have hmem : ∀ b, (LinearMap.id - t ∘ₗ g : B →ₗ[R] B) b ∈ LinearMap.range f := by
    intro b
    have h1 := LinearMap.congr_fun ht (g b)
    have h2 := LinearMap.congr_fun hr (Submodule.Quotient.mk b)
    simp only [LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.mkQ_apply,
      LinearMap.id_apply] at h1 h2
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, ← Submodule.Quotient.eq,
      h1, h2]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f.rangeRestrict
    (LinearMap.codRestrict _ _ hmem) f.surjective_rangeRestrict
  refine ⟨s, t, LinearMap.ext fun b => ?_⟩
  have := congrArg Subtype.val (LinearMap.congr_fun hs b)
  simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.rangeRestrict] at this
  simp [this]

theorem forall_exact_residueField_of_isLocalRing [IsLocalRing R] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Exact (f.lTensor (IsLocalRing.ResidueField R)) (g.lTensor (IsLocalRing.ResidueField R)))
    (m : Ideal R) [m.IsMaximal] :
    Exact (f.lTensor m.ResidueField) (g.lTensor m.ResidueField) :=
  (exact_lTensor_iff_residueField m (IsLocalRing.ResidueField R)
    (IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal ‹_›).symm) f g).1 h

theorem exact_of_homotopy {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by
  intro x
  constructor
  · intro hx
    refine ⟨s x, ?_⟩
    simpa [hx] using LinearMap.congr_fun h x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hfg y

end LinearAlgebra

section Comparison

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D]

section ShortComplex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]

noncomputable def shortCyclesComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] : F.obj S.cycles ⟶ (S.map F).cycles :=
  (S.map F).liftCycles (F.map S.iCycles) (by
    rw [ShortComplex.map_g, ← F.map_comp, S.iCycles_g, F.map_zero])

@[reassoc (attr := simp)]
theorem shortCyclesComparison_iCycles (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    shortCyclesComparison F S ≫ (S.map F).iCycles = F.map S.iCycles :=
  ShortComplex.liftCycles_i _ _ _

@[reassoc (attr := simp)]
theorem map_toCycles_shortCyclesComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    F.map S.toCycles ≫ shortCyclesComparison F S = (S.map F).toCycles := by
  rw [← cancel_mono (S.map F).iCycles, assoc, shortCyclesComparison_iCycles, ← F.map_comp,
    S.toCycles_i, (S.map F).toCycles_i, ShortComplex.map_f]

variable [PreservesColimitsOfShape WalkingParallelPair F]

noncomputable def shortHomologyComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] : F.obj S.homology ⟶ (S.map F).homology :=
  (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F).desc
    (CokernelCofork.ofπ (shortCyclesComparison F S ≫ (S.map F).homologyπ) (by
      rw [map_toCycles_shortCyclesComparison_assoc, ShortComplex.toCycles_comp_homologyπ]))

@[reassoc (attr := simp)]
theorem map_homologyπ_shortHomologyComparison (S : ShortComplex C) [S.HasHomology]
    [(S.map F).HasHomology] :
    F.map S.homologyπ ≫ shortHomologyComparison F S =
      shortCyclesComparison F S ≫ (S.map F).homologyπ :=
  Cofork.IsColimit.π_desc (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)

theorem epi_map_homologyπ (S : ShortComplex C) [S.HasHomology] : Epi (F.map S.homologyπ) :=
  epi_of_isColimit_cofork (CokernelCofork.mapIsColimit _ S.homologyIsCokernel F)

end ShortComplex

section Complex

variable [HasZeroMorphisms C] [HasZeroMorphisms D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.PreservesZeroMorphisms] {ι : Type*} {c : ComplexShape ι}

noncomputable def cyclesComparison (K : HomologicalComplex C c) (p : ι) :
    F.obj (K.cycles p) ⟶ ((F.mapHomologicalComplex c).obj K).cycles p :=
  shortCyclesComparison F (K.sc p)

@[reassoc (attr := simp)]
theorem cyclesComparison_iCycles (K : HomologicalComplex C c) (p : ι) :
    cyclesComparison F K p ≫ ((F.mapHomologicalComplex c).obj K).iCycles p =
      F.map (K.iCycles p) :=
  shortCyclesComparison_iCycles F (K.sc p)

variable [PreservesColimitsOfShape WalkingParallelPair F]

noncomputable def homologyComparison (K : HomologicalComplex C c) (p : ι) :
    F.obj (K.homology p) ⟶ ((F.mapHomologicalComplex c).obj K).homology p :=
  shortHomologyComparison F (K.sc p)

@[reassoc (attr := simp)]
theorem map_homologyπ_homologyComparison (K : HomologicalComplex C c) (p : ι) :
    F.map (K.homologyπ p) ≫ homologyComparison F K p =
      cyclesComparison F K p ≫ ((F.mapHomologicalComplex c).obj K).homologyπ p :=
  map_homologyπ_shortHomologyComparison F (K.sc p)

end Complex

end Comparison

section Homotopy

open CategoryTheory Category Limits

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D] {ι : Type*} {c : ComplexShape ι}

end Homotopy

section Modules

open CategoryTheory Category Limits

universe u w

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}

theorem isZero_homology_extendScalars_iff (S : Type w) [CommRing S] [inst : Algebra R S]
    (K : HomologicalComplex (ModuleCat.{u} R) c) {p q r : ι} (hp : c.prev q = p)
    (hr : c.next q = r) :
    IsZero ((((ModuleCat.extendScalars.{u, w, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology q) ↔
      Exact ((K.d p q).hom.lTensor S) ((K.d q r).hom.lTensor S) := by
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* S, φ.toAlgebra = inst := ⟨_, toAlgebra_algebraMap⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ p q r hp hr,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rfl

end Modules

section Explicit

open CategoryTheory Category Limits ChangeOfRings

universe u

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type*} {c : ComplexShape ι}

set_option backward.isDefEq.respectTransparency false in

noncomputable def tensorEquivExtendScalars (M : ModuleCat.{u} R) :
    S ⊗[R] M ≃ₗ[S] (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).obj M :=
  let e : S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) :=
    { toFun := fun s => s
      invFun := fun s => s
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => Algebra.smul_def r s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  { (TensorProduct.congr e (LinearEquiv.refl R M)).toAddEquiv with
    map_smul' := fun s x => by
      change TensorProduct.congr e (LinearEquiv.refl R M) (s • x) =
        s • TensorProduct.congr e (LinearEquiv.refl R M) x
      induction x with
      | zero => simp
      | tmul a m => rfl
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

noncomputable def homologyBaseChange (K : HomologicalComplex (ModuleCat.{u} R) c) (p : ι) :
    S ⊗[R] (K.homology p : ModuleCat R) →ₗ[S]
      ((((ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).mapHomologicalComplex c).obj
        K).homology p : ModuleCat S) :=
  (homologyComparison (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) K p).hom ∘ₗ
    (tensorEquivExtendScalars S (K.homology p)).toLinearMap

end Explicit

section Main

open CategoryTheory Category Limits

universe u

variable {R : Type u} [CommRing R]

end Main

end GlobalTheory
