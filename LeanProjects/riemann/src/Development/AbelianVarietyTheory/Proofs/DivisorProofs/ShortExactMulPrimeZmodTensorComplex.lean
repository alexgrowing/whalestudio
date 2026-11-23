import Mathlib
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory

abbrev pMultiples (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M)

lemma zmultiples_mkQ_p (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    zmultiplesHom (M →+ M ⧸ pMultiples p M) (pMultiples p M).mkQ.toAddMonoidHom (p : ℤ) = 0 := by
  ext m
  simp only [zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.zero_apply]
  show (p : ℤ) • Submodule.Quotient.mk m = (0 : M ⧸ pMultiples p M)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨m, by simp⟩

def modPPairing (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    ZMod p →+ M →+ (M ⧸ pMultiples p M) :=
  ZMod.lift p ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩

lemma modPPairing_one (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] (m : M) :
    modPPairing p M 1 m = Submodule.Quotient.mk m := by
  have h := ZMod.lift_coe p (A := M →+ (M ⧸ pMultiples p M))
    ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩ 1
  simp only [Int.cast_one] at h
  unfold modPPairing
  rw [h]
  simp

abbrev zmodOverInt (p : ℕ) : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of (ZMod p) (ZMod p))

def tensorToModP (p : ℕ) (M : ModuleCat.{0} ℤ) :
    TensorProduct ℤ (zmodOverInt p) M →+ (M ⧸ pMultiples p M) :=
  TensorProduct.liftAddHom (modPPairing p M) (fun r a m => by
    have key : ∀ b : ZMod p, modPPairing p M ((r : ZMod p) * b) m = r • modPPairing p M b m := by
      intro b
      rw [← zsmul_eq_mul, map_zsmul]
      rfl
    refine (key a).trans ?_
    rw [← map_zsmul]
    congr 1
    exact (int_smul_eq_zsmul _ r m).symm)

lemma tensorToModP_unit (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  unfold tensorToModP
  exact (TensorProduct.liftAddHom_tmul _ _ _ _).trans (modPPairing_one p M m)

end GlobalTheory

end

noncomputable section

namespace GlobalTheory

def oneZ (p : ℕ) : zmodOverInt p := (1 : ZMod p)

lemma oneZ_tmul_surjective (p : ℕ) (M : ModuleCat.{0} ℤ) :
    ∀ t : TensorProduct ℤ (zmodOverInt p) M, ∃ m : M, oneZ p ⊗ₜ[ℤ] m = t := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, TensorProduct.tmul_zero _ _⟩
  | tmul a m =>
    obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := p) a
    have h1 := map_zsmul (AddMonoidHom.mk' (fun x : M => oneZ p ⊗ₜ[ℤ] x) (TensorProduct.tmul_add _)) k m
    have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] m)
      (fun b c => TensorProduct.add_tmul b c m)) k (oneZ p)
    refine ⟨_, (h1.trans h2.symm).trans (congrArg (fun x => x ⊗ₜ[ℤ] m) ?_)⟩
    show (k • (1 : ZMod p) : ZMod p) = a
    rw [zsmul_one]
    exact hk
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, (TensorProduct.tmul_add _ u v).trans (by rw [hu, hv])⟩

lemma unit_surjective_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by
  intro t
  obtain ⟨m, hm⟩ := oneZ_tmul_surjective p M t
  exact ⟨m, (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans hm⟩

lemma unit_kernel_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (y : M)
    (hy : ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom y = 0) :
    ∃ x : M, ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x = y := by
  have h := tensorToModP_unit p M y
  rw [hy] at h
  exact (Submodule.Quotient.mk_eq_zero _).mp (h.symm.trans (map_zero (tensorToModP p M)))

lemma oneZ_tmul_p (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    oneZ p ⊗ₜ[ℤ] ((p : ℤ) • x) = 0 := by
  have h1 := map_zsmul (AddMonoidHom.mk' (fun y : M => oneZ p ⊗ₜ[ℤ] y) (TensorProduct.tmul_add _)) (p : ℤ) x
  have h2 := map_zsmul (AddMonoidHom.mk' (fun b : zmodOverInt p => b ⊗ₜ[ℤ] x)
      (fun b c => TensorProduct.add_tmul b c x)) (p : ℤ) (oneZ p)
  refine (h1.trans h2.symm).trans ((congrArg (fun b => b ⊗ₜ[ℤ] x) ?_).trans (TensorProduct.zero_tmul _ _))
  show ((p : ℤ) • (1 : ZMod p) : ZMod p) = 0
  simp

lemma unit_pmul_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) (x : M) :
    ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom
      (((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M) x) = 0 :=
  (ModuleCat.extendRestrictScalarsAdj_unit_app_apply _ _ _).trans (oneZ_tmul_p p M x)

lemma pmul_injective (p : ℕ) (M : ModuleCat.{0} ℤ) (h : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Function.Injective (ConcreteCategory.hom ((p : ℤ) • 𝟙 M)) := by
  intro a b hab
  have hab' : (p : ℤ) • a = (p : ℤ) • b := hab
  apply sub_eq_zero.mp
  apply h
  rw [zsmul_sub, hab', sub_self]

theorem shortExact_mul_p_modP :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by
  intro C p _ hinj
  let π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C) :=
    { f := fun n => (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app (C.X n)
      comm' := fun i j _ =>
        ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.naturality (C.d i j)) }
  have hz : ((p : ℤ) • 𝟙 C) ≫ π = 0 := by
    ext n x
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f,
      ModuleCat.hom_comp, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact unit_pmul_zmod p (C.X n) x
  refine ⟨π, hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  apply ShortComplex.ShortExact.mk'
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    simp only [ShortComplex.map_f, ShortComplex.map_g, HomologicalComplex.eval_map,
      HomologicalComplex.zsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_zsmul,
      ModuleCat.hom_id] at hy ⊢
    exact unit_kernel_zmod p (C.X n) y hy
  · rw [ModuleCat.mono_iff_injective]
    exact pmul_injective p (C.X n) (hinj n)
  · rw [ModuleCat.epi_iff_surjective]
    exact unit_surjective_zmod p (C.X n)

end GlobalTheory

end
