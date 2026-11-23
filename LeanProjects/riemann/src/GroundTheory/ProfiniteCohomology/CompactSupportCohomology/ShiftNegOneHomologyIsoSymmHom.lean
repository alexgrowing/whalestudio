import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.HomApplyHomApplyEqOfCompEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Shift

variable (L : CochainComplex (ModuleCat.{u} k) ℕ)

noncomputable def shiftNegOneSuccHom (n : ℕ) : L.X n ⟶ (shiftNegOne L).X (n + 1) :=
  ModuleCat.ofHom (shiftNegOneSucc L n)

instance (n : ℕ) : IsIso (shiftNegOneSuccHom L n) :=
  (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

theorem shiftNegOne_d_succ_hom_apply (n : ℕ) (y : L.X n) :
    ((shiftNegOne L).d (n + 1) (n + 1 + 1)).hom (shiftNegOneSucc L n y) =
      shiftNegOneSucc L (n + 1) (-(L.d n (n + 1)).hom y) := by
  rw [shiftNegOne_d]
  rfl

@[reassoc]
theorem shiftNegOneSuccHom_d (n : ℕ) :
    shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      -(L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)) :=
  ModuleCat.hom_ext (LinearMap.ext fun y => shiftNegOne_d_succ_hom_apply L n y)

def prevNat : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

theorem up_prev_eq_prevNat (n : ℕ) : (ComplexShape.up ℕ).prev n = prevNat n := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

noncomputable def shiftNegOneτ₁ : ∀ n, L.X (prevNat n) ⟶ (shiftNegOne L).X n
  | 0 => 0
  | n + 1 => -shiftNegOneSuccHom L n

noncomputable def shiftNegOneψ (n : ℕ) :
    L.sc' (prevNat n) n (n + 1) ⟶ (shiftNegOne L).sc' n (n + 1) (n + 1 + 1) where
  τ₁ := shiftNegOneτ₁ L n
  τ₂ := shiftNegOneSuccHom L n
  τ₃ := -shiftNegOneSuccHom L (n + 1)
  comm₁₂ := by
    cases n with
    | zero =>
      change (0 : L.X 0 ⟶ (shiftNegOne L).X 0) ≫ (shiftNegOne L).d 0 (0 + 1) =
        L.d 0 0 ≫ shiftNegOneSuccHom L 0
      rw [L.shape 0 0 (by simp), zero_comp, zero_comp]
    | succ n =>
      change (-shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
        L.d n (n + 1) ≫ shiftNegOneSuccHom L (n + 1)
      rw [Preadditive.neg_comp, shiftNegOneSuccHom_d, neg_neg]
  comm₂₃ := by
    change shiftNegOneSuccHom L n ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) =
      L.d n (n + 1) ≫ (-shiftNegOneSuccHom L (n + 1))
    rw [shiftNegOneSuccHom_d, Preadditive.comp_neg]

theorem epi_shiftNegOneτ₁ (n : ℕ) : Epi (shiftNegOneτ₁ L n) := by
  cases n with
  | zero => exact (ModuleCat.epi_iff_surjective _).2 fun (_ : PUnit) => ⟨0, rfl⟩
  | succ n =>
    refine (ModuleCat.epi_iff_surjective _).2 fun (y : L.X n) => ⟨-y, ?_⟩
    change -(-y) = y
    exact neg_neg y

theorem mono_neg_shiftNegOneSuccHom (n : ℕ) : Mono (-shiftNegOneSuccHom L n) :=
  (ModuleCat.mono_iff_injective _).2 fun (a b : L.X n) h => by
    have h' : -a = -b := h
    exact neg_injective h'

noncomputable def shiftNegOneHomologyHom (n : ℕ) :
    L.homology n ⟶ (shiftNegOne L).homology (n + 1) :=
  (L.homologyIsoSc' (prevNat n) n (n + 1) (up_prev_eq_prevNat n) (CochainComplex.next ℕ n)).hom ≫
    ShortComplex.homologyMap (shiftNegOneψ L n) ≫
    ((shiftNegOne L).homologyIsoSc' n (n + 1) (n + 1 + 1) (CochainComplex.prev_nat_succ n)
      (CochainComplex.next ℕ (n + 1))).inv

instance isIso_shiftNegOneHomologyHom (n : ℕ) : IsIso (shiftNegOneHomologyHom L n) := by
  have := ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' (shiftNegOneψ L n)
    (epi_shiftNegOneτ₁ L n) (inferInstanceAs (IsIso (shiftNegOneSuccHom L n)))
    (mono_neg_shiftNegOneSuccHom L (n + 1))
  unfold shiftNegOneHomologyHom
  infer_instance

noncomputable def shiftNegOneHomologyIso (n : ℕ) :
    (shiftNegOne L).homology (n + 1) ≅ L.homology n :=
  (asIso (shiftNegOneHomologyHom L n)).symm

@[simp]
theorem shiftNegOneHomologyIso_inv (n : ℕ) :
    (shiftNegOneHomologyIso L n).inv = shiftNegOneHomologyHom L n :=
  rfl

@[simp]
theorem shiftNegOneHomologyIso_symm_hom (n : ℕ) :
    (shiftNegOneHomologyIso L n).symm.hom = shiftNegOneHomologyHom L n :=
  rfl

theorem iCycles_shiftNegOneSuccHom_d (n : ℕ) :
    (L.iCycles n ≫ shiftNegOneSuccHom L n) ≫ (shiftNegOne L).d (n + 1) (n + 1 + 1) = 0 := by
  rw [Category.assoc, shiftNegOneSuccHom_d, Preadditive.comp_neg, L.iCycles_d_assoc, zero_comp,
    neg_zero]

@[reassoc]
theorem homologyπ_shiftNegOneHomologyHom (n : ℕ) :
    L.homologyπ n ≫ shiftNegOneHomologyHom L n =
      (shiftNegOne L).liftCycles (L.iCycles n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (iCycles_shiftNegOneSuccHom_d L n) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
  rw [shiftNegOneHomologyHom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    HomologicalComplex.liftCycles_i]
  rw [← HomologicalComplex.cyclesIsoSc'_hom_iCycles L (prevNat n) n (n + 1) (up_prev_eq_prevNat n)
    (CochainComplex.next ℕ n)]
  exact (congrArg (_ ≫ ·) (ShortComplex.cyclesMap_i (shiftNegOneψ L n))).trans
    (Category.assoc _ _ _).symm

end Shift

namespace mappingCoconeNat

variable {K L : CochainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L)

@[reassoc (attr := simp)]
theorem inr_fst : inr f ≫ fst f = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

noncomputable abbrev shortComplex : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (inr f) (fst f) (inr_fst f)

theorem shortExact : (shortComplex f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => {
    exact := by
      rw [ShortComplex.moduleCat_exact_iff]
      intro (p : K.X n × shiftNegOneX L n) hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
    mono_f := (ModuleCat.mono_iff_injective _).2 fun _ _ h => congrArg Prod.snd h
    epi_g := (ModuleCat.epi_iff_surjective _).2 fun (x : K.X n) => ⟨((x, 0) : K.X n × _), rfl⟩ }

noncomputable def inlX (n : ℕ) : K.X n ⟶ (mappingCoconeNat f).X n :=
  ModuleCat.ofHom (LinearMap.inl k (K.X n) (shiftNegOneX L n))

@[reassoc (attr := simp)]
theorem inlX_fst (n : ℕ) : inlX f n ≫ (fst f).f n = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

theorem inlX_d (n : ℕ) :
    inlX f n ≫ (mappingCoconeNat f).d n (n + 1) =
      K.d n (n + 1) ≫ inlX f (n + 1) + f.f n ≫ shiftNegOneSuccHom L n ≫ (inr f).f (n + 1) := by
  rw [mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Prod.ext ?_ ?_)
  · change (K.d n (n + 1)).hom x = (K.d n (n + 1)).hom x + 0
    rw [add_zero]
  · change shiftNegOneSucc L n ((f.f n).hom x) + (shiftNegOneD L n).hom 0 =
      0 + shiftNegOneSucc L n ((f.f n).hom x)
    rw [map_zero, add_zero, zero_add]

theorem δ_eq (n : ℕ) :
    (shortExact f).δ n (n + 1) rfl =
      HomologicalComplex.homologyMap f n ≫ shiftNegOneHomologyHom L n := by
  refine (cancel_epi (K.homologyπ n)).1 ?_
  have h := (shortExact f).δ_eq n (n + 1) rfl (K.iCycles n) (K.iCycles_d n (n + 1))
    (K.iCycles n ≫ inlX f n) (by
      change (K.iCycles n ≫ inlX f n) ≫ (fst f).f n = K.iCycles n
      rw [Category.assoc, inlX_fst, Category.comp_id])
    (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (by
      change (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) ≫ (inr f).f (n + 1) =
        (K.iCycles n ≫ inlX f n) ≫ (mappingCoconeNat f).d n (n + 1)
      simp only [Category.assoc]
      rw [inlX_d, Preadditive.comp_add, K.iCycles_d_assoc, zero_comp, zero_add])
    (n + 1 + 1) (CochainComplex.next ℕ (n + 1))
  have hl : K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) =
      𝟙 _ := by
    rw [← cancel_mono (K.iCycles n), HomologicalComplex.liftCycles_i, Category.id_comp]
  have h2 : K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
      (shiftNegOne L).liftCycles (K.iCycles n ≫ f.f n ≫ shiftNegOneSuccHom L n) (n + 1 + 1)
        (CochainComplex.next ℕ (n + 1)) (by
          rw [← HomologicalComplex.cyclesMap_i_assoc, Category.assoc,
            iCycles_shiftNegOneSuccHom_d, comp_zero]) ≫
        (shiftNegOne L).homologyπ (n + 1) := by
    calc K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl =
        K.liftCycles (K.iCycles n) (n + 1) (CochainComplex.next ℕ n) (K.iCycles_d n (n + 1)) ≫
          K.homologyπ n ≫ (shortExact f).δ n (n + 1) rfl := by rw [hl, Category.id_comp]
      _ = _ := h
  rw [h2, HomologicalComplex.homologyπ_naturality_assoc, homologyπ_shiftNegOneHomologyHom]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L).iCycles (n + 1))]
  simp only [Category.assoc, HomologicalComplex.liftCycles_i, HomologicalComplex.cyclesMap_i_assoc]

noncomputable def homologyδ (n : ℕ) : L.homology n ⟶ (mappingCoconeNat f).homology (n + 1) :=
  shiftNegOneHomologyHom L n ≫ HomologicalComplex.homologyMap (inr f) (n + 1)

@[reassoc (attr := simp)]
theorem homologyMap_homologyδ (n : ℕ) :
    HomologicalComplex.homologyMap f n ≫ homologyδ f n = 0 := by
  rw [homologyδ, ← Category.assoc, ← δ_eq]
  exact (shortExact f).δ_comp n (n + 1) rfl

@[reassoc (attr := simp)]
theorem homologyδ_homologyMap_fst (n : ℕ) :
    homologyδ f n ≫ HomologicalComplex.homologyMap (fst f) (n + 1) = 0 := by
  rw [homologyδ, Category.assoc, ← HomologicalComplex.homologyMap_comp, inr_fst,
    HomologicalComplex.homologyMap_zero, comp_zero]

@[reassoc (attr := simp)]
theorem homologyMap_fst_homologyMap (n : ℕ) :
    HomologicalComplex.homologyMap (fst f) n ≫ HomologicalComplex.homologyMap f n = 0 := by
  rw [← cancel_mono (shiftNegOneHomologyHom L n), Category.assoc, ← δ_eq, zero_comp]
  exact (shortExact f).comp_δ n (n + 1) rfl

theorem homology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_homologyδ f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₁ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (shiftNegOneHomologyIso L n).symm (Iso.refl _)
    (by simp [δ_eq]) (by simp [homologyδ])

theorem homology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyδ_homologyMap_fst f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₂ (n + 1))
  exact ShortComplex.isoMk (shiftNegOneHomologyIso L n).symm (Iso.refl _) (Iso.refl _)
    (by simp [homologyδ]) (by simp)

theorem homology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_fst_homologyMap f n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 ((shortExact f).homology_exact₃ n (n + 1) rfl)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (shiftNegOneHomologyIso L n).symm
    (by simp) (by simp [δ_eq])

theorem mono_homologyMap_fst_zero : Mono (HomologicalComplex.homologyMap (fst f) 0) := by
  have hz : IsZero ((shiftNegOne L).homology 0) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k PUnit))
  exact ((shortExact f).homology_exact₂ 0).mono_g (hz.eq_of_src _ _)

end mappingCoconeNat

end GroundTheory.ProfCoh
