import Mathlib
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology.ShiftNegOneHomologyIsoSymmHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k : Type u} [CommRing k]

section Shift

variable {L L' L'' : CochainComplex (ModuleCat.{u} k) ℕ}

noncomputable def shiftNegOneMapF (β : L ⟶ L') : ∀ n, shiftNegOneX L n ⟶ shiftNegOneX L' n
  | 0 => 0
  | n + 1 => β.f n

theorem shiftNegOneMapF_succ_apply (β : L ⟶ L') (n : ℕ) (y : L.X n) :
    (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n y) = shiftNegOneSucc L' n ((β.f n).hom y) :=
  rfl

theorem shiftNegOneMapF_comm (β : L ⟶ L') (n : ℕ) :
    shiftNegOneMapF β n ≫ shiftNegOneD L' n = shiftNegOneD L n ≫ shiftNegOneMapF β (n + 1) := by
  cases n with
  | zero =>
    change shiftNegOneMapF β 0 ≫ 0 = 0 ≫ shiftNegOneMapF β 1
    rw [comp_zero, zero_comp]
  | succ n =>
    refine ModuleCat.hom_ext (LinearMap.ext fun (y : L.X n) => ?_)
    change -(L'.d n (n + 1)).hom ((β.f n).hom y) = (β.f (n + 1)).hom (-(L.d n (n + 1)).hom y)
    rw [map_neg, hom_apply_hom_apply_eq_of_comp_eq (β.comm n (n + 1)) y]

noncomputable def shiftNegOneMap (β : L ⟶ L') : shiftNegOne L ⟶ shiftNegOne L' :=
  CochainComplex.ofHom (shiftNegOneMapF β) fun n =>
    ((congrArg (shiftNegOneMapF β n ≫ ·) (shiftNegOne_d L' n)).trans
      (shiftNegOneMapF_comm β n)).trans
      (congrArg (· ≫ shiftNegOneMapF β (n + 1)) (shiftNegOne_d L n)).symm

@[reassoc]
theorem shiftNegOneSuccHom_shiftNegOneMap_f (β : L ⟶ L') (n : ℕ) :
    shiftNegOneSuccHom L n ≫ (shiftNegOneMap β).f (n + 1) = β.f n ≫ shiftNegOneSuccHom L' n :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem shiftNegOneMap_id : shiftNegOneMap (𝟙 L) = 𝟙 (shiftNegOne L) := by
  ext n : 1
  cases n with
  | zero => exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)
  | succ n => rfl

@[reassoc]
theorem shiftNegOneHomologyHom_naturality (β : L ⟶ L') (n : ℕ) :
    shiftNegOneHomologyHom L n ≫ HomologicalComplex.homologyMap (shiftNegOneMap β) (n + 1) =
      HomologicalComplex.homologyMap β n ≫ shiftNegOneHomologyHom L' n := by
  refine (cancel_epi (L.homologyπ n)).1 ?_
  rw [homologyπ_shiftNegOneHomologyHom_assoc, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_naturality, homologyπ_shiftNegOneHomologyHom,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc, HomologicalComplex.comp_liftCycles_assoc]
  congr 1
  rw [← cancel_mono ((shiftNegOne L').iCycles (n + 1))]
  simp only [HomologicalComplex.liftCycles_i, Category.assoc, HomologicalComplex.cyclesMap_i_assoc,
    shiftNegOneSuccHom_shiftNegOneMap_f]

end Shift

namespace mappingCoconeNat

variable {K L K' L' K'' L'' : CochainComplex (ModuleCat.{u} k) ℕ} {f : K ⟶ L} {f' : K' ⟶ L'}
  {f'' : K'' ⟶ L''}

noncomputable def mapF (α : K ⟶ K') (β : L ⟶ L') (n : ℕ) :
    (mappingCoconeNat f).X n ⟶ (mappingCoconeNat f').X n :=
  ModuleCat.ofHom ((α.f n).hom.prodMap (shiftNegOneMapF β n).hom)

theorem mapF_comm (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (n : ℕ) :
    mapF α β n ≫ (mappingCoconeNat f').d n (n + 1) =
      (mappingCoconeNat f).d n (n + 1) ≫ mapF α β (n + 1) := by
  have wn : f.f n ≫ β.f n = α.f n ≫ f'.f n := by
    rw [← HomologicalComplex.comp_f, w, HomologicalComplex.comp_f]
  have hβ : ∀ y : shiftNegOneX L n, (shiftNegOneMapF β (n + 1)).hom ((shiftNegOneD L n).hom y) =
      (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom y) := fun y =>
    (hom_apply_hom_apply_eq_of_comp_eq (shiftNegOneMapF_comm β n) y).symm
  rw [mappingCoconeNat_d, mappingCoconeNat_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext ?_ ?_)
  · exact hom_apply_hom_apply_eq_of_comp_eq (α.comm n (n + 1)) p.1
  · change shiftNegOneSucc L' n ((f'.f n).hom ((α.f n).hom p.1)) +
        (shiftNegOneD L' n).hom ((shiftNegOneMapF β n).hom p.2) =
      (shiftNegOneMapF β (n + 1)).hom (shiftNegOneSucc L n ((f.f n).hom p.1) +
        (shiftNegOneD L n).hom p.2)
    rw [map_add, shiftNegOneMapF_succ_apply, hβ, hom_apply_hom_apply_eq_of_comp_eq wn p.1]

noncomputable def map (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    mappingCoconeNat f ⟶ mappingCoconeNat f' :=
  CochainComplex.ofHom (mapF α β) (mapF_comm α β w)

@[simp]
theorem map_id : map (𝟙 K) (𝟙 L) (by simp) = 𝟙 (mappingCoconeNat f) := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

theorem map_comp (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (α' : K' ⟶ K'')
    (β' : L' ⟶ L'') (w' : f' ≫ β' = α' ≫ f'') :
    map (α ≫ α') (β ≫ β') (by rw [reassoc_of% w, w', Category.assoc]) =
      map α β w ≫ map α' β' w' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (p : K.X n × shiftNegOneX L n) => Prod.ext rfl ?_)
  cases n with
  | zero => rfl
  | succ n => rfl

@[reassoc (attr := simp)]
theorem map_fst (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    map α β w ≫ fst f' = fst f ≫ α :=
  HomologicalComplex.hom_ext _ _ fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

@[reassoc (attr := simp)]
theorem inr_map (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') :
    inr f ≫ map α β w = shiftNegOneMap β ≫ inr f' := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun y => Prod.ext ?_ rfl)
  exact (α.f n).hom.map_zero

@[reassoc]
theorem homologyδ_naturality (α : K ⟶ K') (β : L ⟶ L') (w : f ≫ β = α ≫ f') (n : ℕ) :
    homologyδ f n ≫ HomologicalComplex.homologyMap (map α β w) (n + 1) =
      HomologicalComplex.homologyMap β n ≫ homologyδ f' n := by
  rw [homologyδ, homologyδ, Category.assoc, ← HomologicalComplex.homologyMap_comp, inr_map,
    HomologicalComplex.homologyMap_comp, shiftNegOneHomologyHom_naturality_assoc]

section ShortExact

variable {S T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)}

noncomputable def mapShortComplex (F : S ⟶ T) : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (map (f := F.τ₁) (f' := F.τ₂) S.f T.f F.comm₁₂)
    (map (f := F.τ₂) (f' := F.τ₃) S.g T.g F.comm₂₃) (by
    rw [← map_comp]
    ext n : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun (p : S.X₁.X n × shiftNegOneX T.X₁ n) =>
      Prod.ext ?_ ?_)
    · exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) S.zero) p.1
    · cases n with
      | zero => rfl
      | succ n => exact hom_apply_hom_apply_of_comp_eq (congrArg (·.f n) T.zero) p.2)

theorem shortExact_mapShortComplex (F : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) :
    (mapShortComplex F).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => by
    have hSn := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
    have hTn := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT
    have iS := (ModuleCat.mono_iff_injective _).1 hSn.mono_f
    have sS := (ModuleCat.epi_iff_surjective _).1 hSn.epi_g
    have eS := hSn.exact
    rw [ShortComplex.moduleCat_exact_iff] at eS
    refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
    · rw [ShortComplex.moduleCat_exact_iff]
      intro (p : S.X₂.X n × shiftNegOneX T.X₂ n) hp
      obtain ⟨x, hx⟩ := eS p.1 (congrArg Prod.fst hp)
      cases n with
      | zero => exact ⟨(x, PUnit.unit), Prod.ext hx rfl⟩
      | succ n =>
        have eT := (hTn n).exact
        rw [ShortComplex.moduleCat_exact_iff] at eT
        obtain ⟨y, hy⟩ := eT p.2 (congrArg Prod.snd hp)
        exact ⟨(x, y), Prod.ext hx hy⟩
    · refine (ModuleCat.mono_iff_injective _).2
        fun (p q : S.X₁.X n × shiftNegOneX T.X₁ n) h => Prod.ext (iS (congrArg Prod.fst h)) ?_
      cases n with
      | zero => rfl
      | succ n => exact (ModuleCat.mono_iff_injective _).1 (hTn n).mono_f (congrArg Prod.snd h)
    · refine (ModuleCat.epi_iff_surjective _).2 fun (p : S.X₃.X n × shiftNegOneX T.X₃ n) => ?_
      obtain ⟨x, hx⟩ := sS p.1
      cases n with
      | zero => exact ⟨(x, PUnit.unit), Prod.ext hx rfl⟩
      | succ n =>
        obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 (hTn n).epi_g p.2
        exact ⟨(x, y), Prod.ext hx hy⟩

end ShortExact

end mappingCoconeNat

end GroundTheory.ProfCoh
