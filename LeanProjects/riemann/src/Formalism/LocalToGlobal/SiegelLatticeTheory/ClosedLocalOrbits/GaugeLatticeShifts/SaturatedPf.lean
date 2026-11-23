import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

section Lin

variable (β : S.V ≃ₗ[E] S.V)

theorem smul_O (s : 𝓞 E) (x : S.V) : s • x = ((s : E)) • x := (algebraMap_smul E s x).symm

theorem symm_smul_O (s : 𝓞 E) (x : S.V) : β.symm (s • x) = s • β.symm x := by
  rw [smul_O, smul_O, map_smul]

theorem apply_smul_O (s : 𝓞 E) (x : S.V) : β (s • x) = s • β x := by
  rw [smul_O, smul_O, map_smul]

theorem gmap_apply_mem (M : Submodule (𝓞 E) S.V) (x : S.V) : β x ∈ Formalism.HermitianLatticesTheory.gmap β M ↔ x ∈ M := by
  rw [mem_gmap_iff]; simp

theorem gmap_inj {A B : Submodule (𝓞 E) S.V} : Formalism.HermitianLatticesTheory.gmap β A = Formalism.HermitianLatticesTheory.gmap β B ↔ A = B := by
  constructor
  · intro h
    ext x
    rw [← gmap_apply_mem β A, ← gmap_apply_mem β B, h]
  · rintro rfl; rfl

theorem gmap_inf' (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap β (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap β A ⊓ Formalism.HermitianLatticesTheory.gmap β B := by
  ext x; simp only [Submodule.mem_inf, mem_gmap_iff]

theorem gmap_sup' (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap β (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap β A ⊔ Formalism.HermitianLatticesTheory.gmap β B := Submodule.map_sup _ _ _

theorem gmap_span' (s : Set S.V) :
    Formalism.HermitianLatticesTheory.gmap β (Submodule.span (𝓞 E) s) = Submodule.span (𝓞 E) (β '' s) := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_span]
  rfl

theorem coe_gmap (M : Submodule (𝓞 E) S.V) : (Formalism.HermitianLatticesTheory.gmap β M : Set S.V) = β '' M := by
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_coe]
  rfl

theorem gmap_toO (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap β (toO S U) = toO S (U.map (β : S.V →ₗ[E] S.V)) := by
  ext x
  rw [mem_gmap_iff]
  simp only [toO, Submodule.restrictScalars_mem]
  rw [Submodule.mem_map_equiv]

theorem gmap_locP (P : Ideal (𝓞 E)) [P.IsPrime] (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.gmap β M) = Formalism.HermitianLatticesTheory.gmap β (Formalism.HermitianLatticesTheory.localization₂ P M) := by
  ext x
  rw [mem_gmap_iff]
  change (∃ s ∈ P.primeCompl, s • x ∈ Formalism.HermitianLatticesTheory.gmap β M) ↔ (∃ s ∈ P.primeCompl, s • β.symm x ∈ M)
  simp only [mem_gmap_iff, symm_smul_O]

theorem gmap_ideal_smul (I : Ideal (𝓞 E)) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap β (I • M) = I • Formalism.HermitianLatticesTheory.gmap β M := Submodule.map_smul'' _ _ _

theorem spanE_gmap (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap β M) = (spanE S M).map (β : S.V →ₗ[E] S.V) := by
  rw [spanE, spanE, Submodule.map_span, coe_gmap]
  rfl

theorem span_image_E (s : Set S.V) :
    (Submodule.span E s).map (β : S.V →ₗ[E] S.V) = Submodule.span E (β '' s) := by
  rw [Submodule.map_span]; rfl

end Lin

section Isom

variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)

include hβ in
theorem mem_orth_iff_sat (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

include hβ in
theorem orth_map_sat (U : Submodule E S.V) :
    orth S (U.map (β : S.V →ₗ[E] S.V)) = (orth S U).map (β : S.V →ₗ[E] S.V) := by
  ext v
  rw [Submodule.mem_map_equiv, mem_orth_iff_sat β hβ, mem_orth_iff_sat β hβ]
  constructor
  · intro h x hx
    have := h (β x) (Submodule.mem_map_of_mem hx)
    rwa [← isom_apply hβ x (β.symm v), LinearEquiv.apply_symm_apply]
  · intro h y hy
    rw [Submodule.mem_map_equiv] at hy
    have := h _ hy
    rw [← isom_apply hβ] at this
    simpa using this

variable {T T' : E}

theorem Xsp_mapL (F : LFlag S r T) : Xsp (mapL β hβ F) = (Xsp F).map (β : S.V →ₗ[E] S.V) := by
  simp only [Xsp, FlagG.X, mapL, mapFlag]
  rw [span_image_E, ← Set.range_comp]
  rfl

theorem Xflag_mapL (F : LFlag S r T) (j : ℕ) :
    Xflag (mapL β hβ F) j = (Xflag F j).map (β : S.V →ₗ[E] S.V) := by
  simp only [Xflag, FlagG.Xa, mapL, mapFlag]
  rw [span_image_E, Set.image_image]

theorem zt_mapL (F : LFlag S r T) : (mapL β hβ F).zt = β F.zt := rfl
theorem z_mapL (F : LFlag S r T) : (mapL β hβ F).fl.z = β F.fl.z := rfl
theorem e_mapL (F : LFlag S r T) (a : Fin r) : (mapL β hβ F).fl.e a = β (F.fl.e a) := rfl

theorem XLam_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) :
    XLam (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) = Formalism.HermitianLatticesTheory.gmap β (XLam Λ F) := by
  rw [XLam, XLam, gmap_inf', gmap_toO, Xsp_mapL]

theorem Lrep_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) :
    Lrep (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) = Formalism.HermitianLatticesTheory.gmap β (Lrep Λ F) := by
  rw [Lrep, Lrep, gmap_inf', gmap_toO, Xsp_mapL, orth_map_sat β hβ]

theorem Lsub_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) :
    Lsub (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) = Formalism.HermitianLatticesTheory.gmap β (Lsub Λ F) := by
  rw [Lsub, Lsub, Lrep_mapL β hβ, gmap_inf', gmap_sup', gmap_toO, gmap_toO, Xsp_mapL, orth_map_sat β hβ]

theorem UU_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UU (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = Formalism.HermitianLatticesTheory.gmap β (UU Λ F F') := by
  simp only [UU, gmap_sup', XLam_mapL β hβ, gmap_span', Set.image_singleton, zt_mapL]

theorem UUE_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UUE (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = (UUE Λ F F').map (β : S.V →ₗ[E] S.V) := by
  rw [UUE, UUE, UU_mapL β hβ, spanE_gmap]

theorem BLat_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    BLat (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) (mapL β hβ F') = Formalism.HermitianLatticesTheory.gmap β (BLat Λ F F') := by
  rw [BLat, BLat, UUE_mapL β hβ, gmap_inf', gmap_toO]

theorem NgX_mapL (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    NgX (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) (mapL β hβ F') = Formalism.HermitianLatticesTheory.gmap β (NgX Λ g F F') := by
  rw [NgX, NgX, gmap_sup', gmap_sup', gmap_ideal_smul, XLam_mapL β hβ, XLam_mapL β hβ]

theorem frameAct_map {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (b : Fin n) :
    frameAct (fun a => β (f a)) ξ b = β (frameAct f ξ b) := by
  simp only [frameAct, map_sum, LinearEquiv.map_smul]

theorem frame_mapL' (F : LFlag S r T) : frame (mapL β hβ F) = fun a => β (frame F a) := by
  funext a; exact frame_mapL β hβ F a

theorem Mplus_mapL (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    Mplus (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) (mapL β hβ F') ξ = Formalism.HermitianLatticesTheory.gmap β (Mplus Λ g F F' ξ) := by
  rw [Mplus, Mplus, gmap_span', Set.image_union, Set.image_union, ← coe_gmap, XLam_mapL β hβ,
    Set.image_singleton, zt_mapL, ← Set.range_comp, frame_mapL' β hβ, frame_mapL' β hβ]
  congr 3
  funext b
  simp only [Function.comp_apply, frameAct_map, map_smul, map_sub]

theorem ModG_map (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    ModG S (Formalism.HermitianLatticesTheory.gmap β Λ) g (β x) ↔ ModG S Λ g x := by
  simp only [ModG, ← gmap_ideal_smul, gmap_locP, gmap_apply_mem]

theorem AdmWit_mapL (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    AdmWit (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) (mapL β hβ F') ξ ↔ AdmWit Λ g F F' ξ := by
  simp only [AdmWit, frame_mapL' β hβ, frameAct_map, ← map_sub, ModG_map]

theorem IsAdmissible_mapL (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    IsAdmissible (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) (mapL β hβ F') ↔ IsAdmissible Λ g F F' := by
  simp only [IsAdmissible, AdmWit_mapL β hβ]

end Isom

section Group

theorem gmap_mul_sat (a b : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  ext x
  rw [mem_gmap_iff, mem_gmap_iff, mem_gmap_iff]
  rfl

theorem gmap_one_sat (M : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) M = M := by
  ext x
  rw [mem_gmap_iff]
  rfl

theorem gmap_inv_gmap (β : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap β⁻¹ (Formalism.HermitianLatticesTheory.gmap β M) = M := by
  rw [← gmap_mul_sat, inv_mul_cancel, gmap_one_sat]

theorem conj_apply (β n : S.V ≃ₗ[E] S.V) (x : S.V) : (β * n * β⁻¹) x = β (n (β.symm x)) := rfl

variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT)

include hβ in
theorem conj_mem_isom (n : S.V ≃ₗ[E] S.V) :
    β * n * β⁻¹ ∈ Formalism.HermitianLatticesTheory.isom S.hT ↔ n ∈ Formalism.HermitianLatticesTheory.isom S.hT :=
  (Subgroup.mul_mem_cancel_right _ (Subgroup.inv_mem _ hβ)).trans (Subgroup.mul_mem_cancel_left _ hβ)

theorem conj_gmap (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (β * n * β⁻¹) (Formalism.HermitianLatticesTheory.gmap β Λ) = Formalism.HermitianLatticesTheory.gmap β Λ ↔ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  rw [gmap_mul_sat, gmap_mul_sat, gmap_inv_gmap, gmap_inj]

include hβ in
theorem conj_isAutLam (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    IsAutLam S (Formalism.HermitianLatticesTheory.gmap β Λ) (β * n * β⁻¹) ↔ IsAutLam S Λ n := by
  simp only [IsAutLam, conj_mem_isom β hβ, conj_gmap]

theorem conj_forall_map (n : S.V ≃ₗ[E] S.V) (U W : Submodule E S.V) :
    (∀ x ∈ U.map (β : S.V →ₗ[E] S.V), (β * n * β⁻¹) x - x ∈ W.map (β : S.V →ₗ[E] S.V)) ↔
      ∀ y ∈ U, n y - y ∈ W := by
  constructor
  · intro h y hy
    have := h (β y) (Submodule.mem_map_of_mem hy)
    rw [conj_apply, LinearEquiv.symm_apply_apply, ← map_sub, Submodule.mem_map_equiv,
      LinearEquiv.symm_apply_apply] at this
    exact this
  · intro h x hx
    rw [Submodule.mem_map_equiv] at hx
    rw [conj_apply, Submodule.mem_map_equiv, map_sub, LinearEquiv.symm_apply_apply]
    exact h _ hx

variable {T : E}

include hβ in
theorem conj_mem_NLam (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V) :
    β * n * β⁻¹ ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) ↔ n ∈ NLam Λ F := by
  simp only [NLam, Set.mem_ofPred_eq, conj_isAutLam β hβ, Xflag_mapL β hβ, Xsp_mapL β hβ, orth_map_sat β hβ,
    conj_forall_map]

include hβ in
theorem mem_NLam_map (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V) :
    n ∈ NLam (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) ↔ β⁻¹ * n * β ∈ NLam Λ F := by
  have : β * (β⁻¹ * n * β) * β⁻¹ = n := by group
  rw [← conj_mem_NLam β hβ Λ F (β⁻¹ * n * β), this]

end Group

theorem generic_isomorphism_holds (g : ℕ) : GenIso S r g := by
  intro T T' β hβ Λ F F'
  simp only [IsGeneric, AdmWit_mapL β hβ, BLat_mapL β hβ, Mplus_mapL β hβ, UU_mapL β hβ, gmap_locP, gmap_inj]

theorem big_block_isomorphism_holds (g : ℕ) : BBIso S r g := by
  intro T T' P β hβ Λ F F'
  simp only [BBneP, AdmWit_mapL β hβ, BLat_mapL β hβ, Mplus_mapL β hβ, UU_mapL β hβ, gmap_locP, ne_eq, gmap_inj]

theorem iota_isomorphism_holds (g : ℕ) : IotaIso S r g := by
  intro T T' β hβ Λ F F' l' l
  simp only [IotaG, Lrep_mapL β hβ, NgX_mapL β hβ, ← map_sub, gmap_apply_mem]

theorem flag_equivalence_isomorphism : FeqFIso S r := by
  intro T T' β hβ Λ F F'
  simp only [frame_mapL' β hβ]
  constructor
  · rintro ⟨n, hn, h⟩
    refine ⟨β⁻¹ * n * β, (mem_NLam_map β hβ Λ F n).1 hn, fun a => ?_⟩
    have := h a
    change β.symm (n (β (frame F a))) = frame F' a
    rw [this, LinearEquiv.symm_apply_apply]
  · rintro ⟨n, hn, h⟩
    refine ⟨β * n * β⁻¹, (conj_mem_NLam β hβ Λ F n).2 hn, fun a => ?_⟩
    rw [conj_apply, LinearEquiv.symm_apply_apply, h a]

theorem double_coset_isomorphism : DCIso S r := by
  intro T T' β hβ Λ F F₁ F₂
  simp only [DCRel, frame_mapL' β hβ, zt_mapL]
  constructor
  · rintro ⟨n, hn, m, hm, hf, hz⟩
    refine ⟨β⁻¹ * n * β, (mem_NLam_map β hβ Λ F n).1 hn, β⁻¹ * m * β, (mem_NLam_map β hβ Λ F₁ m).1 hm,
      fun a => ?_, ?_⟩
    · apply β.injective
      rw [hf a]
      change n (m (β (frame F₁ a))) = β (β.symm (n (β (β.symm (m (β (frame F₁ a)))))))
      simp
    · apply β.injective
      rw [hz]
      change n (m (β F₁.zt)) = β (β.symm (n (β (β.symm (m (β F₁.zt))))))
      simp
  · rintro ⟨n, hn, m, hm, hf, hz⟩
    refine ⟨β * n * β⁻¹, (conj_mem_NLam β hβ Λ F n).2 hn, β * m * β⁻¹, (conj_mem_NLam β hβ Λ F₁ m).2 hm,
      fun a => ?_, ?_⟩
    · simp only [conj_apply, LinearEquiv.symm_apply_apply, hf a]
    · simp only [conj_apply, LinearEquiv.symm_apply_apply, hz]

section Rel

variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T T' : E}

def conjL (Y : S.V →ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  (β : S.V →ₗ[E] S.V) ∘ₗ Y ∘ₗ (β.symm : S.V →ₗ[E] S.V)

theorem conjL_apply (Y : S.V →ₗ[E] S.V) (x : S.V) : conjL β Y (β x) = β (Y x) := by
  simp [conjL]

theorem conjL_symm (Y : S.V →ₗ[E] S.V) : conjL β (conjL β.symm Y) = Y := by
  ext x; simp [conjL]

theorem Xa_mapFlag (F : FlagG S r T) (j : ℕ) :
    (mapFlag β hβ F).Xa j = (F.Xa j).map (β : S.V →ₗ[E] S.V) := by
  simp only [FlagG.Xa, mapFlag]
  rw [span_image_E, Set.image_image]

theorem X_mapFlag (F : FlagG S r T) : (mapFlag β hβ F).X = F.X.map (β : S.V →ₗ[E] S.V) := by
  simp only [FlagG.X, mapFlag]
  rw [span_image_E, ← Set.range_comp]
  rfl

include hβ in
theorem perpS_map (U : Submodule E S.V) :
    perpS S (U.map (β : S.V →ₗ[E] S.V)) = (perpS S U).map (β : S.V →ₗ[E] S.V) := by
  have h1 : ∀ U' : Submodule E S.V, perpS S U' = orth S U' := by
    intro U'
    ext v
    rw [mem_orth_iff_sat β hβ]
    rfl
  rw [h1, h1, orth_map_sat β hβ]

theorem mem_map_apply (U : Submodule E S.V) (x : S.V) : β x ∈ U.map (β : S.V →ₗ[E] S.V) ↔ x ∈ U := by
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem coefX_mapFlag (F : FlagG S r T) (y : S.V) (a : Fin r) :
    (mapFlag β hβ F).coefX (β y) a = F.coefX y a := by
  have hsp : ∀ y, β y ∈ Submodule.span E (Set.range (mapFlag β hβ F).e) ↔
      y ∈ Submodule.span E (Set.range F.e) := by
    intro y
    have := X_mapFlag β hβ F
    simp only [FlagG.X] at this
    rw [this, mem_map_apply]
  unfold FlagG.coefX
  by_cases h : y ∈ Submodule.span E (Set.range F.e)
  · rw [dif_pos ((hsp y).2 h), dif_pos h]
    congr 1
    apply LinearIndependent.repr_eq
    have e1 := F.e_indep.linearCombination_repr ⟨y, h⟩
    simp only at e1 ⊢
    have : (mapFlag β hβ F).e = (β : S.V →ₗ[E] S.V) ∘ F.e := rfl
    rw [this, ← Finsupp.apply_linearCombination, e1]
    rfl
  · rw [dif_neg (fun h' => h ((hsp y).1 h')), dif_neg h]

theorem ell_mapFlag (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) :
    (mapFlag β hβ F).ell (conjL β Y) = F.ell Y := by
  simp only [FlagG.ell, fvec_mapFlag, conjL_apply, coefX_mapFlag]

include hβ in
theorem conjL_mem_LieU (Y : S.V →ₗ[E] S.V) : conjL β Y ∈ LieU S ↔ Y ∈ LieU S := by
  simp only [LieU, Set.mem_ofPred_eq]
  constructor
  · intro h x y
    have := h (β x) (β y)
    rwa [conjL_apply, conjL_apply, isom_apply hβ, isom_apply hβ] at this
  · intro h x y
    obtain ⟨x, rfl⟩ := β.surjective x
    obtain ⟨y, rfl⟩ := β.surjective y
    rw [conjL_apply, conjL_apply, isom_apply hβ, isom_apply hβ]
    exact h x y

theorem conjL_forall_map (Y : S.V →ₗ[E] S.V) (U W : Submodule E S.V) :
    (∀ x ∈ U.map (β : S.V →ₗ[E] S.V), conjL β Y x ∈ W.map (β : S.V →ₗ[E] S.V)) ↔
      ∀ y ∈ U, Y y ∈ W := by
  constructor
  · intro h y hy
    have := h (β y) (Submodule.mem_map_of_mem hy)
    rwa [conjL_apply, mem_map_apply] at this
  · intro h x hx
    rw [Submodule.mem_map_equiv] at hx
    have := h _ hx
    rw [← mem_map_apply β, ← conjL_apply, LinearEquiv.apply_symm_apply] at this
    exact this

include hβ in
theorem conjL_mem_LieN (F : FlagG S r T) (Y : S.V →ₗ[E] S.V) :
    conjL β Y ∈ (mapFlag β hβ F).LieN ↔ Y ∈ F.LieN := by
  simp only [FlagG.LieN, Set.mem_ofPred_eq, conjL_mem_LieU β hβ, Xa_mapFlag β hβ, X_mapFlag β hβ,
    perpS_map β hβ, conjL_forall_map]

theorem relevant_mapFlag (K : Type) [Field K] [Algebra K E] (F : FlagG S r T) (F' : FlagG S r T') :
    Relevant K (mapFlag β hβ F) (mapFlag β hβ F') ↔ Relevant K F F' := by
  constructor
  · rintro h Y ⟨h1, h2⟩
    have := h (conjL β Y) ⟨(conjL_mem_LieN β hβ F Y).2 h1, (conjL_mem_LieN β hβ F' Y).2 h2⟩
    simpa only [FlagG.dpsi, ell_mapFlag] using this
  · rintro h Y ⟨h1, h2⟩
    rw [← conjL_symm β Y] at h1 h2 ⊢
    rw [conjL_mem_LieN β hβ] at h1 h2
    simp only [FlagG.dpsi, ell_mapFlag]
    exact h _ ⟨h1, h2⟩

end Rel

theorem relative_isomorphism_holds (K : Type) [Field K] [Algebra K E] : RelIso S r K := by
  intro T T' β hβ Λ F F'
  exact relevant_mapFlag β hβ K F.fl F'.fl

section Conv

variable (β : S.V ≃ₗ[E] S.V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) {T : E}

theorem IsLift_mapL (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) :
    IsLift (Formalism.HermitianLatticesTheory.gmap β Λ) (mapL β hβ F) ↔ IsLift Λ F := by
  simp only [IsLift, z_mapL, zt_mapL, gmap_apply_mem, β.injective.eq_iff]

theorem span_smul_e_mapL (F : LFlag S r T) (c : Fin r → E) :
    Submodule.span (𝓞 E) (Set.range fun a => c a • (mapL β hβ F).fl.e a) =
      Formalism.HermitianLatticesTheory.gmap β (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)) := by
  have h : (fun a => c a • (mapL β hβ F).fl.e a) = (β ∘ fun a => c a • F.fl.e a) := by
    funext a; exact (map_smul β _ _).symm
  rw [gmap_span', ← Set.range_comp, h]

theorem IsFixedConv_mapL (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) :
    IsFixedConv (Formalism.HermitianLatticesTheory.gmap β Λ) g (mapL β hβ F) ↔ IsFixedConv Λ g F := by
  simp only [IsFixedConv, XLam_mapL β hβ, span_smul_e_mapL β hβ, gmap_locP, gmap_inj, Lsub_mapL β hβ,
    z_mapL, ← map_smul, gmap_apply_mem]

end Conv

end Transport

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem XS_mapFlag (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
    (F : FlagG (VS D) D.R.rS T) : XS D (mapFlag β hβ F) = Formalism.HermitianLatticesTheory.gmap β (XS D F) := by
  rw [XS, XS, gmap_span']
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, mapFlag]
  constructor
  · rintro ⟨a, x, hx, rfl⟩
    exact ⟨x • F.e a, ⟨a, x, hx, rfl⟩, map_smul _ _ _⟩
  · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
    exact ⟨a, x, hx, map_smul _ _ _⟩

theorem positive_definite_isomorphism : PDIso D := by
  intro u' β hβ Λ T F F'
  simp only [PD, FrameOK, IsLift_mapL β hβ, IsAdmissible_mapL β hβ, IsFixedConv_mapL β hβ, XLam_mapL β hβ]
  rw [show (mapL β hβ F').fl = mapFlag β hβ F'.fl from rfl, XS_mapFlag D β hβ, gmap_inj]

end D7

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_left {s : Set S.V} {v : S.V} (h : ∀ x ∈ s, S.hT x v = 0) :
    ∀ x ∈ Submodule.span E s, S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem hT_span_right {s : Set S.V} {v : S.V} (h : ∀ x ∈ s, S.hT v x = 0) :
    ∀ x ∈ Submodule.span E s, S.hT v x = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem mem_orth' (U : Submodule E S.V) (v : S.V) : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

variable {T T' : E}

theorem isotropicSpan_orthogonal_anisotropicVector (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth']
  exact hT_span_left (by rintro _ ⟨a, rfl⟩; exact F.fl.z_orth a)

theorem X_le_orth_sat (F : LFlag S r T) : Xsp F ≤ orth S (Xsp F) := by
  intro v hv
  rw [mem_orth']
  refine hT_span_left ?_
  rintro _ ⟨a, rfl⟩
  exact hT_span_right (fun x hx => by obtain ⟨b, rfl⟩ := hx; exact F.fl.e_iso a b) v hv

theorem frame_last_sat (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem frame_castSucc_sat (F : LFlag S r T) (i : Fin r) : frame F (Fin.castSucc i) = F.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frameAct_split (F : LFlag S r T) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    frameAct (frame F) ξ b = (∑ i : Fin r, ((ξ (Fin.castSucc i) b : 𝓞 E) : E) • F.fl.e i) +
      ((ξ (Fin.last r) b : 𝓞 E) : E) • F.fl.z := by
  simp only [frameAct, Fin.sum_univ_castSucc, frame_castSucc_sat, frame_last_sat]

theorem sum_e_mem_X (F : LFlag S r T) (c : Fin r → E) : (∑ i, c i • F.fl.e i) ∈ Xsp F :=
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_of_forall_prime (N : Submodule (𝓞 E) S.V) (x : S.V)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ N) : x ∈ N := by
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) S.V x)
  have hI : ∀ s, s ∈ I ↔ s • x ∈ N := fun s => by simp [I]
  by_cases htop : I = ⊤
  · have := (hI 1).1 (htop ▸ Submodule.mem_top)
    simpa using this
  · obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop
    have hne : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    obtain ⟨s, hs, hsx⟩ := h ⟨M, hM.isPrime, hne⟩
    exact absurd (hIM ((hI s).2 hsx)) hs

theorem mem_gSmul (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Ideal.span {(g : 𝓞 E)} • Λ ↔ ∃ w ∈ Λ, (g : 𝓞 E) • w = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]

theorem gSmul_le (g : ℕ) (Λ : Submodule (𝓞 E) S.V) : Ideal.span {(g : 𝓞 E)} • Λ ≤ Λ :=
  Submodule.smul_le_right

theorem iota_integral_holds (g : ℕ) : IotaZ S r g := by
  rintro T T' Λ F F' hL hL' ⟨ξ, -, hdiag, hmod⟩
  refine ⟨⟨hL'.1, isotropicSpan_orthogonal_anisotropicVector F'⟩, ⟨hL.1, isotropicSpan_orthogonal_anisotropicVector F⟩, ?_⟩
  apply mem_of_forall_prime
  intro P
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  · obtain ⟨s, hs, hw⟩ := hmod (Fin.last r) P hg
    refine ⟨s, hs, ?_⟩
    rw [frame_last_sat, frameAct_split, hdiag, show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul] at hw
    set y := ∑ i : Fin r, ((ξ (Fin.castSucc i) (Fin.last r) : 𝓞 E) : E) • F.fl.e i
    set w := s • (F'.fl.z - (y + F.fl.z))
    have hwΛ : w ∈ Λ := gSmul_le g Λ hw
    have hsy : s • y ∈ XLam Λ F := by
      refine ⟨?_, ?_⟩
      · have : s • y = s • F'.fl.z - s • F.fl.z - w := by
          simp only [w, smul_sub, smul_add]; abel
        rw [this]
        exact Λ.sub_mem (Λ.sub_mem (Λ.smul_mem s hL'.1) (Λ.smul_mem s hL.1)) hwΛ
      · exact (Xsp F).smul_of_tower_mem s (sum_e_mem_X F _)
    have : s • (F.fl.z - F'.fl.z) = -w - s • y := by
      simp only [w, smul_sub, smul_add]; abel
    rw [this, NgX]
    refine Submodule.sub_mem _ (Submodule.neg_mem _ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left hw)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right hsy)
  · refine ⟨g, hg, ?_⟩
    rw [NgX]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (Λ.sub_mem hL.1 hL'.1)

end Loc

section Mplus

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem le_locP' (P : Ideal (𝓞 E)) [P.IsPrime] (M : Submodule (𝓞 E) S.V) : M ≤ Formalism.HermitianLatticesTheory.localization₂ P M :=
  fun x hx => ⟨1, P.primeCompl.one_mem, by simpa using hx⟩

theorem locP_le_locP' {P : Ideal (𝓞 E)} [P.IsPrime] {M N : Submodule (𝓞 E) S.V} (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ P N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  rintro x ⟨s, hs, hsx⟩
  obtain ⟨t, ht, htx⟩ := h hsx
  exact ⟨t * s, P.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact htx⟩

theorem Mplus_le (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F)
    (hF : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal)
    (ξ₁ ξ₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (h₁ : AdmWit Λ g F F' ξ₁) (h₂ : AdmWit Λ g F F' ξ₂) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ₁) ≤
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ₂)) := by
  have := P.isPrime
  apply locP_le_locP'
  rw [Mplus, Submodule.span_le]
  rintro v ((hv | hv) | ⟨b, rfl⟩)
  · exact le_locP' _ _ (Submodule.subset_span (Or.inl (Or.inl hv)))
  · exact le_locP' _ _ (Submodule.subset_span (Or.inl (Or.inr hv)))
  · by_cases hg0 : (g : E) = 0
    · simp only [hg0, inv_zero, zero_smul, SetLike.mem_coe]
      exact Submodule.zero_mem _
    have hgE : (((g : 𝓞 E)) : E) = (g : E) := by simp
    obtain ⟨s₁, hs₁, hw₁⟩ := h₁.2.2 b P hg
    obtain ⟨s₂, hs₂, hw₂⟩ := h₂.2.2 b P hg
    set d := frameAct (frame F) ξ₂ b - frameAct (frame F) ξ₁ b with hd_def
    have hsplit : (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ₁ b) =
        (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ₂ b) + (g : E)⁻¹ • d := by
      rw [← smul_add, hd_def]; congr 1; abel
    show (g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ₁ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ₂)
    rw [hsplit]
    refine Submodule.add_mem _ (le_locP' _ _ (Submodule.subset_span (Or.inr ⟨b, rfl⟩))) ?_
    have hd : (s₂ * s₁) • d ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
      have : (s₂ * s₁) • d = s₂ • (s₁ • (frame F' b - frameAct (frame F) ξ₁ b)) -
          s₁ • (s₂ • (frame F' b - frameAct (frame F) ξ₂ b)) := by
        simp only [hd_def, smul_sub, smul_smul, mul_comm s₁ s₂]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hw₁) (Submodule.smul_mem _ _ hw₂)
    obtain ⟨l, hl, hgl⟩ := (mem_gSmul g Λ _).1 hd
    have hgl' : ((s₂ * s₁ : 𝓞 E) : E) • d = (g : E) • l := by rw [← smul_O, ← hgl, smul_O, hgE]
    have hl' : (s₂ * s₁) • ((g : E)⁻¹ • d) = l := by
      rw [smul_O, smul_smul, mul_comm, ← smul_smul, hgl', smul_smul, inv_mul_cancel₀ hg0, one_smul]
    refine ⟨s₂ * s₁, P.asIdeal.primeCompl.mul_mem hs₂ hs₁, ?_⟩
    rw [hl']

    set k : E := ((s₂ * s₁ : 𝓞 E) : E) * (g : E)⁻¹
    have hlk : l = k • d := by rw [← hl', smul_O, smul_smul]
    set c₀ : E := k * (((ξ₂ (Fin.last r) b : 𝓞 E) : E) - ((ξ₁ (Fin.last r) b : 𝓞 E) : E))
    set x₀ : S.V := k • ((∑ i : Fin r, ((ξ₂ (Fin.castSucc i) b : 𝓞 E) : E) • F.fl.e i) -
      (∑ i : Fin r, ((ξ₁ (Fin.castSucc i) b : 𝓞 E) : E) • F.fl.e i))
    have hx₀X : x₀ ∈ Xsp F := Submodule.smul_mem _ _ (Submodule.sub_mem _ (sum_e_mem_X F _) (sum_e_mem_X F _))
    have hlx : l = x₀ + c₀ • F.fl.z := by
      rw [hlk, hd_def, frameAct_split, frameAct_split]
      simp only [x₀, c₀]
      module
    have hzo : F.fl.z ∈ orth S (Xsp F) := isotropicSpan_orthogonal_anisotropicVector F
    have hc₀ : c₀ • F.fl.z ∈ Lsub Λ F := by
      refine ⟨?_, Submodule.smul_mem _ _ hzo⟩
      have : c₀ • F.fl.z = l + (-x₀) := by rw [hlx]; abel
      rw [this]
      refine Submodule.add_mem_sup ⟨hl, ?_⟩ (Submodule.neg_mem _ hx₀X)
      rw [hlx]
      exact Submodule.add_mem _ (X_le_orth_sat F hx₀X) (Submodule.smul_mem _ _ hzo)
    obtain ⟨o, ho⟩ := hF.2 c₀ hc₀
    have hx₀Λ : x₀ ∈ Λ := by
      have : x₀ = l - o • F.fl.z := by rw [smul_O, ho, hlx]; abel
      rw [this]
      exact Λ.sub_mem hl (Λ.smul_mem o hL.1)
    rw [hlx, ← ho, ← smul_O]
    refine Submodule.add_mem _ (Submodule.subset_span (Or.inl (Or.inl ⟨hx₀Λ, hx₀X⟩))) ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ?_)))
    rw [Set.mem_singleton_iff, hL.2]

theorem m_plus_independent (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    MplusIndep Λ F g F' := by
  intro hL hF P hg ξ₁ ξ₂ h₁ h₂
  exact le_antisymm (Mplus_le g Λ F F' hL hF P hg ξ₁ ξ₂ h₁ h₂) (Mplus_le g Λ F F' hL hF P hg ξ₂ ξ₁ h₂ h₁)

end Mplus

section BBF

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem smul_comm_O (s : 𝓞 E) (c : E) (v : S.V) : s • c • v = c • s • v := by
  rw [smul_O, smul_O, smul_smul, smul_smul, mul_comm]

theorem localization_mono' {P : Ideal (𝓞 E)} [P.IsPrime] {M N : Submodule (𝓞 E) S.V} (h : M ≤ N) :
    Formalism.HermitianLatticesTheory.localization₂ P M ≤ Formalism.HermitianLatticesTheory.localization₂ P N := by
  rintro x ⟨s, hs, hsx⟩
  exact ⟨s, hs, h hsx⟩

def Apart (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : Submodule (𝓞 E) S.V :=
  XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt}

def Mint (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) ((Apart Λ F : Set S.V) ∪
    (fun w => (g : E)⁻¹ • w) '' ((UU Λ F F' ⊓ Ideal.span {(g : 𝓞 E)} • Λ : Submodule (𝓞 E) S.V) : Set S.V))

theorem UU_eq (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UU Λ F F' = Apart Λ F ⊔ Apart Λ F' := by
  simp only [UU, Apart, sup_assoc]

theorem mem_Apart_of_Xplus {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} (hL : IsLift Λ F)
    (hF : IsFixedConv Λ g F) {l : S.V} (hl : l ∈ Λ) (hx : l ∈ Xsp F ⊔ Submodule.span E {F.fl.z}) :
    l ∈ Apart Λ F := by
  obtain ⟨x₀, hx₀, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨c₀, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hzo : F.fl.z ∈ orth S (Xsp F) := isotropicSpan_orthogonal_anisotropicVector F
  have hc₀ : c₀ • F.fl.z ∈ Lsub Λ F := by
    refine ⟨?_, Submodule.smul_mem _ _ hzo⟩
    have : c₀ • F.fl.z = (x₀ + c₀ • F.fl.z) + (-x₀) := by abel
    rw [this]
    refine Submodule.add_mem_sup ⟨hl, ?_⟩ (Submodule.neg_mem _ hx₀)
    exact Submodule.add_mem _ (X_le_orth_sat F hx₀) (Submodule.smul_mem _ _ hzo)
  obtain ⟨o, ho⟩ := hF.2 c₀ hc₀
  have hx₀Λ : x₀ ∈ Λ := by
    have : x₀ = (x₀ + c₀ • F.fl.z) - o • F.fl.z := by rw [smul_O, ho]; abel
    rw [this]
    exact Λ.sub_mem hl (Λ.smul_mem o hL.1)
  refine Submodule.add_mem_sup ⟨hx₀Λ, hx₀⟩ ?_
  rw [← ho, ← smul_O, hL.2.symm]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem Apart_le_Xplus {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} (hL : IsLift Λ F) (v : S.V)
    (hv : v ∈ Apart Λ F) : v ∈ Xsp F ⊔ Submodule.span E {F.fl.z} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  refine Submodule.add_mem_sup hx.2 ?_
  obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
  rw [hL.2, smul_O]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem frame_mem_locP_Apart {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} (hL : IsLift Λ F)
    (hF : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin (r + 1)) :
    frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Apart Λ F)) := by
  have := P.isPrime
  refine Fin.lastCases ?_ (fun i => ?_) a
  · rw [frame_last_sat, ← hL.2]
    exact le_locP' _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · rw [frame_castSucc_sat]
    obtain ⟨c, -, hc1, heq⟩ := hF.1 P
    refine localization_mono' le_sup_left ?_
    rw [heq]
    refine le_locP' _ _ (Submodule.subset_span ⟨i, ?_⟩)
    simp [hc1 hg i]

theorem frameAct_mem {P : Ideal (𝓞 E)} [P.IsPrime] {M : Submodule (𝓞 E) S.V} {f : Fin (r + 1) → S.V}
    (hf : ∀ a, f a ∈ Formalism.HermitianLatticesTheory.localization₂ P M) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    frameAct f ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P M := by
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← smul_O]
  exact Submodule.smul_mem _ _ (hf a)

theorem mem_localization_gSmul {P : Ideal (𝓞 E)} [P.IsPrime] {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {v : S.V}
    (h : v ∈ Formalism.HermitianLatticesTheory.localization₂ P (Ideal.span {(g : 𝓞 E)} • Λ)) :
    ∃ s ∈ P.primeCompl, s • v ∈ Ideal.span {(g : 𝓞 E)} • Λ := h

variable (g : ℕ) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T')

theorem Mplus_eq_Mint (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (hL' : IsLift Λ F') (hF' : IsFixedConv Λ g F')
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : AdmWit Λ g F F' ξ) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mint Λ g F F')) := by
  have := P.isPrime
  have hfA := frame_mem_locP_Apart hL hF P hg
  have hfA' := frame_mem_locP_Apart hL' hF' P hg
  have hAM : Apart Λ F ≤ Mplus Λ g F F' ξ := by
    refine sup_le (fun v hv => Submodule.subset_span (Or.inl (Or.inl hv))) ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span (Or.inl (Or.inr rfl))
  have hAMi : Apart Λ F ≤ Mint Λ g F F' := fun v hv => Submodule.subset_span (Or.inl hv)
  apply le_antisymm
  · apply locP_le_locP'
    rw [Mplus, Submodule.span_le]
    rintro v ((hv | hv) | ⟨b, rfl⟩)
    · exact le_locP' _ _ (hAMi (Submodule.mem_sup_left hv))
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact le_locP' _ _ (hAMi (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    · obtain ⟨s, hs, hw⟩ := hξ.2.2 b P hg
      have hU : frame F' b - frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F') := by
        rw [UU_eq]
        refine Submodule.sub_mem _ (localization_mono' le_sup_right (hfA' b)) ?_
        exact localization_mono' le_sup_left (frameAct_mem hfA ξ b)
      obtain ⟨t, ht, htU⟩ := hU
      refine ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, Submodule.subset_span (Or.inr ⟨(t * s) • (frame F' b -
        frameAct (frame F) ξ b), ⟨?_, ?_⟩, ?_⟩)⟩
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ htU
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hw
      · exact (smul_comm_O _ _ _).symm
  · apply locP_le_locP'
    rw [Mint, Submodule.span_le]
    rintro v (hv | ⟨w, ⟨hwU, hwg⟩, rfl⟩)
    · exact le_locP' _ _ (hAM hv)
    · by_cases hg0 : (g : E) = 0
      · simp only [hg0, inv_zero, zero_smul, SetLike.mem_coe]
        exact Submodule.zero_mem _
      set K : Submodule (𝓞 E) S.V :=
        Submodule.span (𝓞 E) (Set.range fun b => frame F' b - frameAct (frame F) ξ b) with hK
      have hKM : ∀ k ∈ K, (g : E)⁻¹ • k ∈ Mplus Λ g F F' ξ := by
        intro k hk
        induction hk using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨b, rfl⟩ := hx
          exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
        | zero => simp
        | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
        | smul o x _ hx => rw [← smul_comm_O]; exact Submodule.smul_mem _ _ hx
      have hKg : K ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
        rw [hK, Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        exact hξ.2.2 b P hg
      have hf'KA : ∀ b, frame F' b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (K ⊔ Apart Λ F) := by
        intro b
        have : frame F' b = (frame F' b - frameAct (frame F) ξ b) + frameAct (frame F) ξ b := by abel
        rw [this]
        refine Submodule.add_mem _ (le_locP' _ _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))) ?_
        exact localization_mono' le_sup_right (frameAct_mem hfA ξ b)
      have hUKA : UU Λ F F' ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (K ⊔ Apart Λ F) := by
        rw [UU_eq]
        refine sup_le (fun v hv => le_locP' _ _ (Submodule.mem_sup_right hv)) (sup_le ?_ ?_)
        · obtain ⟨c, -, hc1, heq⟩ := hF'.1 P
          refine (le_locP' P.asIdeal _).trans ?_
          rw [heq]
          refine locP_le_locP' ?_
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          simp only [hc1 hg i, one_smul]
          have := hf'KA (Fin.castSucc i)
          rwa [frame_castSucc_sat] at this
        · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
          have := hf'KA (Fin.last r)
          rwa [frame_last_sat] at this
      obtain ⟨s₁, hs₁, hs₁w⟩ := hUKA hwU
      obtain ⟨k, hk, a, ha, hka⟩ := Submodule.mem_sup.1 hs₁w
      obtain ⟨s₂, hs₂, hs₂k⟩ := hKg hk
      have hs₂a : s₂ • a ∈ Ideal.span {(g : 𝓞 E)} • Λ := by
        have : s₂ • a = s₂ • (s₁ • w) - s₂ • k := by rw [← hka, smul_add]; abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hwg)) hs₂k
      obtain ⟨l, hl, hgl⟩ := (mem_gSmul g Λ _).1 hs₂a
      have hgE : (((g : 𝓞 E)) : E) = (g : E) := by simp
      have hla : l = (g : E)⁻¹ • (s₂ • a) := by
        rw [← hgl, smul_O (g : 𝓞 E), hgE, smul_smul, inv_mul_cancel₀ hg0, one_smul]
      have hlA : l ∈ Apart Λ F := by
        refine mem_Apart_of_Xplus hL hF hl ?_
        rw [hla]
        exact Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (Apart_le_Xplus hL a ha))
      refine ⟨s₂ * s₁, P.asIdeal.primeCompl.mul_mem hs₂ hs₁, ?_⟩
      have : (s₂ * s₁) • ((g : E)⁻¹ • w) = s₂ • ((g : E)⁻¹ • k) + l := by
        rw [hla, mul_smul, smul_comm_O s₁, ← hka, smul_add, smul_add, smul_comm_O s₂ _ a]
      rw [this]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hKM k hk)) (hAM hlA)

theorem BBneP_iff (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (hL' : IsLift Λ F') (hF' : IsFixedConv Λ g F')
    (hadm : IsAdmissible Λ g F F') (P : HeightOneSpectrum (𝓞 E)) :
    BBneP Λ g F F' P ↔
      (((g : 𝓞 E) ∈ P.asIdeal) → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') ≠
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mint Λ g F F'))) ∧
      (((g : 𝓞 E) ∉ P.asIdeal) → (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ F F') ≠
        Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F'))) := by
  obtain ⟨ξ₀, hξ₀⟩ := hadm
  refine and_congr_left fun _ => ?_
  constructor
  · intro h hg
    rw [← Mplus_eq_Mint g Λ F F' hL hF hL' hF' P hg ξ₀ hξ₀]
    exact h hg ξ₀ hξ₀
  · intro h hg ξ hξ
    rw [Mplus_eq_Mint g Λ F F' hL hF hL' hF' P hg ξ hξ]
    exact h hg

end BBF

section DC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem e_mem_Xflag (F : LFlag S r T) (a : Fin r) : F.fl.e a ∈ Xflag F (a.1 + 1) :=
  Submodule.subset_span ⟨a, by simp, rfl⟩

theorem Xflag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem NLam_map_X {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := by
  have hle : (Xsp F).map (n : S.V →ₗ[E] S.V) ≤ Xsp F := by
    rw [Submodule.map_le_iff_le_comap]
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    show n (F.fl.e a) ∈ Xsp F
    have h := hn.2.1 a.1 (F.fl.e a) (e_mem_Xflag F a)
    have : n (F.fl.e a) = (n (F.fl.e a) - F.fl.e a) + F.fl.e a := by abel
    rw [this]
    exact Submodule.add_mem _ (Xflag_le_X F a.1 h) (Submodule.subset_span ⟨a, rfl⟩)
  exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n _)

theorem NLam_XLam {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n (XLam Λ F) = XLam Λ F := by
  rw [XLam, gmap_inf', gmap_toO, NLam_map_X hn, hn.1.2]

theorem NLamAlt {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hL : IsLift Λ F) :
    n F.zt - F.zt ∈ XLam Λ F := by
  rw [hL.2]
  refine ⟨Λ.sub_mem ?_ hL.1, hn.2.2 _ (isotropicSpan_orthogonal_anisotropicVector F)⟩
  rw [← hn.1.2]
  exact (gmap_apply_mem n Λ _).2 hL.1

theorem sup_span_shift {B : Submodule (𝓞 E) S.V} {v d : S.V} (hd : d ∈ B) :
    B ⊔ Submodule.span (𝓞 E) {v + d} = B ⊔ Submodule.span (𝓞 E) {v} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
      (Submodule.mem_sup_left hd)
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have h := Submodule.sub_mem _
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (v + d)) :
        v + d ∈ B ⊔ Submodule.span (𝓞 E) {v + d})
      (Submodule.mem_sup_left hd : d ∈ B ⊔ Submodule.span (𝓞 E) {v + d})
    rwa [add_sub_cancel_right] at h

theorem NLam_Apart {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hL : IsLift Λ F) :
    Formalism.HermitianLatticesTheory.gmap n (Apart Λ F) = Apart Λ F := by
  rw [Apart, gmap_sup', NLam_XLam hn, gmap_span', Set.image_singleton]
  have : n F.zt = F.zt + (n F.zt - F.zt) := by abel
  rw [this, sup_span_shift (NLamAlt hn hL)]

variable {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}

theorem Xsp_DC (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    Xsp F₂ = (Xsp F₁).map (n : S.V →ₗ[E] S.V) := by
  have he : F₂.fl.e = fun a => n (m (F₁.fl.e a)) := funext fun a => by
    have := hf (Fin.castSucc a)
    simpa [frame_castSucc_sat] using this
  have hr : Set.range (fun a => n (m (F₁.fl.e a))) =
      (n : S.V →ₗ[E] S.V) '' ((m : S.V →ₗ[E] S.V) '' Set.range F₁.fl.e) := by
    ext; simp
  show Submodule.span E (Set.range F₂.fl.e) = _
  rw [he, hr, ← Submodule.map_span, ← Submodule.map_span]
  change Submodule.map (n : S.V →ₗ[E] S.V) (Submodule.map (m : S.V →ₗ[E] S.V) (Xsp F₁)) = _
  rw [NLam_map_X hm]

theorem XLam_DC (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap n (XLam Λ F₁) := by
  rw [XLam, XLam, Xsp_DC hm hf, gmap_inf', gmap_toO, hn.1.2]

theorem Apart_DC (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a)))
    (hz : F₂.zt = n (m F₁.zt)) (hL₁ : IsLift Λ F₁) :
    Apart Λ F₂ = Formalism.HermitianLatticesTheory.gmap n (Apart Λ F₁) := by
  rw [← NLam_Apart hm hL₁]
  simp only [Apart, gmap_sup', gmap_span', Set.image_singleton]
  rw [NLam_XLam hm, XLam_DC hn hm hf, hz]

theorem UU_DC (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a)))
    (hz : F₂.zt = n (m F₁.zt)) (hL : IsLift Λ F) (hL₁ : IsLift Λ F₁) :
    UU Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (UU Λ F F₁) := by
  rw [UU_eq, UU_eq, Apart_DC hn hm hf hz hL₁, gmap_sup', NLam_Apart hn hL]

theorem BLat_DC (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a)))
    (hz : F₂.zt = n (m F₁.zt)) (hL : IsLift Λ F) (hL₁ : IsLift Λ F₁) :
    BLat Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (BLat Λ F F₁) := by
  rw [BLat, BLat, UUE, UUE, UU_DC hn hm hf hz hL hL₁, spanE_gmap, gmap_inf', gmap_toO, hn.1.2]

theorem Mint_DC (g : ℕ) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hf : ∀ a, frame F₂ a = n (m (frame F₁ a)))
    (hz : F₂.zt = n (m F₁.zt)) (hL : IsLift Λ F) (hL₁ : IsLift Λ F₁) :
    Mint Λ g F F₂ = Formalism.HermitianLatticesTheory.gmap n (Mint Λ g F F₁) := by
  have hM : UU Λ F F₂ ⊓ Ideal.span {(g : 𝓞 E)} • Λ =
      Formalism.HermitianLatticesTheory.gmap n (UU Λ F F₁ ⊓ Ideal.span {(g : 𝓞 E)} • Λ) := by
    rw [gmap_inf', gmap_ideal_smul, hn.1.2, UU_DC hn hm hf hz hL hL₁]
  have h2 : (fun x => (g : E)⁻¹ • n x) = (fun x => n ((g : E)⁻¹ • x)) :=
    funext fun x => (map_smul n _ x).symm
  rw [Mint, Mint, gmap_span', Set.image_union, ← coe_gmap, NLam_Apart hn hL, hM, coe_gmap, Set.image_image,
    Set.image_image, h2]

end DC

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem big_block_function_holds (u u' : D.what₂.Word) : BBFun D u u' := by
  intro F0 Λ hΛ P x y hxy
  obtain ⟨n, hn, m, hm, hf, hz⟩ := hxy
  have hL : IsLift Λ (lf D F0) := hΛ.2.1.2.2.1
  have hC : IsFixedConv Λ (gS D) (lf D F0) := hΛ.2.1.2.2.2
  obtain ⟨hLx, hAx, hCx, -⟩ := x.2
  obtain ⟨hLy, hAy, hCy, -⟩ := y.2
  show BBneP Λ (gS D) (lf D F0) x.1 P ↔ BBneP Λ (gS D) (lf D F0) y.1 P
  rw [BBneP_iff _ _ _ _ hL hC hLx hCx hAx, BBneP_iff _ _ _ _ hL hC hLy hCy hAy,
    BLat_DC hn hm hf hz hL hLx, UU_DC hn hm hf hz hL hLx, Mint_DC _ hn hm hf hz hL hLx]
  simp only [gmap_locP, ne_eq, gmap_inj]

end D7

section Split

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
variable (e f : Fin r → S.V)

def pj : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

theorem pj_apply (v : S.V) : pj e f v = v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a := by
  simp [pj, LinearMap.sub_apply, LinearMap.sum_apply]

def bmap (δ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V :=
  (LinearMap.id - pj e f) + pj e f ∘ₗ (δ : S.V →ₗ[E] S.V) ∘ₗ pj e f

theorem bmap_apply (δ : S.V ≃ₗ[E] S.V) (v : S.V) : bmap e f δ v = (v - pj e f v) + pj e f (δ (pj e f v)) := by
  simp [bmap]

variable {e f}
variable (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
  (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)

include hef in
theorem hfe' (a b : Fin r) : S.hT (f a) (e b) = if b = a then 1 else 0 := by
  rw [← S.herm.eq (e b) (f a), hef]
  split_ifs <;> simp

include hee hef in
theorem pj_e (b : Fin r) : pj e f (e b) = 0 := by
  rw [pj_apply]
  simp [hfe' hef, hee]

include hff hef in
theorem pj_f (b : Fin r) : pj e f (f b) = 0 := by
  rw [pj_apply]
  simp [hff, hef]

theorem pj_perp (v : S.V) (hv : ∀ a, S.hT (e a) v = 0 ∧ S.hT (f a) v = 0) : pj e f v = v := by
  rw [pj_apply]
  simp [(hv _).1, (hv _).2]

include hee hef in
theorem hT_e_pj (v : S.V) (b : Fin r) : S.hT (e b) (pj e f v) = 0 := by
  rw [pj_apply]
  simp [hee, hef]

include hff hef in
theorem hT_f_pj (v : S.V) (b : Fin r) : S.hT (f b) (pj e f v) = 0 := by
  rw [pj_apply]
  simp [hff, hfe' hef]

include hee hff hef in
theorem pj_pj (v : S.V) : pj e f (pj e f v) = pj e f v :=
  pj_perp _ fun a => ⟨hT_e_pj hee hef v a, hT_f_pj hff hef v a⟩

include hee hef in
theorem pj_X (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) : pj e f x = 0 := by
  have : Submodule.span E (Set.range e) ≤ LinearMap.ker (pj e f) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact pj_e hee hef b
  exact this hx

theorem pj_sub_mem (u : S.V) (hu : ∀ a, S.hT (e a) u = 0) :
    pj e f u - u ∈ Submodule.span E (Set.range e) := by
  have : pj e f u - u = -∑ a, S.hT (f a) u • e a := by
    rw [pj_apply]; simp only [hu, zero_smul, Finset.sum_const_zero, sub_zero]; abel
  rw [this]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

include hee in
theorem perpX_of_X (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) (a : Fin r) : S.hT (e a) x = 0 :=
  hT_span_right (by rintro _ ⟨b, rfl⟩; exact hee a b) x hx

theorem hT_X_left (y : S.V) (hy : ∀ a, S.hT (e a) y = 0) (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) :
    S.hT x y = 0 :=
  hT_span_left (by rintro _ ⟨b, rfl⟩; exact hy b) x hx

theorem hT_X_right (y : S.V) (hy : ∀ a, S.hT (e a) y = 0) (x : S.V) (hx : x ∈ Submodule.span E (Set.range e)) :
    S.hT y x = 0 := by
  rw [← S.herm.eq x y, hT_X_left y hy x hx, map_zero]

theorem perpX_map (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX' : ∀ x ∈ Submodule.span E (Set.range e), δ.symm x ∈ Submodule.span E (Set.range e))
    (y : S.V) (hy : ∀ a, S.hT (e a) y = 0) (a : Fin r) : S.hT (e a) (δ y) = 0 := by
  have := isom_apply hδ (δ.symm (e a)) y
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact hT_X_left y hy _ (hX' _ (Submodule.subset_span ⟨a, rfl⟩))

include hee in
theorem hT_modX {y y' q q' : S.V} (hy : ∀ a, S.hT (e a) y = 0) (hy' : ∀ a, S.hT (e a) y' = 0)
    (hx : q - y ∈ Submodule.span E (Set.range e)) (hx' : q' - y' ∈ Submodule.span E (Set.range e)) :
    S.hT q q' = S.hT y y' := by
  obtain ⟨x, hxX, rfl⟩ : ∃ x ∈ Submodule.span E (Set.range e), q = y + x := ⟨q - y, hx, by abel⟩
  obtain ⟨x', hxX', rfl⟩ : ∃ x ∈ Submodule.span E (Set.range e), q' = y' + x := ⟨q' - y', hx', by abel⟩
  have h1 : S.hT x y' = 0 := hT_X_left y' hy' x hxX
  have h2 : S.hT x x' = 0 := hT_X_left x' (perpX_of_X hee x' hxX') x hxX
  have h4 : S.hT y x' = 0 := hT_X_right y hy x' hxX'
  simp [map_add, LinearMap.add_apply, h1, h2, h4]

theorem cross_l (v w : S.V) (hw : ∀ a, S.hT (e a) w = 0 ∧ S.hT (f a) w = 0) :
    S.hT (v - pj e f v) w = 0 := by
  rw [pj_apply]
  simp [(hw _).1, (hw _).2]

theorem cross_r (v w : S.V) (hw : ∀ a, S.hT (e a) w = 0 ∧ S.hT (f a) w = 0) :
    S.hT w (v - pj e f v) = 0 := by
  rw [← S.herm.eq, cross_l v w hw, map_zero]

include hee hff hef in
theorem bmap_isom (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX' : ∀ x ∈ Submodule.span E (Set.range e), δ.symm x ∈ Submodule.span E (Set.range e)) (v v' : S.V) :
    S.hT (bmap e f δ v) (bmap e f δ v') = S.hT v v' := by
  have hP : ∀ w, ∀ a, S.hT (e a) (pj e f w) = 0 ∧ S.hT (f a) (pj e f w) = 0 :=
    fun w a => ⟨hT_e_pj hee hef w a, hT_f_pj hff hef w a⟩
  have ev : S.hT v v' = S.hT (v - pj e f v) (v' - pj e f v') + S.hT (pj e f v) (pj e f v') := by
    conv_lhs => rw [← sub_add_cancel v (pj e f v), ← sub_add_cancel v' (pj e f v')]
    simp only [map_add, LinearMap.add_apply, cross_l v _ (hP v'), cross_r v' _ (hP v)]
    abel
  rw [ev, bmap_apply, bmap_apply]
  simp only [map_add, LinearMap.add_apply, cross_l v _ (hP _), cross_r v' _ (hP _)]
  have hy := fun a => (hP v a).1
  have hy' := fun a => (hP v' a).1
  have hdy := perpX_map δ hδ hX' _ hy
  have hdy' := perpX_map δ hδ hX' _ hy'
  rw [hT_modX hee hdy hdy' (pj_sub_mem _ hdy) (pj_sub_mem _ hdy'), isom_apply hδ]
  abel

include hee hff hef in
theorem bmap_inv (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX' : ∀ x ∈ Submodule.span E (Set.range e), δ.symm x ∈ Submodule.span E (Set.range e)) (v : S.V) :
    bmap e f δ.symm (bmap e f δ v) = v := by
  have hpw : pj e f (pj e f v) = pj e f v := pj_pj hee hff hef v
  have hq : pj e f (bmap e f δ v) = pj e f (δ (pj e f v)) := by
    rw [bmap_apply, map_add, map_sub, hpw, sub_self, zero_add, pj_pj hee hff hef]
  have hu := perpX_map δ hδ hX' _ (fun a => hT_e_pj hee hef v a)
  have hx₁ := pj_sub_mem (e := e) (f := f) _ hu
  have key : pj e f (δ.symm (pj e f (δ (pj e f v)))) = pj e f v := by
    have : δ.symm (pj e f (δ (pj e f v))) = pj e f v + δ.symm (pj e f (δ (pj e f v)) - δ (pj e f v)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]; abel
    rw [this, map_add, hpw, pj_X hee hef _ (hX' _ hx₁), add_zero]
  rw [bmap_apply, hq, key, bmap_apply]
  abel

include hee in
theorem bmap_sub_mem (δ : S.V ≃ₗ[E] S.V) (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ x ∈ Submodule.span E (Set.range e), δ x ∈ Submodule.span E (Set.range e))
    (hX' : ∀ x ∈ Submodule.span E (Set.range e), δ.symm x ∈ Submodule.span E (Set.range e))
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0)
    (x : S.V) (hx : ∀ a, S.hT (e a) x = 0) :
    δ x - bmap e f δ x ∈ Submodule.span E (Set.range e) := by
  have h1 := pj_sub_mem (f := f) x hx
  have h2 := pj_sub_mem (f := f) (δ (pj e f x)) (perpX_map δ hδ hX' _ (fun a => hT_e_pj hee hef x a))
  have h3 : δ (pj e f x - x) ∈ Submodule.span E (Set.range e) := hX _ h1
  have : δ x - bmap e f δ x = (pj e f x - x) - (pj e f (δ (pj e f x)) - δ (pj e f x)) - δ (pj e f x - x) := by
    rw [bmap_apply, map_sub]; abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ h1 h2) h3

end Split

section SplitEquiv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {e f : Fin r → S.V}

def bEquiv (hee : ∀ a b, S.hT (e a) (e b) = 0) (hff : ∀ a b, S.hT (f a) (f b) = 0)
    (hef : ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0) (δ : S.V ≃ₗ[E] S.V)
    (hδ : δ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hX : ∀ x ∈ Submodule.span E (Set.range e), δ x ∈ Submodule.span E (Set.range e))
    (hX' : ∀ x ∈ Submodule.span E (Set.range e), δ.symm x ∈ Submodule.span E (Set.range e)) :
    S.V ≃ₗ[E] S.V :=
  LinearEquiv.ofLinearMap (bmap e f δ) (bmap e f δ.symm)
    (LinearMap.ext fun v => by
      have := bmap_inv hee hff hef δ.symm (Subgroup.inv_mem _ hδ)
        (fun x hx => by rw [LinearEquiv.symm_symm]; exact hX x hx) v
      rw [LinearEquiv.symm_symm] at this
      simpa using this)
    (LinearMap.ext fun v => by simpa using bmap_inv hee hff hef δ hδ hX' v)

theorem bEquiv_apply (hee hff hef) (δ : S.V ≃ₗ[E] S.V) (hδ hX hX') (v : S.V) :
    bEquiv (e := e) (f := f) hee hff hef δ hδ hX hX' v = bmap e f δ v := rfl

theorem bEquiv_symm_apply (hee hff hef) (δ : S.V ≃ₗ[E] S.V) (hδ hX hX') (v : S.V) :
    (bEquiv (e := e) (f := f) hee hff hef δ hδ hX hX').symm v = bmap e f δ.symm v := rfl

end SplitEquiv

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem Xa_r' {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (A : FlagG S r T) : A.Xa r = A.X := by
  simp only [FlagG.Xa, FlagG.X]
  congr 1
  ext x
  simp

theorem automorphism_induces_lattice_map (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) : AutFInduces D u F0 Λ := by
  rintro - ⟨f, L, hff, hef, hLp, hzL, hΛ⟩
  have hee : ∀ a b, (VS D).hT (F0.e a) (F0.e b) = 0 := F0.e_iso
  have hLΛ : L ≤ Λ := by rw [hΛ]; exact le_sup_right.trans le_sup_left
  have hpjΛ : ∀ v ∈ Λ, pj F0.e f v ∈ L := by
    have h : Λ ≤ L.comap ((pj F0.e f).restrictScalars (𝓞 D.host.E)) := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        show pj F0.e f (x • F0.e a) ∈ L
        rw [map_smul, pj_e hee hef, smul_zero]
        exact L.zero_mem
      · intro l hl
        show pj F0.e f l ∈ L
        rw [pj_perp l (fun a => hLp l hl a)]
        exact hl
      · rw [latSpan, Submodule.span_le]
        rintro _ ⟨a, x, -, rfl⟩
        show pj F0.e f (x • f a) ∈ L
        rw [map_smul, pj_f hff hef, smul_zero]
        exact L.zero_mem
    exact fun v hv => h hv
  have hbΛ : ∀ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V, (∀ x ∈ Λ, δ x ∈ Λ) → ∀ v ∈ Λ, bmap F0.e f δ v ∈ Λ := by
    intro δ hδ v hv
    rw [bmap_apply]
    exact Λ.add_mem (Λ.sub_mem hv (hLΛ (hpjΛ v hv))) (hLΛ (hpjΛ _ (hδ _ (hLΛ (hpjΛ v hv)))))
  have hzp : pj F0.e f F0.z = F0.z := pj_perp _ (hLp _ hzL)
  ext φ
  constructor
  · rintro ⟨γ, ⟨hγi, hγX, hγz⟩, hγΛ, hφ⟩
    have hXX : (F0.X).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
      rw [← Xa_r' F0]; exact hγX _
    have hX : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e), γ x ∈ Submodule.span D.host.E (Set.range F0.e) :=
      fun x hx => by
        change γ x ∈ F0.X
        rw [← hXX]
        exact Submodule.mem_map_of_mem hx
    have hX' : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e),
        γ.symm x ∈ Submodule.span D.host.E (Set.range F0.e) := fun x hx => by
      change x ∈ F0.X at hx
      rw [← hXX, Submodule.mem_map_equiv] at hx
      exact hx
    have hγΛ1 : ∀ y ∈ Λ, γ y ∈ Λ := fun y hy => by
      rw [← hγΛ]; exact (gmap_apply_mem γ Λ y).2 hy
    have hγΛ2 : ∀ y ∈ Λ, γ.symm y ∈ Λ := fun y hy => by
      have h := hy
      rw [← hγΛ, mem_gmap_iff] at h
      exact h
    let β := bEquiv hee hff hef γ hγi hX hX'
    have hβ : ∀ v, β v = bmap F0.e f γ v := fun v => rfl
    have hβs : ∀ v, β.symm v = bmap F0.e f γ.symm v := fun v => rfl
    have hβe : ∀ i, β (F0.e i) = F0.e i := fun i => by
      rw [hβ, bmap_apply, pj_e hee hef, sub_zero, map_zero, map_zero, add_zero]
    have hβz : β F0.z = F0.z := by
      rw [hβ, bmap_apply, hzp, sub_self, zero_add, hγz, hzp]
    refine ⟨β, ⟨⟨?_, ?_⟩, fun a => ?_, hβz⟩, ?_⟩
    · intro v v'
      rw [hβ, hβ]
      exact bmap_isom hee hff hef γ hγi hX' v v'
    · ext x
      rw [mem_gmap_iff, hβs]
      constructor
      · intro hx
        have := hbΛ γ hγΛ1 _ hx
        rwa [← hβ, ← hβs, LinearEquiv.apply_symm_apply] at this
      · intro hx
        exact hbΛ γ.symm hγΛ2 x hx
    · refine Fin.lastCases ?_ (fun i => ?_) a
      · show β (F0.fvec (Fin.last _)) = F0.fvec (Fin.last _)
        simp only [FlagG.fvec, Fin.snoc_last]
        exact hβz
      · show β (F0.fvec (Fin.castSucc i)) = F0.fvec (Fin.castSucc i)
        simp only [FlagG.fvec, Fin.snoc_castSucc]
        exact hβe i
    · intro x hx
      have hx0 : ∀ y ∈ F0.X, (VS D).hT y x.1 = 0 := x.2
      have hγx : γ x.1 ∈ perpS (VS D) F0.X := by
        show ∀ y ∈ F0.X, (VS D).hT y (γ x.1) = 0
        intro y hy
        have := isom_apply hγi (γ.symm y) x.1
        rw [LinearEquiv.apply_symm_apply] at this
        rw [this]
        exact hx0 _ (hX' y hy)
      rw [hφ x hγx, Submodule.Quotient.eq]
      exact bmap_sub_mem hee γ hγi hX hX' hef x.1 (fun a => hx0 _ (Submodule.subset_span ⟨a, rfl⟩))
  · rintro ⟨β, hβ, hφ⟩
    have hβe : ∀ i, β (F0.e i) = F0.e i := fun i => by
      have := hβ.2.1 (Fin.castSucc i)
      rwa [frame_castSucc_sat] at this
    have hβz : β F0.z = F0.z := by
      have := hβ.2.1 (Fin.last _)
      rwa [frame_last_sat] at this
    refine ⟨β, ⟨hβ.1.1, fun j => ?_, hβz⟩, hβ.1.2, hφ⟩
    rw [FlagG.Xa, Submodule.map_span, Set.image_image]
    congr 1
    exact Set.image_congr fun i _ => hβe i

end D7

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem saturated_term_classes {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (hrows : IsRowReps D F0 what₂) (hTF : TermFun D u u')
    (p : HeightOneSpectrum (𝓞 D.host.F)) :
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.G = 0} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.G ≠ 0} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.generic} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.generic} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.relevant} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.relevant} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | t.FeqF} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ t.FeqF} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | termBBne t p} ∧
    TSat (what₂ := what₂) {t : Term D u u' F0 what₂ | ¬ termBBne t p} :=
  saturated_term_classes_of_iso hrows hTF (big_block_function_holds D u u') (generic_isomorphism_holds _) (relative_isomorphism_holds _) flag_equivalence_isomorphism (big_block_isomorphism_holds _) p

end D7

section Int

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def MplusInt (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') :
    Submodule (𝓞 E) S.V :=
  UU Λ F F' ⊔ Submodule.span (𝓞 E) {v | ∃ u' ∈ Apart Λ F', ∃ u ∈ Apart Λ F,
    u' - u ∈ Ideal.span {(g : 𝓞 E)} • Λ ∧ v = (g : E)⁻¹ • (u' - u)}

variable {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {F : LFlag S r T} {F' : LFlag S r T'}

theorem Mint_le_MplusInt : Mint Λ g F F' ≤ MplusInt Λ g F F' := by
  rw [Mint, Submodule.span_le]
  rintro v (hv | ⟨w, ⟨hwU, hwg⟩, rfl⟩)
  · exact Submodule.mem_sup_left (by rw [UU_eq]; exact Submodule.mem_sup_left hv)
  · have hwU' : w ∈ Apart Λ F ⊔ Apart Λ F' := by rw [← UU_eq]; exact hwU
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hwU'
    have e1 : u' - -u = u + u' := by rw [sub_neg_eq_add, add_comm]
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨u', hu', -u, Submodule.neg_mem _ hu, ?_, ?_⟩)
    · rw [e1]; exact hwg
    · show (g : E)⁻¹ • (u + u') = (g : E)⁻¹ • (u' - -u)
      rw [e1]

theorem Apart_le_Mplus (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) : Apart Λ F ≤ Mplus Λ g F F' ξ := by
  refine sup_le (fun v hv => Submodule.subset_span (Or.inl (Or.inl hv))) ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact Submodule.subset_span (Or.inl (Or.inr rfl))

theorem frame'_mem_locP_Mplus (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E))
    (hg : (g : 𝓞 E) ∈ P.asIdeal) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : AdmWit Λ g F F' ξ)
    (b : Fin (r + 1)) :
    frame F' b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ)) := by
  have := P.isPrime
  have hfx : frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ) :=
    localization_mono' (Apart_le_Mplus ξ) (frameAct_mem (frame_mem_locP_Apart hL hF P hg) ξ b)
  have hgE : (((g : 𝓞 E)) : E) = (g : E) := by simp
  by_cases hg0 : (g : E) = 0
  · obtain ⟨s, hs, hw⟩ := hξ.2.2 b P hg
    obtain ⟨w, -, hw'⟩ := (mem_gSmul g Λ _).1 hw
    have hg0' : (g : 𝓞 E) = 0 := by simpa using hg0
    rw [hg0', zero_smul, eq_comm, smul_O] at hw'
    have hs0 : ((s : 𝓞 E) : E) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by simpa using h0
      rw [this]
      exact P.asIdeal.zero_mem
    have hd := (smul_eq_zero.1 hw').resolve_left hs0
    rw [sub_eq_zero] at hd
    rw [hd]
    exact hfx
  · have : frame F' b = (g : 𝓞 E) • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) +
        frameAct (frame F) ξ b := by
      rw [smul_O, hgE, smul_smul, mul_inv_cancel₀ hg0, one_smul]; abel
    rw [this]
    refine Submodule.add_mem _ (le_locP' _ _ (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨b, rfl⟩)))) hfx

theorem MplusInt_le_locP_Mint (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (hL' : IsLift Λ F')
    (hF' : IsFixedConv Λ g F') (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : AdmWit Λ g F F' ξ) :
    MplusInt Λ g F F' ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mint Λ g F F')) := by
  have := P.isPrime
  have hMM := Mplus_eq_Mint g Λ F F' hL hF hL' hF' P hg ξ hξ
  have hfM := frame'_mem_locP_Mplus hL hF P hg ξ hξ
  refine sup_le ?_ ?_
  · rw [UU_eq]
    refine sup_le (fun v hv => le_locP' _ _ (Submodule.subset_span (Or.inl hv))) ?_
    rw [← hMM]
    refine sup_le ?_ ?_
    · obtain ⟨c, -, hc1, heq⟩ := hF'.1 P
      refine (le_locP' P.asIdeal _).trans ?_
      rw [heq]
      refine locP_le_locP' ?_
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [hc1 hg i, one_smul]
      have := hfM (Fin.castSucc i)
      rwa [frame_castSucc_sat] at this
    · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
      have := hfM (Fin.last r)
      rwa [frame_last_sat] at this
  · rw [Submodule.span_le]
    rintro v ⟨u', hu', u, hu, hug, rfl⟩
    refine le_locP' _ _ (Submodule.subset_span (Or.inr ⟨u' - u, ⟨?_, hug⟩, rfl⟩))
    show u' - u ∈ UU Λ F F'
    rw [UU_eq]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right hu') (Submodule.mem_sup_left hu)

theorem Mplus_eq_MplusInt (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (hL' : IsLift Λ F')
    (hF' : IsFixedConv Λ g F') (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (hξ : AdmWit Λ g F F' ξ) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F F' ξ) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MplusInt Λ g F F')) := by
  have := P.isPrime
  rw [Mplus_eq_Mint g Λ F F' hL hF hL' hF' P hg ξ hξ]
  exact le_antisymm (localization_mono' Mint_le_MplusInt)
    (locP_le_locP' (MplusInt_le_locP_Mint hL hF hL' hF' P hg ξ hξ))

theorem MplusInt_away (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∉ P.asIdeal) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MplusInt Λ g F F') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ F F')) := by
  have := P.isPrime
  have hgE : (((g : 𝓞 E)) : E) = (g : E) := by simp
  have hg0 : (g : E) ≠ 0 := by
    intro h0
    apply hg
    have : (g : 𝓞 E) = 0 := by simpa using h0
    rw [this]
    exact P.asIdeal.zero_mem
  refine le_antisymm (locP_le_locP' (sup_le (le_locP' _ _) ?_)) (localization_mono' le_sup_left)
  rw [Submodule.span_le]
  rintro v ⟨u', hu', u, hu, -, rfl⟩
  refine ⟨(g : 𝓞 E), hg, ?_⟩
  rw [smul_O, hgE, smul_smul, mul_inv_cancel₀ hg0, one_smul, UU_eq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hu') (Submodule.mem_sup_left hu)

theorem eq_of_locP {A B : Submodule (𝓞 E) S.V}
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B)) : A = B := by
  have key : ∀ A B : Submodule (𝓞 E) S.V, (∀ P : HeightOneSpectrum (𝓞 E), (haveI := P.isPrime;
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B)) → A ≤ B := by
    intro A B h x hx
    apply mem_of_forall_prime
    intro P
    have := P.isPrime
    have hx' : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B := by rw [← h P]; exact le_locP' _ _ hx
    obtain ⟨s, hs, hsx⟩ := hx'
    exact ⟨s, hs, hsx⟩
  exact le_antisymm (key A B h) (key B A fun P => (h P).symm)

theorem isGeneric_iff_MplusInt (hL : IsLift Λ F) (hF : IsFixedConv Λ g F) (hL' : IsLift Λ F')
    (hF' : IsFixedConv Λ g F') (hadm : IsAdmissible Λ g F F') :
    IsGeneric Λ g F F' ↔ BLat Λ F F' = MplusInt Λ g F F' := by
  constructor
  · rintro ⟨ξ, hξ, h⟩
    apply eq_of_locP
    intro P
    by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
    · rw [(h P).1 hg, Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ]
    · rw [(h P).2 hg, MplusInt_away P hg]
  · intro h
    obtain ⟨ξ, hξ⟩ := hadm
    refine ⟨ξ, hξ, fun P => ⟨fun hg => ?_, fun hg => ?_⟩⟩
    · rw [h, Mplus_eq_MplusInt hL hF hL' hF' P hg ξ hξ]
    · rw [h, MplusInt_away P hg]

end Int

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem m_plus_integral_admissible {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    {F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (hF' : PD D Λ (lf D F0) u' F') :
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)),
      ((gS D : 𝓞 D.host.E) ∈ P.asIdeal) → AdmWit Λ (gS D) (lf D F0) F' ξ →
        (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ (gS D) (lf D F0) F' ξ) =
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MplusInt Λ (gS D) (lf D F0) F'))) ∧
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : 𝓞 D.host.E) ∉ P.asIdeal) →
        (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (MplusInt Λ (gS D) (lf D F0) F') =
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ (lf D F0) F'))) ∧
    (IsGeneric Λ (gS D) (lf D F0) F' ↔ BLat Λ (lf D F0) F' = MplusInt Λ (gS D) (lf D F0) F') := by
  have hL : IsLift Λ (lf D F0) := hΛ.2.1.2.2.1
  have hC : IsFixedConv Λ (gS D) (lf D F0) := hΛ.2.1.2.2.2
  obtain ⟨hL', hA', hC', -⟩ := hF'
  exact ⟨fun P ξ hg hξ => Mplus_eq_MplusInt hL hC hL' hC' P hg ξ hξ, fun P hg => MplusInt_away P hg,
    isGeneric_iff_MplusInt hL hC hL' hC' hA'⟩

end D7

end Formalism.L2.SG.Pf
