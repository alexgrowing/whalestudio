import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.GmapInjective

noncomputable section

namespace PI.RepsIndep.Tr

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem Xsp_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapL γ hγ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) :=
  X_mapF hγ F.fl

theorem Xflag_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapL γ hγ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) :=
  Xa_mapF hγ F.fl j

theorem XLam_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : XLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (XLam Λ F) := by
  simp only [XLam, Xsp_mapL hγ, gmap_inf, gmap_toO]

theorem Lrep_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : Lrep (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (Lrep Λ F) := by
  simp only [Lrep, Xsp_mapL hγ, orth_map hγ, gmap_inf, gmap_toO]

theorem Lsub_mapL {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) : Lsub (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) = Formalism.HermitianLatticesTheory.gmap γ (Lsub Λ F) := by
  simp only [Lsub, Lrep_mapL hγ, Xsp_mapL hγ, orth_map hγ, gmap_inf, gmap_sup, gmap_toO]

theorem ModG_map {γ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {x : S.V} (h : ModG S Λ g x) :
    ModG S (Formalism.HermitianLatticesTheory.gmap γ Λ) g (γ x) := by
  intro P hP
  have h1 := h P hP
  rw [← gmap_smul, ← gmap_locP, ap_mem_gmap]
  exact h1

theorem frameAct_map {γ : S.V ≃ₗ[E] S.V} {n : ℕ} (f : Fin n → S.V) (ξ : Matrix (Fin n) (Fin n) (𝓞 E))
    (b : Fin n) : frameAct (fun i => γ (f i)) ξ b = γ (frameAct f ξ b) := by
  simp only [frameAct, map_sum, map_smul]

theorem frame_mapL' {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    frame (mapL γ hγ F) = fun i => γ (frame F i) :=
  funext (frame_mapL hγ F)

theorem AdmWit_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} {F' : LFlag S r T'} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h : AdmWit Λ g F F' ξ) : AdmWit (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') ξ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun b => ?_⟩
  simp only [frame_mapL' hγ, frameAct_map]
  rw [← map_sub]
  exact ModG_map (h3 b)

theorem IsLift_map {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {F : LFlag S r T} (h : IsLift Λ F) : IsLift (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨ap_mem_gmap.2 h1, by show γ F.zt = γ F.fl.z; rw [h2]⟩

theorem IsFixedConv_map {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} (h : IsFixedConv Λ g F) : IsFixedConv (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun P => ?_, fun c hc => h2 c ?_⟩
  · obtain ⟨c, hc0, hc1, hc2⟩ := h1 P
    refine ⟨c, hc0, hc1, ?_⟩
    rw [XLam_mapL hγ, ← gmap_locP, hc2, gmap_locP, gmap_span, ← Set.range_comp]
    simp only [Function.comp_def, map_smul]
    rfl
  · rw [Lsub_mapL hγ] at hc
    have h3 : γ (c • F.fl.z) ∈ Formalism.HermitianLatticesTheory.gmap γ (Lsub Λ F) := by
      rw [map_smul]
      exact hc
    exact ap_mem_gmap.1 h3

theorem UU_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    UU (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = Formalism.HermitianLatticesTheory.gmap γ (UU Λ F F') := by
  simp only [UU, XLam_mapL hγ, gmap_sup, gmap_span, Set.image_singleton]
  rfl

theorem UUE_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    UUE (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = (UUE Λ F F').map (γ : S.V →ₗ[E] S.V) := by
  rw [UUE, UUE, UU_map hγ, spanE_gmap]

theorem BLat_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') :
    BLat (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) (mapL γ hγ F') = Formalism.HermitianLatticesTheory.gmap γ (BLat Λ F F') := by
  simp only [BLat, UUE_map hγ, gmap_inf, gmap_toO]

theorem Mplus_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (Λ : Submodule (𝓞 E) S.V)
    (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    Mplus (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') ξ = Formalism.HermitianLatticesTheory.gmap γ (Mplus Λ g F F' ξ) := by
  simp only [Mplus, gmap_span, Set.image_union, Set.image_singleton, XLam_mapL hγ, coe_gmap,
    ← Set.range_comp]
  congr 3
  funext b
  simp only [Function.comp_apply, map_smul, map_sub, frame_mapL' hγ, frameAct_map]

theorem IsGeneric_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {g : ℕ} {F : LFlag S r T} {F' : LFlag S r T'} (h : IsGeneric Λ g F F') :
    IsGeneric (Formalism.HermitianLatticesTheory.gmap γ Λ) g (mapL γ hγ F) (mapL γ hγ F') := by
  obtain ⟨ξ, hξ, hP⟩ := h
  refine ⟨ξ, AdmWit_map hγ hξ, fun P => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · rw [BLat_map hγ, Mplus_map hγ, ← gmap_locP, ← gmap_locP, (hP P).1 hg]
  · rw [BLat_map hγ, UU_map hγ, ← gmap_locP, ← gmap_locP, (hP P).2 hg]

def conj (γ n : S.V ≃ₗ[E] S.V) : S.V ≃ₗ[E] S.V := γ.symm.trans (n.trans γ)

theorem conj_apply (γ n : S.V ≃ₗ[E] S.V) (x : S.V) : conj γ n x = γ (n (γ.symm x)) := rfl

theorem gmap_trans (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a.trans b) L = Formalism.HermitianLatticesTheory.gmap b (Formalism.HermitianLatticesTheory.gmap a L) := by
  simp only [Formalism.HermitianLatticesTheory.gmap, ← Submodule.map_comp]
  rfl

theorem IsAutLam_conj {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {n : S.V ≃ₗ[E] S.V} (h : IsAutLam S Λ n) : IsAutLam S (Formalism.HermitianLatticesTheory.gmap γ Λ) (conj γ n) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, ?_⟩
  · rw [conj_apply, conj_apply, iso_ap hγ, iso_ap h1, iso_ap (iso_symm hγ)]
  · rw [conj, gmap_trans, gmap_trans, gmap_symm_gmap, h2]

theorem NLam_conj {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (h : n ∈ NLam Λ F) :
    conj γ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨IsAutLam_conj hγ h1, fun j x hx => ?_, fun x hx => ?_⟩
  · rw [Xflag_mapL hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, h2 j y hy, ?_⟩
    simp [conj_apply, map_sub]
  · rw [Xsp_mapL hγ, orth_map hγ] at hx
    rw [Xsp_mapL hγ]
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, h3 y hy, ?_⟩
    simp [conj_apply, map_sub]

theorem rel_map {T T' : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) {Λ : Submodule (𝓞 E) S.V}
    {F : LFlag S r T} {F' F'' : LFlag S r T'}
    (h : ∃ n ∈ NLam Λ F, (∀ a, n (frame F a) = frame F a) ∧ ∀ b, n (frame F' b) = frame F'' b) :
    ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap γ Λ) (mapL γ hγ F),
      (∀ a, n (frame (mapL γ hγ F) a) = frame (mapL γ hγ F) a) ∧
        ∀ b, n (frame (mapL γ hγ F') b) = frame (mapL γ hγ F'') b := by
  obtain ⟨n, hn, h1, h2⟩ := h
  refine ⟨conj γ n, NLam_conj hγ hn, fun a => ?_, fun b => ?_⟩
  · simp only [frame_mapL' hγ, conj_apply, LinearEquiv.symm_apply_apply, h1]
  · simp only [frame_mapL' hγ, conj_apply, LinearEquiv.symm_apply_apply, h2]

end PI.RepsIndep.Tr
