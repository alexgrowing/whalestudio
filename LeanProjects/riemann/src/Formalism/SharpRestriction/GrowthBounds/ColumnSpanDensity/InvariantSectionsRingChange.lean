import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.IsLatticeMapSubIff

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section Lat

variable {O₁ K₁ O₂ K₂ : Type} [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [CommRing O₂] [Field K₂] [Algebra O₂ K₂]
  (J : Iso2 O₁ K₁ O₂ K₂)

abbrev Iso2.pm {σ : Type*} : MvPolynomial σ K₁ →+* MvPolynomial σ K₂ := map (J.φF : K₁ →+* K₂)

theorem det_map (k : ℕ) (g : Matrix (Fin k) (Fin k) K₁) : (g.map J.φF).det = J.φF g.det :=
  (RingHom.map_det (J.φF : K₁ →+* K₂) g).symm

theorem nablaL_tr (k n : ℕ) (ν : Fin n → ℕ) (g : Matrix (Fin k) (Fin k) K₁) (F : MvPolynomial (Fin k × Fin n) K₁)
    (hF : F ∈ nablaL O₁ K₁ k n ν g) : J.pm F ∈ nablaL O₂ K₂ k n ν (g.map J.φF) := by
  unfold nablaL at hF ⊢
  rw [Submodule.mem_comap, Submodule.mem_map] at hF ⊢
  obtain ⟨D, hD, hDe⟩ := hF
  refine ⟨map (J.φR : O₁ →+* O₂) D, dualWeyl_map _ hD, ?_⟩
  simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply] at hDe ⊢
  have key := rowAct_map' (n := n) (J.φF : K₁ →+* K₂) g F
  rw [RingEquiv.coe_toRingHom] at key
  rw [key, ← hDe]
  simp only [mapAlgHom_apply, map_map]
  have hc : (Algebra.ofId O₂ K₂ : O₂ →+* K₂).comp (J.φR : O₁ →+* O₂) =
      (J.φF : K₁ →+* K₂).comp (Algebra.ofId O₁ K₁ : O₁ →+* K₁) := by
    ext x
    simp [J.h]
  rw [hc]

theorem nablaLTw_tr (m : ℕ) (lam : Fin (m + 1) → ℤ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K₁)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K₁) (hF : F ∈ nablaLTw O₁ K₁ m lam g) :
    J.pm F ∈ nablaLTw O₂ K₂ m lam (g.map J.φF) := by
  unfold nablaLTw at hF ⊢
  rw [Submodule.mem_map] at hF ⊢
  obtain ⟨G, hG, rfl⟩ := hF
  refine ⟨J.pm G, nablaL_tr J _ _ _ g G hG, ?_⟩
  simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply, det_map, Iso2.pm, map_smul', map_zpow₀,
    RingEquiv.coe_toRingHom]

theorem invariant_sections_ring_change (m : ℕ) (lam : Fin (m + 1) → ℤ) (Λ : Submodule O₁ (Fin (m + 1) → K₁))
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K₁) (hF : F ∈ H0 O₁ m lam Λ) :
    J.pm F ∈ H0 O₂ m lam (mapSub J Λ) := by
  unfold H0 at hF ⊢
  split_ifs at hF ⊢ with ha
  · rw [Submodule.mem_iInf] at hF ⊢
    intro g₂
    rw [Submodule.mem_iInf]
    rintro ⟨hu, hΛ⟩
    have h1 := hF (g₂.map J.symm.φF)
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 ⟨by rw [det_map J.symm]; exact hu.map _, by rw [← mapSub_symm J Λ, hΛ, mapSub_colSpan]⟩
    have h3 := nablaLTw_tr J m lam _ F h2
    have hg : (g₂.map J.symm.φF).map J.φF = g₂ := by
      ext i j
      simp [Iso2.symm]
    rwa [hg] at h3
  · rw [Submodule.mem_bot] at hF ⊢
    simp [hF]

theorem tensorLat_tr {S : Type*} [Fintype S] {k n : ℕ} (M : S → Submodule O₁ (MvPolynomial (Fin k × Fin n) K₁))
    (M' : S → Submodule O₂ (MvPolynomial (Fin k × Fin n) K₂)) (h : ∀ s F, F ∈ M s → J.pm F ∈ M' s) :
    ∀ P ∈ tensorLat O₁ K₁ M, J.pm P ∈ tensorLat O₂ K₂ M' := by
  intro P hP
  unfold tensorLat at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => J.pm (F s), fun s => h s (F s) (hF s), ?_⟩
    simp only [Iso2.pm, map_prod, blockEmb, map_rename]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Iso2.pm, map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul K₁ c x, Iso2.pm, map_smul', RingEquiv.coe_toRingHom, J.h, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

end Lat

section RSl

variable {p n' : ℕ} {R₁ R₂ : RS p n'} (I : RSIso R₁ R₂)

def RSIso.JW : Iso2 R₁.W R₁.Qq R₂.W R₂.Qq := ⟨I.φW, I.φQ, I.hWQ⟩
def RSIso.JO : Iso2 R₁.O R₁.Kf R₂.O R₂.Kf := ⟨I.φO, I.φK, I.hOK⟩
def RSIso.JK : Iso2 R₁.Kf R₁.Kf R₂.Kf R₂.Kf := ⟨I.φK, I.φK, fun _ => rfl⟩

def RSIso.symm : RSIso R₂ R₁ where
  φW := I.φW.symm
  φQ := I.φQ.symm
  φO := I.φO.symm
  φK := I.φK.symm
  hWQ := I.JW.symm.h
  hOK := I.JO.symm.h
  hι x := by
    apply I.φK.injective
    rw [RingEquiv.apply_symm_apply, I.hι, RingEquiv.apply_symm_apply]
  hσ x := by
    apply I.φQ.injective
    rw [RingEquiv.apply_symm_apply, I.hσ, RingEquiv.apply_symm_apply]
  hj x := by
    apply I.φO.injective
    rw [RingEquiv.apply_symm_apply, I.hj, RingEquiv.apply_symm_apply]
  hw := by
    rw [← I.hw, RingEquiv.symm_apply_apply]

theorem RSIso.hσs (s : ℕ) (x : R₁.Qq) : I.φQ ((R₁.σ ^ s) x) = (R₂.σ ^ s) (I.φQ x) := by
  induction s generalizing x with
  | zero => rfl
  | succ s ih =>
    rw [pow_succ, pow_succ]
    show I.φQ ((R₁.σ ^ s) (R₁.σ x)) = (R₂.σ ^ s) (R₂.σ (I.φQ x))
    rw [ih, I.hσ]

theorem twist_tr (s : ℕ) {k : ℕ} (v : Fin k → R₁.Qq) :
    (fun i => I.φK (twistVec R₁.ι R₁.σ s v i)) = twistVec R₂.ι R₂.σ s (fun i => I.φQ (v i)) := by
  funext i
  simp only [twistVec]
  rw [I.hι, I.hσs]

theorem img1 (s : ℕ) {k : ℕ} (L : Submodule R₁.W (Fin k → R₁.Qq)) :
    (fun (x : Fin k → R₁.Kf) i => I.JO.φF (x i)) '' (twistVec R₁.ι R₁.σ s '' (L : Set (Fin k → R₁.Qq))) =
      twistVec R₂.ι R₂.σ s '' (mapSub I.JW L : Set (Fin k → R₂.Qq)) := by
  rw [Set.image_image]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨fun i => I.φQ (v i), (map_mem_mapSub I.JW L v).2 hv, ?_⟩
    exact (twist_tr I s v).symm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => I.φQ.symm (u i), (mem_mapSub I.JW L u).1 hu, ?_⟩
    show (fun i => I.φK (twistVec R₁.ι R₁.σ s (fun i => I.φQ.symm (u i)) i)) = _
    rw [twist_tr]
    simp

theorem extO_tr (s : ℕ) {k : ℕ} (L : Submodule R₁.W (Fin k → R₁.Qq)) :
    mapSub I.JO (extO R₁.O R₁.ι R₁.σ s L) = extO R₂.O R₂.ι R₂.σ s (mapSub I.JW L) := by
  unfold extO
  rw [mapSub_span, img1]

private theorem phiF_inv_smul_twistVec_eq (s : ℕ) {k : ℕ} (v : Fin k → R₁.Qq) :
    (fun i => I.JO.φF (((algebraMap R₁.O R₁.Kf R₁.w)⁻¹ • twistVec R₁.ι R₁.σ s ((p : R₁.W) • v)) i)) =
      (algebraMap R₂.O R₂.Kf R₂.w)⁻¹ • twistVec R₂.ι R₂.σ s ((p : R₂.W) • fun i => I.φQ (v i)) := by
  have e1 : (p : R₂.W) • (fun i => I.φQ (v i)) = fun i => I.φQ (((p : R₁.W) • v) i) := by
    funext j
    simp [Algebra.smul_def, I.hWQ]
  rw [e1, ← twist_tr]
  funext i
  show I.φK _ = _
  simp [smul_eq_mul, map_mul, map_inv₀, I.hOK, I.hw]

theorem img2 (s : ℕ) {k : ℕ} (L : Submodule R₁.W (Fin k → R₁.Qq)) :
    (fun (x : Fin k → R₁.Kf) i => I.JO.φF (x i)) ''
        ((fun v => (algebraMap R₁.O R₁.Kf R₁.w)⁻¹ • twistVec R₁.ι R₁.σ s ((p : R₁.W) • v)) ''
          (L : Set (Fin k → R₁.Qq))) =
      (fun v => (algebraMap R₂.O R₂.Kf R₂.w)⁻¹ • twistVec R₂.ι R₂.σ s ((p : R₂.W) • v)) ''
        (mapSub I.JW L : Set (Fin k → R₂.Qq)) := by
  rw [Set.image_image]
  ext y
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨fun i => I.φQ (v i), (map_mem_mapSub I.JW L v).2 hv, (phiF_inv_smul_twistVec_eq I s v).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => I.φQ.symm (u i), (mem_mapSub I.JW L u).1 hu, ?_⟩
    exact (phiF_inv_smul_twistVec_eq I s _).trans (by simp)

theorem LeAt_tr (s : ℕ) {k : ℕ} (e : Edge R₁.W R₁.Qq k) :
    mapSub I.JO (LeAt p R₁.ι R₁.σ R₁.w s e) =
      LeAt p R₂.ι R₂.σ R₂.w s ⟨mapSub I.JW e.src, mapSub I.JW e.tgt⟩ := by
  unfold LeAt extO
  rw [← Submodule.span_union, mapSub_span, Set.image_union, Submodule.span_union, img1, img2]

theorem Hten_tr {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (Λ : Fin n' → Submodule R₁.O (Fin (m + 1) → R₁.Kf))
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) (hP : P ∈ Hten R₁.O lam0 Λ) :
    I.JO.pm P ∈ Hten R₂.O lam0 (fun s => mapSub I.JO (Λ s)) := by
  unfold Hten at hP ⊢
  exact tensorLat_tr I.JO _ _ (fun s F hF => invariant_sections_ring_change I.JO m _ _ F hF) P hP

theorem Vsp_tr {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (P : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) R₁.Kf) (hP : P ∈ Vsp R₁.Kf lam0) :
    I.JO.pm P ∈ Vsp R₂.Kf lam0 := by
  unfold Vsp at hP ⊢
  refine tensorLat_tr I.JK _ _ (fun s F hF => ?_) P hP
  split_ifs at hF ⊢
  · exact dualWeyl_map _ hF
  · rw [Submodule.mem_bot] at hF ⊢
    simp [hF]

end RSl

end Formalism.MainNotions.flipOneThree.Pf

end
