import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace Formalism.MainNotions.N.K.Norm

section ConjM

variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

def IsConjM (M M' : Γ → Matrix n n K) : Prop :=
  ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ ∀ g, P * M g = M' g * P

theorem IsConjM.refl (M : Γ → Matrix n n K) : IsConjM M M :=
  ⟨1, 1, by simp, by simp, fun g => by simp⟩

theorem IsConjM.symm {M M' : Γ → Matrix n n K} (h : IsConjM M M') : IsConjM M' M := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨Q, P, h2, h1, fun g => ?_⟩
  calc Q * M' g = Q * M' g * (P * Q) := by rw [h1, Matrix.mul_one]
    _ = Q * (M' g * P) * Q := by simp only [Matrix.mul_assoc]
    _ = Q * (P * M g) * Q := by rw [h3]
    _ = M g * Q := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem IsConjM.comp {M M' : Γ → Matrix n n K} (h : IsConjM M M') {Γ' : Type} (f : Γ' → Γ) :
    IsConjM (fun g => M (f g)) (fun g => M' (f g)) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => h3 (f g)⟩

theorem IsConjM.map {M M' : Γ → Matrix n n K} (h : IsConjM M M') {S : Type} [CommRing S] (f : K →+* S) :
    IsConjM (fun g => (M g).map f) (fun g => (M' g).map f) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨P.map f, Q.map f, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.map_mul, h1, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, h2, Matrix.map_one _ f.map_zero f.map_one]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, h3]

theorem IsConjM.smul {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K) :
    IsConjM (fun g => c g • M g) (fun g => c g • M' g) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [Matrix.mul_smul, Matrix.smul_mul, h3]⟩

theorem IsConjM.dual [Group Γ] {M M' : Γ → Matrix n n K} (h : IsConjM M M') :
    IsConjM (fun g => (M g⁻¹).transpose) (fun g => (M' g⁻¹).transpose) := by
  obtain ⟨Q, P, h2, h1, h3⟩ := h.symm
  refine ⟨Q.transpose, P.transpose, ?_, ?_, fun g => ?_⟩
  · rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, h2, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, h3]

end ConjM

section MatRep

variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}

theorem matRep_apply (M : Γ →* Matrix (Fin k) (Fin k) K) (g : Γ) (v : Fin k → K) :
    matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

def matEquiv (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) :
    (Fin k → K) ≃ₗ[K] (Fin k → K) where
  toLinearMap := Matrix.toLin' P
  invFun v := Q.mulVec v
  left_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  right_inv v := by simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1]

theorem matEquiv_apply (P Q : Matrix (Fin k) (Fin k) K) (h1 : P * Q = 1) (h2 : Q * P = 1) (v : Fin k → K) :
    matEquiv P Q h1 h2 v = P.mulVec v := rfl

theorem exists_equiv_of_conj {M M' : Γ →* Matrix (Fin k) (Fin k) K} (h : IsConjM ⇑M ⇑M') :
    ∃ e : (Fin k → K) ≃ₗ[K] (Fin k → K), ∀ g v, e (matRep M g v) = matRep M' g (e v) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨matEquiv P Q h1 h2, fun g v => ?_⟩
  rw [matEquiv_apply, matEquiv_apply, matRep_apply, matRep_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]

end MatRep

section Inv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem isCrys_congr (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  let E : V ⊗[Qp] B ≃ₗ[LL] V' ⊗[Qp] B := AlgebraTensorModule.congr e (LinearEquiv.refl Qp B)
  have hE : ∀ g x, E (actVB PD ρ g x) = actVB PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVB, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hD : Dcris PD ρ = (Dcris PD ρ').comap (E : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B) := by
    ext x
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsCrys at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (Dcris PD ρ')).finrank_eq.symm

omit he in
theorem filV_map_tmul (a : ℤ) (y : V ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp)) :
    AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype y) =
      AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL] V') ((PD.Fil a).restrictScalars Qp).subtype
        (AlgebraTensorModule.congr e (LinearEquiv.refl Qp _) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

omit he in
theorem congr_symm_tmul (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp BdR)
      (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem mem_fildR_iff (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) x ∈ FildR PD ρ' τ a := by
  set E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) with hEd
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hM : ∀ c x, E (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c x) =
      mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL) c (E x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, mulVdR]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  have hF : x ∈ FilV PD (LL := LL) (V := V) a ↔ E x ∈ FilV PD (LL := LL) (V := V') a := by
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (filV_map_tmul PD e a y).symm⟩
    · rintro ⟨y, hy⟩
      refine ⟨AlgebraTensorModule.congr e.symm (LinearEquiv.refl Qp _) y, ?_⟩
      rw [← filV_map_tmul PD e.symm a y, hy, hEd, congr_symm_tmul]
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
  refine and_congr (and_congr ⟨fun h g => ?_, fun h g => E.injective ?_⟩ ⟨fun h c => ?_, fun h c => E.injective ?_⟩) hF
  · rw [← hE, h g]
  · rw [hE]; exact h g
  · rw [← hM, h c, map_smul]
  · rw [hM, map_smul]; exact h c

theorem fildR_eq_comap (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FildR PD ρ' τ a).comap
      (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR) : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
  ext x
  exact mem_fildR_iff PD e he τ a x

theorem isJumpV_congr (τ : K →ₐ[Qp] LL) (a : ℤ) : IsJumpV PD ρ τ a ↔ IsJumpV PD ρ' τ a := by
  unfold IsJumpV
  rw [fildR_eq_comap PD e he, fildR_eq_comap PD e he]
  exact not_congr (Submodule.comap_injective_of_surjective
    (AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).surjective).eq_iff

theorem multV_congr (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  unfold multV
  rw [fildR_eq_comap PD e he, fildR_eq_comap PD e he,
    ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ a)).finrank_eq,
    ((AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)).ofSubmodule' (FildR PD ρ' τ (a + 1))).finrank_eq]

end Inv

section Sums

variable {G : Type} [Group G] {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]
  (ρ : Representation LL G V) {ι : Type} {k : ℕ}

theorem isSubOfSums_of_conj (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubOfSums ρ Ms') : IsSubOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, j, hj, hjg⟩ := h
  refine ⟨m, xs, LinearMap.pi (fun a => (Matrix.toLin' (P (xs a))) ∘ₗ (LinearMap.proj a ∘ₗ j)), ?_, fun g v => ?_⟩
  · intro v w hvw
    apply hj
    funext a
    have h0 := congrArg (Matrix.mulVec (Q (xs a))) (congrFun hvw a)
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h0
    exact h0
  · funext a
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Matrix.toLin'_apply]
    rw [hjg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]

theorem isSubquotOfSums_of_conj (Ms Ms' : ι → G → Matrix (Fin k) (Fin k) LL) (hc : ∀ x, IsConjM (Ms x) (Ms' x))
    (h : IsSubquotOfSums ρ Ms') : IsSubquotOfSums ρ Ms := by
  choose P Q h1 h2 h3 using fun x => (hc x).symm
  obtain ⟨m, xs, U, q, hU, hq, hqg⟩ := h
  let Φ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (P (xs a)) ∘ₗ LinearMap.proj a
  let Ψ : (Fin m → Fin k → LL) →ₗ[LL] (Fin m → Fin k → LL) :=
    LinearMap.pi fun a => Matrix.toLin' (Q (xs a)) ∘ₗ LinearMap.proj a
  have hΦ : ∀ u a, Φ u a = (P (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨ : ∀ u a, Ψ u a = (Q (xs a)).mulVec (u a) := fun _ _ => rfl
  have hΨΦ : ∀ u, Ψ (Φ u) = u := by
    intro u
    funext a
    rw [hΨ, hΦ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  have hcomm : ∀ g u, (fun a => (Ms (xs a) g).mulVec (Φ u a)) = Φ (fun a => (Ms' (xs a) g).mulVec (u a)) := by
    intro g u
    funext a
    rw [hΦ, hΦ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
  refine ⟨m, xs, U.map Φ, q ∘ₗ Ψ, ?_, ?_, ?_⟩
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨_, hU g u hu, (hcomm g u).symm⟩
  · intro v
    obtain ⟨u, hu, rfl⟩ := hq v
    exact ⟨Φ u, ⟨u, hu, rfl⟩, by rw [LinearMap.comp_apply, hΨΦ]⟩
  · rintro g _ ⟨u, hu, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcomm, hΨΦ, hΨΦ]
    exact hqg g u hu

end Sums

section SS

variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem isSS_congr (h : IsSS ρ) : IsSS ρ' := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h (W.comap (e : V →ₗ[Kf] V')) (fun g v hv => by
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, he] at hv ⊢
    exact hW g _ hv)
  refine ⟨W'.map (e : V →ₗ[Kf] V'), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hW' g v hv, he g v⟩
  · have h1 : IsCompl ((W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V')) (W'.map (e : V →ₗ[Kf] V')) :=
      (Submodule.orderIsoMapComap e).isCompl_iff.1 hc
    have h2 : (W.comap (e : V →ₗ[Kf] V')).map (e : V →ₗ[Kf] V') = W :=
      Submodule.map_comap_eq_of_surjective e.surjective W
    rw [h2] at h1
    exact h1

end SS

section Abs

variable {Kf : Type} [Field Kf] {Γ : Type} [Group Γ] {V V' : Type} [AddCommGroup V] [Module Kf V]
  [AddCommGroup V'] [Module Kf V'] {ρ : Representation Kf Γ V} {ρ' : Representation Kf Γ V'}
  (e : V ≃ₗ[Kf] V') (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem absIrrDistinct_congr (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  let Vs' : ι → Submodule Kf V' := fun j => (Vs j).map (e : V →ₗ[Kf] V')
  have hs' : ∀ j, Stable ρ' (Vs' j) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, he g v⟩
  let ej : ∀ j, Vs j ≃ₗ[Kf] Vs' j := fun j => e.submoduleMap (Vs j)
  have hej : ∀ j g (v : Vs j), ej j ((ρ g).restrict (hs j g) v) = (ρ' g).restrict (hs' j g) (ej j v) := by
    intro j g v
    apply Subtype.ext
    exact he g v
  refine ⟨ι, hι, hd, Vs', hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    obtain ⟨hind, htop⟩ := hint
    refine ⟨hind.map_orderIso (Submodule.orderIsoMapComap e), ?_⟩
    show ⨆ j, (Vs j).map (e : V →ₗ[Kf] V') = ⊤
    rw [← Submodule.map_iSup, htop, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    apply hne j
    have h1 := congrArg (Submodule.comap (e : V →ₗ[Kf] V')) hj
    rwa [Submodule.comap_map_eq_of_injective e.injective, Submodule.comap_bot, LinearEquiv.ker] at h1
  · intro j
    let c : Module.End Kf (Vs j) ≃ₗ[Kf] Module.End Kf (Vs' j) := LinearEquiv.conj (ej j)
    have hc : ∀ g, c ((ρ g).restrict (hs j g)) = (ρ' g).restrict (hs' j g) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [LinearEquiv.conj_apply]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [hej, LinearEquiv.apply_symm_apply]
    have hr : Set.range (fun g => (ρ' g).restrict (hs' j g)) =
        (c : Module.End Kf (Vs j) →ₗ[Kf] Module.End Kf (Vs' j)) '' Set.range (fun g => (ρ g).restrict (hs j g)) := by
      ext f
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨_, ⟨g, rfl⟩, hc g⟩
      · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
        exact ⟨g, (hc g).symm⟩
    rw [hr, ← Submodule.map_span, hspan j, Submodule.map_top, LinearEquiv.range]
  · intro j j' hjj f hf
    apply hdist j j' hjj (((ej j).trans f).trans (ej j').symm)
    intro g v
    simp only [LinearEquiv.trans_apply]
    rw [hej, hf]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (ej j') (f (ej j v)), ← hej, LinearEquiv.symm_apply_apply]

end Abs

end Formalism.MainNotions.N.K.Norm
