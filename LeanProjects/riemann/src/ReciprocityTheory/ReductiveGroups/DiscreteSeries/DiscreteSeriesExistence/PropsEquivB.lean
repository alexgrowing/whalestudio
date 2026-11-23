import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.BridgeExpK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.UniqueA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

namespace KTypeIsomorphism

open Formalism.REAL

variable {n : ℕ}

section Transport

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def eV (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] :
    V ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  (stdOrthonormalBasis ℂ V).repr

def trOp (F : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) :
    Module.End ℂ (EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :=
  LinearEquiv.conjRingEquiv (eV V).toLinearEquiv (F a b)

theorem trOp_apply (F : Fin n → Fin n → Module.End ℂ V) (a b : Fin n)
    (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :
    trOp F a b x = eV V (F a b ((eV V).symm x)) := rfl

theorem trOp_kRel (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (h : KRel ε F) :
    KRel ε (trOp F) :=
  HW.uq_kRel_map ε F (LinearEquiv.conjRingEquiv (eV V).toLinearEquiv).toRingHom h

theorem trOp_kUnit (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (h : KUnit ε F) :
    KUnit ε (trOp F) := by
  intro a b hab x y
  rw [trOp_apply, trOp_apply]
  have h1 : y = eV V ((eV V).symm y) := ((eV V).apply_symm_apply y).symm
  have h2 : x = eV V ((eV V).symm x) := ((eV V).apply_symm_apply x).symm
  conv_lhs => rw [h1]
  conv_rhs => rw [h2]
  rw [(eV V).inner_map_map, (eV V).inner_map_map, h a b hab]

theorem trOp_kHighest (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) {Λ : Fin n → ℝ} {w : V}
    (h : KHighest ε F Λ w) : KHighest ε (trOp F) Λ (eV V w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [trOp_apply, LinearIsometryEquiv.symm_apply_apply, h.1 a, map_smul]
  · rw [trOp_apply, LinearIsometryEquiv.symm_apply_apply, h.2 a b hab he, map_zero]

theorem trOp_kSpan (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) {w : V}
    (hT : kSpan ε F w = ⊤) : kSpan ε (trOp F) (eV V w) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [kSpan, Submodule.mem_sInf]
  rintro S ⟨hwS, hSK⟩
  have hK : KStable ε F (S.comap (eV V).toLinearEquiv.toLinearMap) := by
    intro a b hab y hy
    show eV V (F a b y) ∈ S
    have := hSK a b hab (eV V y) hy
    rwa [trOp_apply, LinearIsometryEquiv.symm_apply_apply] at this
  have hle := HW.uq_kSpan_le ε F (show w ∈ S.comap (eV V).toLinearEquiv.toLinearMap from hwS) hK
  have hx := hle (show (eV V).symm x ∈ kSpan ε F w by rw [hT]; exact Submodule.mem_top)
  have : eV V ((eV V).symm x) ∈ S := hx
  rwa [LinearIsometryEquiv.apply_symm_apply] at this

theorem exists_kIso {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (F' : Fin n → Fin n → Module.End ℂ V')
    (Λ : Fin n → ℝ) (w : V) (w' : V') (hR : KRel ε F) (hR' : KRel ε F') (hU : KUnit ε F) (hU' : KUnit ε F')
    (hw : KHighest ε F Λ w) (hw' : KHighest ε F' Λ w') (hw1 : ‖w‖ = 1) (hw1' : ‖w'‖ = 1)
    (hT : kSpan ε F w = ⊤) (hT' : kSpan ε F' w' = ⊤) :
    ∃ φ : V ≃ₗᵢ[ℂ] V', ∀ a b, ε a = ε b → ∀ v, φ (F a b v) = F' a b (φ v) := by
  obtain ⟨ψ, hψ, -⟩ := HW.uq_exists_isometry ε (trOp F) (trOp F') Λ (eV V w) (eV V' w')
    (trOp_kRel ε F hR) (trOp_kRel ε F' hR') (trOp_kUnit ε F hU) (trOp_kUnit ε F' hU')
    (trOp_kHighest ε F hw) (trOp_kHighest ε F' hw') (by rw [(eV V).norm_map, hw1])
    (by rw [(eV V').norm_map, hw1']) (trOp_kSpan ε F hT) (trOp_kSpan ε F' hT')
  refine ⟨(eV V).trans (ψ.trans (eV V').symm), fun a b hab v => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  have h1 : eV V (F a b v) = trOp F a b (eV V v) := by
    rw [trOp_apply, LinearIsometryEquiv.symm_apply_apply]
  rw [h1, hψ a b hab, trOp_apply, LinearIsometryEquiv.symm_apply_apply]

end Transport

section Restrict

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}

def resE (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hst : IsKStableSub ε E V) (a b : Fin n) :
    Module.End ℂ V :=
  if h : ε a = ε b then (E a b).restrict (hst a b h) else 0

variable {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {hst : IsKStableSub ε E V}

theorem coe_resE {a b : Fin n} (h : ε a = ε b) (v : V) : ((resE E V hst a b v : V) : M) = E a b v := by
  rw [resE, dif_pos h]
  rfl

theorem resE_of_ne {a b : Fin n} (h : ¬ ε a = ε b) : resE E V hst a b = 0 := by
  rw [resE, dif_neg h]

theorem kRel_resE (hE : IsGlRep E) : KRel ε (resE E V hst) := by
  intro a b c d hab hcd
  apply LinearMap.ext; intro v; apply Subtype.ext
  have h := LinearMap.congr_fun (hE a b c d) (v : M)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2
    rw [if_pos rfl, if_pos rfl] at h ⊢
    simp only [Submodule.coe_sub, coe_resE hab, coe_resE hcd, coe_resE (rfl : ε d = ε d),
      coe_resE (rfl : ε b = ε b)]
    exact h
  · subst h1
    rw [if_pos rfl, if_neg h2] at h ⊢
    simp only [LinearMap.zero_apply, Submodule.coe_sub, Submodule.coe_zero, coe_resE hab, coe_resE hcd,
      coe_resE (hab.trans hcd)] at h ⊢
    exact h
  · subst h2
    rw [if_neg h1, if_pos rfl] at h ⊢
    simp only [LinearMap.zero_apply, Submodule.coe_sub, Submodule.coe_zero, coe_resE hab, coe_resE hcd,
      coe_resE (hcd.trans hab)] at h ⊢
    exact h
  · rw [if_neg h1, if_neg h2] at h ⊢
    simp only [LinearMap.zero_apply, Submodule.coe_sub, Submodule.coe_zero, coe_resE hab,
      coe_resE hcd] at h ⊢
    exact h

theorem kUnit_resE (hU : IsInfUnitary ε E) : KUnit ε (resE E V hst) := by
  intro a b hab x y
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_resE hab, coe_resE hab.symm, hU a b]
  simp [adjSign, hab]

theorem kHighest_resE {Λ : Fin n → ℝ} {w : M} (hwV : w ∈ V) (hw : IsKHWVec ε E Λ w) :
    KHighest ε (resE E V hst) Λ (⟨w, hwV⟩ : V) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · apply Subtype.ext
    rw [coe_resE rfl, Submodule.coe_smul]
    exact hw.1 a
  · apply Subtype.ext
    rw [coe_resE he]
    exact hw.2 a b hab he

theorem kHighest_smul {F : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {w : V}
    (hw : KHighest ε F Λ w) (c : ℂ) : KHighest ε F Λ (c • w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [map_smul, hw.1 a, smul_comm]
  · rw [map_smul, hw.2 a b hab he, smul_zero]

theorem kSpan_resE_top (hirr : ∀ S' : Submodule ℂ M, S' ≤ V → IsKStableSub ε E S' → S' = ⊥ ∨ S' = V)
    {w : V} (hw0 : w ≠ 0) : kSpan ε (resE E V hst) w = ⊤ := by
  set K := kSpan ε (resE E V hst) w
  have hKs : IsKStableSub ε E (K.map V.subtype) := by
    rintro a b hab _ ⟨y, hy, rfl⟩
    exact ⟨resE E V hst a b y, HW.uq_kSpan_stable ε _ w a b hab y hy, coe_resE hab y⟩
  have hKV : K.map V.subtype ≤ V := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  rcases hirr _ hKV hKs with h | h
  · exfalso
    apply hw0
    have : (w : M) ∈ K.map V.subtype := ⟨w, HW.uq_mem_kSpan ε _ w, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · apply Submodule.map_injective_of_injective V.injective_subtype
    rw [h, Submodule.map_subtype_top]

def resZ (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hst : IsKStableSub ε E V)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, Z a b • resE E V hst a b

theorem actM_coe {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (v : V) :
    actM E Z (v : M) = ((resZ E V hst Z v : V) : M) := by
  simp only [actM, resZ, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε a = ε b
  · rw [coe_resE h]
  · simp only [inK_apply_eq_zero hZ h, zero_smul]

theorem actM_pow_coe {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (v : V) (m : ℕ) :
    ((actM E Z) ^ m) (v : M) = ((((resZ E V hst Z) ^ m) v : V) : M) := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, actM_coe (hst := hst) hZ, pow_succ', Module.End.mul_apply]

end Restrict

section Orbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem orbit_hasSum (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hst : IsKStableSub ε E V) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z)
    (v : V) :
    HasSum (fun m : ℕ => (((1 : ℝ) / (m.factorial : ℝ) : ℝ) : ℂ) • ((((resZ E V hst Z) ^ m) v : V) : H))
      (σ (NormedSpace.exp Z) ((v : D) : H)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hst hVf hZ
  have hs : Summable fun m : ℕ => C ^ m * ‖(v : D)‖ * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    have := (Real.summable_pow_div_factorial C).mul_right ‖(v : D)‖
    refine this.congr fun m => ?_
    simp
    ring
  have hsum := hasSum_orbit_of_bound hσ hD hZ.1 (v : D) (fun m => C ^ m * ‖(v : D)‖)
    (fun m => hC (v : D) v.2 m) 0 1 hs
  rw [exp_zero_smul, hσ.1.1] at hsum
  simp only [Complex.ofReal_one, one_smul, ContinuousLinearMap.one_apply] at hsum
  convert hsum using 1
  funext m
  rw [actM_pow_coe (hst := hst) hZ v m]
  simp

variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)} {D₂ : Submodule ℂ H₂} {E₂ : Fin n → Fin n → Module.End ℂ D₂}

theorem phi_K (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {V : Submodule ℂ D}
    (hVf : FiniteDimensional ℂ V) (hst : IsKStableSub ε E V)
    (hσ₂ : IsURepOn (UJset ε) σ₂) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) {V₂ : Submodule ℂ D₂}
    (hVf₂ : FiniteDimensional ℂ V₂) (hst₂ : IsKStableSub ε E₂ V₂) (φ : V →ₗ[ℂ] V₂)
    (hcomm : ∀ a b, ε a = ε b → ∀ v, φ (resE E V hst a b v) = resE E₂ V₂ hst₂ a b (φ v)) :
    ∀ k ∈ Kset ε, ∀ (v : V) (w : V), ((w : D) : H) = σ k ((v : D) : H) →
      (((φ w : V₂) : D₂) : H₂) = σ₂ k (((φ v : V₂) : D₂) : H₂) := by
  have := hVf
  have := hVf₂
  intro k hk v w hvw
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hk
  have hc : ∀ a b v, φ (resE E V hst a b v) = resE E₂ V₂ hst₂ a b (φ v) := by
    intro a b v
    by_cases h : ε a = ε b
    · exact hcomm a b h v
    · simp only [resE_of_ne h, LinearMap.zero_apply, map_zero]
  have hZc : ∀ v, φ (resZ E V hst Z v) = resZ E₂ V₂ hst₂ Z (φ v) := by
    intro v
    simp only [resZ, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hc]
  have hZp : ∀ m v, φ (((resZ E V hst Z) ^ m) v) = ((resZ E₂ V₂ hst₂ Z) ^ m) (φ v) := by
    intro m
    induction m with
    | zero => intro v; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, hZc, ih, pow_succ', Module.End.mul_apply]
  let ι₁ : V →L[ℂ] H := D.subtypeL.comp V.subtypeL
  let ι₂ : V₂ →L[ℂ] H₂ := D₂.subtypeL.comp V₂.subtypeL
  have hi : Topology.IsInducing ι₁ :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have h1 := orbit_hasSum hσ hD hVf hst hZ v
  rw [← hvw] at h1
  have h1' : HasSum (fun m : ℕ => (((1 : ℝ) / (m.factorial : ℝ) : ℝ) : ℂ) • (((resZ E V hst Z) ^ m) v)) w := by
    rw [← hi.hasSum_iff]
    exact h1
  have h3 := (h1'.mapL (LinearMap.toContinuousLinearMap φ)).mapL ι₂
  have h4 := orbit_hasSum hσ₂ hD₂ hVf₂ hst₂ hZ (φ v)
  refine h3.unique ?_
  convert h4 using 1
  funext m
  simp only [LinearMap.coe_toContinuousLinearMap', map_smul, hZp]
  try rfl

end Orbit

end KTypeIsomorphism

end ReciprocityTheory.ChartRestriction.DS
