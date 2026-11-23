import Formalism.SharpRestriction.GrowthBounds.ChartRank.HypLift

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCmpLiftDesc

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Module Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PCard Formalism.MainNotions.G.CmpJ.PRankGe Formalism.MainNotions.G.CmpJ.PInvLe Formalism.MainNotions.G.CmpJ.PFormsCl Formalism.MainNotions.G.CmpJ.PCmpLift

section Desc

variable {LL K : Type} [Field LL] [Field K] (e : LL →+* K)

theorem lin_ext_map {σ : Type} (φ : MvPolynomial σ LL →ₗ[LL] LL) (P : MvPolynomial σ LL) :
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
      (MvPolynomial.map e P) = e (φ P) := by
  induction P using MvPolynomial.induction_on'
  next u a =>
    have h1 : MvPolynomial.map e (MvPolynomial.monomial u a) = e a • MvPolynomial.basisMonomials σ K u := by
      simp only [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h2 : MvPolynomial.monomial u a = a • MvPolynomial.monomial u (1 : LL) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, Basis.constr_basis, h2, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  next p q hp hq =>
    simp only [map_add, hp, hq]

theorem desc_span {σ : Type} (V : Submodule LL (MvPolynomial σ LL)) {Q : MvPolynomial σ LL}
    (hQ : MvPolynomial.map e Q ∈ Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL)))) : Q ∈ V := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  let φK : MvPolynomial σ K →ₗ[K] K :=
    (MvPolynomial.basisMonomials σ K).constr K (fun m : σ →₀ ℕ => e (φ (MvPolynomial.monomial m 1)))
  have h1 : Submodule.span K (MvPolynomial.map e '' (V : Set (MvPolynomial σ LL))) ≤ LinearMap.ker φK := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change φK (MvPolynomial.map e v) = 0
    rw [lin_ext_map e φ v, (Submodule.mem_dualAnnihilator φ).1 hφ v hv, map_zero]
  have h2 : φK (MvPolynomial.map e Q) = 0 := h1 hQ
  rw [lin_ext_map e φ Q] at h2
  exact (map_eq_zero_iff e e.injective).1 h2

theorem dw_desc {r n : ℕ} (ν : Fin n → ℕ) {f : MvPolynomial (Fin r × Fin n) LL}
    (h : MvPolynomial.map e f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl LL r n ν := by
  rw [Formalism.GradedWeylDivisibility.mem_dualWeyl_iff, isWH_iff] at h ⊢
  refine ⟨MvPolynomial.map_injective e e.injective ?_, fun l j hlj => MvPolynomial.map_injective e e.injective ?_⟩
  · rw [whc_map, h.1]
  · rw [colAddGen_map, MvPolynomial.map_rename, h.2 l j hlj]

theorem dw_span {r n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl K r n ν ≤
      Submodule.span K (MvPolynomial.map e '' (Formalism.GradedWeylDivisibility.dualWeyl LL r n ν : Set (MvPolynomial (Fin r × Fin n) LL))) := by
  refine (dualWeyl_desc e ν).trans (Submodule.span_mono ?_)
  rintro _ ⟨Q, hQ, rfl⟩
  exact ⟨Q, dw_desc e ν hQ, rfl⟩

theorem span_prod_le {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K)) (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL))
    (hM : ∀ s, Ms s ≤ Submodule.span K (MvPolynomial.map e '' (Ns s : Set (MvPolynomial (σ s) LL)))) :
    Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} ≤
      Submodule.span K (MvPolynomial.map e '' (Submodule.span LL
        {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} :
          Set (MvPolynomial τ LL))) := by
  rw [Submodule.span_le]
  rintro _ ⟨F, hF, rfl⟩
  let A : S → Set (MvPolynomial τ K) := fun s =>
    {y | ∃ Q : MvPolynomial (σ s) LL, Q ∈ Ns s ∧ y = MvPolynomial.rename (f s) (MvPolynomial.map e Q)}
  have hx : ∀ s ∈ Finset.univ, MvPolynomial.rename (f s) (F s) ∈ Submodule.span K (A s) := by
    intro s _
    have h1 := Submodule.mem_map_of_mem (f := (MvPolynomial.rename (R := K) (f s)).toLinearMap) (hM s (hF s))
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨Q, hQ, rfl⟩, rfl⟩
    exact ⟨Q, hQ, rfl⟩
  have h := prod_mem_span Finset.univ A _ hx
  refine Submodule.span_mono ?_ h
  rintro _ ⟨a, ha, rfl⟩
  choose Q hQ hQe using fun s => ha s (Finset.mem_univ s)
  refine ⟨∏ s, MvPolynomial.rename (f s) (Q s), Submodule.subset_span ⟨Q, hQ, rfl⟩, ?_⟩
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hQe s, MvPolynomial.map_rename]

theorem vsp_span {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) :
    Vsp K lam0 ≤ Submodule.span K (MvPolynomial.map e '' (Vsp LL lam0 : Set (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL))) := by
  have hM : ∀ s : Fin n', (if Antitone (lamAt lam0 s) then Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥) ≤
      Submodule.span K (MvPolynomial.map e '' (((if Antitone (lamAt lam0 s) then
        Formalism.GradedWeylDivisibility.dualWeyl LL (m + 1) (m + 1) (nuOf (lamAt lam0 s)) else ⊥ : Submodule LL _)) : Set (MvPolynomial (Fin (m + 1) × Fin (m + 1)) LL))) := by
    intro s
    split_ifs
    · exact dw_span e _
    · exact bot_le
  exact span_prod_le e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ hM

theorem vtup_span {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) : VtupR P K ≤ Submodule.span K (MvPolynomial.map e '' (VtupR P LL : Set (XR P LL))) :=
  span_prod_le e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    fun v => vsp_span e (P.lam0 v)

theorem span_prod_map {S : Type} [Fintype S] {σ : S → Type} {τ : Type} (f : ∀ s, σ s → τ)
    (Ns : ∀ s, Submodule LL (MvPolynomial (σ s) LL)) (Ms : ∀ s, Submodule K (MvPolynomial (σ s) K))
    (h : ∀ s, ∀ x ∈ Ns s, MvPolynomial.map e x ∈ Ms s) {Z : MvPolynomial τ LL}
    (hZ : Z ∈ Submodule.span LL {Z | ∃ F : ∀ s, MvPolynomial (σ s) LL, (∀ s, F s ∈ Ns s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)}) :
    MvPolynomial.map e Z ∈
      Submodule.span K {Z | ∃ F : ∀ s, MvPolynomial (σ s) K, (∀ s, F s ∈ Ms s) ∧ Z = ∏ s, MvPolynomial.rename (f s) (F s)} := by
  induction hZ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    refine Submodule.subset_span ⟨fun s => MvPolynomial.map e (F s), fun s => h s _ (hF s), ?_⟩
    simp only [map_prod, MvPolynomial.map_rename]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mapE_smul]; exact Submodule.smul_mem _ _ hx

theorem vsp_map {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) {x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) LL}
    (hx : x ∈ Vsp LL lam0) : MvPolynomial.map e x ∈ Vsp K lam0 := by
  refine span_prod_map e (σ := fun _ => Fin (m + 1) × Fin (m + 1)) (fun s v => (s, v)) _ _ (fun s y hy => ?_) hx
  split_ifs at hy ⊢
  · exact Formalism.GradedWeylDivisibility.dualWeylMap LL K e _ _ _ y hy
  · rw [(Submodule.mem_bot _).1 hy, map_zero]
    exact Submodule.zero_mem _

theorem vtup_map {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {Q : XR P LL} (hQ : Q ∈ VtupR P LL) : MvPolynomial.map e Q ∈ VtupR P K :=
  span_prod_map e (σ := fun v => Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) (fun v x => (⟨v, x⟩ : Var P)) _ _
    (fun v _ hy => vsp_map e (P.lam0 v) hy) hQ

end Desc

section Rec

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem vtupDesc_holds (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) : VtupDesc S e := by
  intro β Q hQ
  exact vtup_map D.what₂.embLL _ (desc_span e (VtupR (Hc S β).P D.what₂.LL) (vtup_span e (Hc S β).P hQ))

theorem cmpLiftOf_of_two (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf) (hV : ∀ β, EvValLe S β) (hI : CmpInvOf S e) :
    CmpLiftOf S e :=
  cmpLiftOf_of S e (vtupDesc_holds S e) hV hI

end Rec

end Formalism.MainNotions.G.CmpJ.PCmpLiftDesc
