import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ProdModeCharExp

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

theorem kset_mem_UJset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : k ∈ UJset ε := by
  show kᴴ * Jm ε * k = Jm ε
  rw [mul_assoc, ← hk.2, ← mul_assoc, ← Matrix.star_eq_conjTranspose,
    (Matrix.mem_unitaryGroup_iff').1 hk.1, one_mul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_sigD (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (u v : D) : inner ℂ (sigD hD hk u) (sigD hD hk v) = inner ℂ u v := by
  let Lk : H →ₗᵢ[ℂ] H := { toLinearMap := (σ k : H →ₗ[ℂ] H), norm_map' := hσ.2.1 k (kset_mem_UJset hk) }
  rw [Submodule.coe_inner, Submodule.coe_inner]
  exact Lk.inner_map_map u v

theorem coord_ff_basis (k : Matrix (Fin n) (Fin n) ℂ) (s s' : Finset (Fin (n * n))) :
    (fockBasis n).coord s (ff ε k (fockBasis n s')) = ffMat ε k s s' := by
  rw [ffMat, LinearMap.toMatrix_apply, Module.Basis.coord_apply, AlgHom.toLinearMap_apply]

theorem tform_wK (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (y y' : TensorProduct ℂ D (Fock n)) :
    tform (wK hD hk y) (wK hD hk y') = tform y y' := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 (ffMat_unitary (ε := ε) hk)
  unfold tform
  simp only [tco_wK, coord_ff_basis, sum_inner, inner_sum, inner_smul_left, inner_smul_right, inner_sigD hσ hD hk,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.sum_comm]
  have h1 : ∀ s'' : Finset (Fin (n * n)), ∑ x, ffMat ε k x s' * ((starRingEnd ℂ) (ffMat ε k x s'') *
      inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y')) =
      (1 : Matrix (Finset (Fin (n * n))) (Finset (Fin (n * n))) ℂ) s'' s' *
        inner ℂ (tcoef ((fockBasis n).coord s'') y) (tcoef ((fockBasis n).coord s') y') := by
    intro s''
    rw [← hU, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.star_apply, Complex.star_def]
    ring
  rw [Finset.sum_congr rfl fun s'' _ => h1 s'']
  simp [Matrix.one_apply]

theorem sigD_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    sigD hD h1 = LinearMap.id := by
  ext v
  simp [sigD, hσ.1.1]

theorem wK_one (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    wK hD h1 = LinearMap.id := by
  rw [wK, sigD_one hσ hD h1, ff_one]
  exact TensorProduct.map_id

theorem wK_mul (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) (hab : a * b ∈ Kset ε) :
    wK hD hab = wK hD ha ∘ₗ wK hD hb := by
  have hs : sigD hD hab = sigD hD ha ∘ₗ sigD hD hb := by
    ext v
    simp [sigD, hσ.1.2 a (kset_mem_UJset ha) b (kset_mem_UJset hb)]
  rw [wK, wK, wK, hs, ff_mul ha hb, ← TensorProduct.map_comp]
  rfl

theorem one_mem_Kset' : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨one_mem _, by rw [one_mul, mul_one]⟩

theorem mul_mem_Kset' {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Kset ε) (hb : b ∈ Kset ε) : a * b ∈ Kset ε :=
  ⟨mul_mem ha.1 hb.1, by rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]⟩

section TSubSec

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def TSub (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : Type _ := S

variable {S : Submodule ℂ (TensorProduct ℂ M (Fock n))}

instance : AddCommGroup (TSub S) := inferInstanceAs (AddCommGroup S)

instance : Module ℂ (TSub S) := inferInstanceAs (Module ℂ S)

def tsubVal (S : Submodule ℂ (TensorProduct ℂ M (Fock n))) : TSub S →ₗ[ℂ] TensorProduct ℂ M (Fock n) :=
  S.subtype

theorem tsubVal_injective : Function.Injective (tsubVal S) := Subtype.val_injective

theorem tsubVal_mem (x : TSub S) : tsubVal S x ∈ S := (x : S).2

instance tsubCore : InnerProductSpace.Core ℂ (TSub S) where
  inner x y := tform (tsubVal S x) (tsubVal S y)
  conj_inner_symm x y := tform_conj _ _
  re_inner_nonneg x := by
    by_cases h : tsubVal S x = 0
    · rw [h]
      simp [tform]
    · exact (tform_self_re_pos h).le
  add_left x y z := by
    simp only [map_add]
    exact tform_add_left _ _ _
  smul_left x y r := by
    simp only [map_smul]
    exact tensorForm_smul_left r _ _
  definite x h := by
    by_contra hx
    have hx' : tsubVal S x ≠ 0 := fun h0 => hx (tsubVal_injective (h0.trans (map_zero _).symm))
    have h' : tform (tsubVal S x) (tsubVal S x) = 0 := h
    have := tform_self_re_pos hx'
    rw [h'] at this
    simp at this

instance : NormedAddCommGroup (TSub S) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (TSub S) := InnerProductSpace.ofCore _

theorem tsub_inner (x y : TSub S) : inner ℂ x y = tform (tsubVal S x) (tsubVal S y) := rfl

instance [h : FiniteDimensional ℂ S] : FiniteDimensional ℂ (TSub S) := h

end TSubSec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def tOp (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
    (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)
    (k : Matrix (Fin n) (Fin n) ℂ) : TSub S →L[ℂ] TSub S :=
  @dite _ (k ∈ Kset ε) (Classical.propDecidable _)
    (fun hk => LinearMap.toContinuousLinearMap
      (((wK hD hk).restrict (hSK k hk) : S →ₗ[ℂ] S) : TSub S →ₗ[ℂ] TSub S)) (fun _ => 0)

section Op

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_apply {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : TSub S) :
    tsubVal S (tOp hD hSK k x) = wK hD hk (tsubVal S x) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isURepOn (hσ : IsURepOn (UJset ε) σ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (tOp hD hSK) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK one_mem_Kset', wK_one hσ hD]
    rfl
  · intro a ha b hb
    ext x
    apply tsubVal_injective
    rw [tOp_apply hD hSK (mul_mem_Kset' ha hb), ContinuousLinearMap.comp_apply, tOp_apply hD hSK ha,
      tOp_apply hD hSK hb, wK_mul hσ hD ha hb]
    rfl
  · intro g hg v
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), tsub_inner, tsub_inner,
      tOp_apply hD hSK hg, tform_wK hσ hD hg]
  · intro v
    have hΨ : Set.EqOn (fun g => coordH (tsubVal S (tOp hD hSK g v)))
        (fun g => fun s => ∑ s', ffMat ε g s s' • σ g ((tcoef ((fockBasis n).coord s') (tsubVal S v) : D) : H))
        (Formalism.REAL.Kset ε) := by
      intro g hg
      have hg' : g ∈ Kset ε := hg
      funext s
      simp only
      rw [tOp_apply hD hSK hg', coordH_apply, tco_wK, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [coord_ff_basis]
      rfl
    have hc : ContinuousOn (fun g => coordH (tsubVal S (tOp hD hSK g v))) (Formalism.REAL.Kset ε) := by
      refine ContinuousOn.congr ?_ hΨ
      refine continuousOn_pi.2 fun s => continuousOn_finsetSum _ fun s' _ => ?_
      exact (ffMat_continuous s s').continuousOn.smul
        ((hσ.2.2 _).mono fun g hg => kset_mem_UJset hg)
    have hinj : Function.Injective (coordH ∘ₗ tsubVal S) := coordH_injective.comp tsubVal_injective
    let e := LinearEquiv.ofInjective _ hinj
    have hcont : Continuous e.symm := LinearMap.continuous_of_finiteDimensional e.symm.toLinearMap
    have hfe : (fun g => tOp hD hSK g v) =
        fun g => e.symm ⟨(coordH ∘ₗ tsubVal S) (tOp hD hSK g v), LinearMap.mem_range_self _ _⟩ := by
      funext g
      refine (e.symm_apply_apply (tOp hD hSK g v)).symm.trans ?_
      congr 1
    rw [hfe, continuousOn_iff_continuous_restrict]
    exact hcont.comp ((continuousOn_iff_continuous_restrict.1 hc).subtype_mk _)

end Op

section KType

variable (hD : IsDerivedOn ε σ D E) {S : Submodule ℂ (TensorProduct ℂ D (Fock n))} [FiniteDimensional ℂ S]
  (hSK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ S, wK hD hk y ∈ S)

theorem tOp_trace {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    LinearMap.trace ℂ (TSub S) (tOp hD hSK k : TSub S →ₗ[ℂ] TSub S) =
      LinearMap.trace ℂ S ((wK hD hk).restrict (hSK k hk)) := by
  simp only [tOp, dif_pos hk]
  rfl

theorem tOp_isKTypeOf (hσ : IsURepOn (UJset ε) σ) {γ : Fin n → ℝ}
    (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) :
    Formalism.MainNotions.S.IsKTypeOf ε (tOp hD hSK) γ ⊤ := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hKA : Formalism.REAL.KRel ε (diagE ε (eT E) cpT cmT) :=
    fun a b c d hab hcd => diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd
  obtain ⟨_, hSs, hirr, w, hwS, hw0, hwK⟩ := hS
  have hSeq : kLowSpan ε (diagE ε (eT E) cpT cmT) w = S := by
    have hle := kLowSpan_le hSs hwS
    rcases hirr _ hle (compactLoweringSpan_kStable hKA hwK) with h | h
    · exfalso
      apply hw0
      have := self_mem_kLowSpan (ε := ε) (E := diagE ε (eT E) cpT cmT) w
      rw [h, Submodule.mem_bot] at this
      exact this
    · exact h
  refine ⟨inferInstance, fun g _ v _ => Submodule.mem_top, ?_, ?_, ?_⟩
  · intro S'' _ hK''
    let P : Submodule ℂ (TensorProduct ℂ D (Fock n)) := S''.map (tsubVal S)
    have hPS : P ≤ S := by
      rintro _ ⟨x, _, rfl⟩
      exact tsubVal_mem x
    have hPfd : FiniteDimensional ℂ P := Module.Finite.map S'' (tsubVal S)
    have hPK : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ P, wK hD hk y ∈ P := by
      rintro k hk _ ⟨x, hx, rfl⟩
      exact ⟨tOp hD hSK k x, hK'' k hk x hx, tOp_apply hD hSK hk x⟩
    have hPs : IsKStableSub ε (diagE ε (eT E) cpT cmT) P := fun a b hab y hy =>
      diagE_mem_of_wK hσ hD P hPfd hPK hab hy
    rcases hirr P hPS hPs with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : tsubVal S x ∈ P := ⟨x, hx, rfl⟩
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot]
      exact tsubVal_injective (this.trans (map_zero _).symm)
    · right
      rw [eq_top_iff]
      intro x _
      have hxP : tsubVal S x ∈ P := by
        rw [h]
        exact tsubVal_mem x
      obtain ⟨x', hx', hxx⟩ := hxP
      exact (tsubVal_injective hxx) ▸ hx'
  · refine ⟨(show TSub S from ⟨w, hwS⟩), Submodule.mem_top, ?_, ?_⟩
    · intro h
      apply hw0
      have := congrArg (tsubVal S) h
      rwa [map_zero] at this
    · intro θ _
      apply tsubVal_injective
      rw [tOp_apply hD hSK (diag_mem_Kset' ε θ), map_smul]
      exact wK_diag_wt hσ hD hwK.1 θ
  · intro μ v _ hv0 hwt
    have hy : ∀ θ : Fin n → ℝ, wK hD (diag_mem_Kset' ε θ) (tsubVal S v) =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • tsubVal S v := by
      intro θ
      rw [← tOp_apply hD hSK (diag_mem_Kset' ε θ), hwt θ (bwt_diag_mem_Kset ε θ), map_smul]
    have hμ := diagE_wt_of_wK hσ hD hy
    have hvS : tsubVal S v ∈ kLowSpan ε (diagE ε (eT E) cpT cmT) w := hSeq ▸ tsubVal_mem v
    have hv0' : tsubVal S v ≠ 0 := fun h => hv0 (tsubVal_injective (h.trans (map_zero _).symm))
    obtain ⟨l, hl, rfl⟩ := kLow_wt_eq_lowWt hKA (fun a y y' => tensorForm_diagAction_adjoint hU rfl y y') hwK hvS hv0' hμ
    exact cdom_lowWt γ l hl

theorem tSub_nontrivial {γ : Fin n → ℝ} (hS : IsKIrrHW ε (diagE ε (eT E) cpT cmT) γ S) : Nontrivial (TSub S) := by
  obtain ⟨_, _, _, w, hwS, hw0, _⟩ := hS
  refine ⟨⟨(show TSub S from ⟨w, hwS⟩), 0, fun h => hw0 ?_⟩⟩
  have := congrArg (tsubVal S) h
  rwa [map_zero] at this

end KType

end ReciprocityTheory.ChartRestriction.DS.TRGap
