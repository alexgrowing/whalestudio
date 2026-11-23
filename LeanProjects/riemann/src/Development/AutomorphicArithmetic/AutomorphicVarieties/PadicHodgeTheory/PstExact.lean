import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepInducedMatches
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap GlobalTheory.Pst.DmapNonzero

namespace UpperTheory.V.Loc.PstExact

theorem charpoly_exact {K M₀ M₁ M₂ : Type} [Field K] [AddCommGroup M₀] [Module K M₀] [FiniteDimensional K M₀]
    [AddCommGroup M₁] [Module K M₁] [FiniteDimensional K M₁] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (i : M₀ →ₗ[K] M₁) (p : M₁ →ₗ[K] M₂) (hk : LinearMap.ker p ≤ LinearMap.range i) (hp : Function.Surjective p)
    (hd : finrank K M₁ = finrank K M₀ + finrank K M₂) (hpi : ∀ x, p (i x) = 0)
    (T₀ : End K M₀) (T₁ : End K M₁) (T₂ : End K M₂) (h₀ : ∀ x, i (T₀ x) = T₁ (i x)) (h₂ : ∀ x, p (T₁ x) = T₂ (p x)) :
    T₁.charpoly = T₀.charpoly * T₂.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker p, T₁ x ∈ LinearMap.ker p := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h₂, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker p) T₁ hA]
  have h5 := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hp, finrank_top] at h5
  congr 1
  · symm
    refine eq_of_monic_of_dvd_of_natDegree_le (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) ?_ ?_
    · refine charpoly_dvd_of_surjective (i.codRestrict (LinearMap.ker p) hpi) (fun y => ?_) _ _
        fun x => Subtype.ext (h₀ x)
      obtain ⟨x, hx⟩ := hk y.2
      exact ⟨x, Subtype.ext hx⟩
    · rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree]; omega
  · symm
    refine eq_of_monic_of_dvd_of_natDegree_le (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _) ?_ ?_ |>.symm
    · refine charpoly_dvd_of_surjective (p.quotKerEquivOfSurjective hp).toLinearMap
        (p.quotKerEquivOfSurjective hp).surjective _ _ fun x => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      exact h₂ x
    · rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree, (p.quotKerEquivOfSurjective hp).finrank_eq]

theorem letter_exact {LL U D₀ D₁ D₂ : Type} [Field LL] [Field U] [AddCommGroup D₀] [Module LL D₀] [AddCommGroup D₁]
    [Module LL D₁] [AddCommGroup D₂] [Module LL D₂] (m₀ : U →+* End LL D₀) (m₁ : U →+* End LL D₁)
    (m₂ : U →+* End LL D₂) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (S : D₀ →ₗ[LL] D₁) (T : D₁ →ₗ[LL] D₂)
    (hS : ∀ c, S ∘ₗ m₀ c = m₁ c ∘ₗ S) (hT : ∀ c, T ∘ₗ m₁ c = m₂ c ∘ₗ T) (he : Function.Exact S T)
    (hs : Function.Surjective T) :
    LinearMap.ker (letterLin m₁ m₂ F τ T hT) ≤ LinearMap.range (letterLin m₀ m₁ F τ S hS) := by
  have hs' : Function.Surjective (T.baseChange F) := LinearMap.lTensor_surjective F hs
  have he' : Function.Exact (S.baseChange F) (T.baseChange F) := lTensor_exact F he hs
  have hle : letterKer m₂ F τ ≤ (letterKer m₁ F τ).map (T.baseChange F) := iSup_le fun c => by
    rintro _ ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := hs' y
    refine ⟨_, Submodule.mem_iSup_of_mem c ⟨y, rfl⟩, ?_⟩
    have := LinearMap.congr_fun (congrArg (LinearMap.baseChange F) (hT c)) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at this
    simp [this]
  intro y hy
  obtain ⟨z, rfl⟩ := letterQ_surjective m₁ F τ y
  have h1 : T.baseChange F z ∈ letterKer m₂ F τ := by
    rw [← ker_letterQ]; exact hy
  obtain ⟨z', hz', e⟩ := hle h1
  obtain ⟨u, hu⟩ := (he' (z - z')).1 (by rw [map_sub, e, sub_self])
  refine ⟨letterQ m₀ F τ u, ?_⟩
  change letterQ m₁ F τ (S.baseChange F u) = _
  rw [← ker_letterQ] at hz'
  rw [hu, map_sub, LinearMap.mem_ker.1 hz', sub_zero]

section Pst

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}

def dUr {f : V₀ →ₗ[↥LL.1] V₁} (hf : ∀ g v, f (ρ₀ g v) = ρ₁ g (f v)) : DpstUr P ρ₀ →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ₁ where
  toFun x := toUr P ρ₁ (dmap P hf ((toUr P ρ₀).symm x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := dmap_mulD P hf c ((toUr P ρ₀).symm x)

variable {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v))
  (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v))

theorem dmap_exact (h1 : Function.Injective i) (h2 : Function.Exact i p) :
    Function.Injective (dmap P hi) ∧ Function.Exact (dmap P hi) (dmap P hp) := by
  have hex : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  have hexT := Module.Flat.rTensor_exact (Bst P) hex
  have hinj : Function.Injective ((i.restrictScalars ℚ_[l]).rTensor (Bst P)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ h1
  refine ⟨fun x y h => Subtype.ext (hinj ?_), fun y => ⟨fun h => ?_, ?_⟩⟩
  · rw [← tensV_eq_rTensor, ← tensV_eq_rTensor]; exact congrArg Subtype.val h
  · have h0 : tensV P p (y : V₁ ⊗[ℚ_[l]] Bst P) = 0 := congrArg Subtype.val h
    rw [tensV_eq_rTensor] at h0
    obtain ⟨z, hz⟩ := (hexT _).mp h0
    have hz' : tensV P i z = y := by rw [tensV_eq_rTensor]; exact hz
    obtain ⟨K', hK'⟩ := (mem_Dpst P ρ₁).mp y.2
    have hzD : z ∈ Dpst P ρ₀ := by
      refine (mem_Dpst P ρ₀).mpr ⟨K', fun g hg => hinj ?_⟩
      rw [← tensV_eq_rTensor, ← tensV_eq_rTensor, tensV_stRep P ρ₀ ρ₁ i hi, hz', hK' g hg]
    exact ⟨⟨z, hzD⟩, Subtype.ext hz'⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    change tensV P p (tensV P i x) = 0
    rw [tensV_eq_rTensor, tensV_eq_rTensor]
    exact (hexT _).2 ⟨_, rfl⟩

variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]

include hi in

theorem isPst_exact {AI : LocAinf l P} (T : LocTied l P AI) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (h3 : Function.Surjective p) (hV : IsPst P ρ₁) :
    IsPst P ρ₀ ∧ IsPst P ρ₂ ∧ Function.Surjective (dmap P hp) := by
  obtain ⟨hdom, hfrac, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] V₀ := Module.Finite.trans ↥LL.1 V₀
  haveI : FiniteDimensional ℚ_[l] V₁ := Module.Finite.trans ↥LL.1 V₁
  haveI : FiniteDimensional ℚ_[l] V₂ := Module.Finite.trans ↥LL.1 V₂
  have b₀ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₀
  have b₂ := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation P hdom hfrac ρ₂
  haveI f₀ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₀) :=
    Module.rank_lt_aleph0_iff.mp (b₀.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI f₂ : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ₂) :=
    Module.rank_lt_aleph0_iff.mp (b₂.trans_lt (Cardinal.natCast_lt_aleph0))
  haveI := hV.finite
  rw [← finrank_eq_rank, Nat.cast_le] at b₀ b₂
  have b₁ := ((isPst_iff P ρ₁).1 hV).2
  obtain ⟨e1, e2⟩ := dmap_exact P hi hp h1 h2
  have e1' : Function.Injective (dUr P hi) := e1
  have e2' : Function.Exact (dUr P hi) (dUr P hp) := e2
  have h4 := (dUr P hp).finrank_range_add_finrank_ker
  rw [e2'.linearMap_ker_eq, LinearMap.finrank_range_of_inj e1'] at h4
  have hex : Function.Exact (i.restrictScalars ℚ_[l]) (p.restrictScalars ℚ_[l]) := h2
  have h5 := (p.restrictScalars ℚ_[l]).finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj (f := i.restrictScalars ℚ_[l]) h1,
    (LinearMap.range_eq_top (f := p.restrictScalars ℚ_[l])).2 h3, finrank_top] at h5
  have h6 := (LinearMap.range (dUr P hp)).finrank_le
  refine ⟨(isPst_iff P ρ₀).2 ⟨f₀, by omega⟩, (isPst_iff P ρ₂).2 ⟨f₂, by omega⟩, ?_⟩
  exact (LinearMap.range_eq_top (f := dUr P hp)).1 (Submodule.eq_top_of_finrank_eq (by omega))

end Pst

section Weil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l}

include T in

theorem charPol_exact
    {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
    [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
    [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
    [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]
    {ρ₀ : Representation ↥LL.1 ↥(GK Bw.Kw) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK Bw.Kw) V₁}
    {ρ₂ : Representation ↥LL.1 ↥(GK Bw.Kw) V₂}
    {i : V₀ →ₗ[↥LL.1] V₁} {p : V₁ →ₗ[↥LL.1] V₂} (hi : ∀ g v, i (ρ₀ g v) = ρ₁ g (i v))
    (hp : ∀ g v, p (ρ₁ g v) = ρ₂ g (p v)) (h1 : Function.Injective i) (h2 : Function.Exact i p)
    (h3 : Function.Surjective p) (hV : IsPst P ρ₁) :
    IsPst P ρ₀ ∧ IsPst P ρ₂ ∧ ∀ σ, (wdPst P ι Bw h hj ρ₁).charPol σ =
      (wdPst P ι Bw h hj ρ₀).charPol σ * (wdPst P ι Bw h hj ρ₂).charPol σ := by
  obtain ⟨p₀, p₂, hs⟩ := isPst_exact P hi hp T h1 h2 h3 hV
  obtain ⟨-, e2⟩ := dmap_exact P hi hp h1 h2
  refine ⟨p₀, p₂, fun σ => ?_⟩
  haveI := p₀.finite
  haveI := hV.finite
  haveI := p₂.finite
  rw [charPol_wdPst P ι Bw h hj ρ₀ p₀, charPol_wdPst P ι Bw h hj ρ₁ hV, charPol_wdPst P ι Bw h hj ρ₂ p₂]
  refine charpoly_exact (wdLin P ι hi) (wdLin P ι hp) ?_ ?_ ?_ (fun x => ?_) _ _ _
    (wdLin_wdRho P ι Bw h hj hi σ) (wdLin_wdRho P ι Bw h hj hp σ)
  · letI := algC ι LL
    exact letter_exact _ _ _ ℂ (urC ι) _ _ _ _ e2 hs
  · rw [← LinearMap.range_eq_top, eq_top_iff, ← span_wdMk P ι ρ₂, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := hs x
    exact ⟨wdMk P ι ρ₁ x, rfl⟩
  · rw [LetterDim.finrank_wdSpace l P ι _ _ _ ρ₀ p₀, LetterDim.finrank_wdSpace l P ι _ _ _ ρ₁ hV,
      LetterDim.finrank_wdSpace l P ι _ _ _ ρ₂ p₂]
    have h5 := p.finrank_range_add_finrank_ker
    rw [h2.linearMap_ker_eq, LinearMap.finrank_range_of_inj h1, LinearMap.range_eq_top.2 h3, finrank_top] at h5
    omega
  · have : (wdLin P ι hp).comp (wdLin P ι hi) = 0 := LinearMap.ext_on_range (span_wdMk P ι ρ₀) fun x => by
      rw [LinearMap.comp_apply, wdLin_mk, wdLin_mk, e2.apply_apply_eq_zero, wdMk_zero, LinearMap.zero_apply]
    exact LinearMap.congr_fun this x

end Weil

section Tri

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem exists_tail (r : Γ →* GL (Fin (n + 1)) k) (hr : ∀ g i j, j < i → (r g).val i j = 0) :
    ∃ r' : Γ →* GL (Fin n) k, ∀ g (i j : Fin n), (r' g).val i j = (r g).val i.succ j.succ := by
  let f : Γ →* Matrix (Fin n) (Fin n) k :=
    { toFun := fun g => (r g).val.submatrix Fin.succ Fin.succ
      map_one' := by
        rw [map_one, Units.val_one, Matrix.submatrix_one _ (Fin.succ_injective n)]
      map_mul' := fun g g' => by
        ext i j
        rw [map_mul, Units.val_mul, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ,
          hr g i.succ 0 (Fin.succ_pos i), zero_mul, zero_add]
        rfl }
  exact ⟨f.toHomUnits, fun _ _ _ => rfl⟩

theorem exact_line : Function.Injective ((LinearMap.single k (fun _ : Fin (n + 1) => k) 0).comp
      (LinearMap.proj (0 : Fin 1) : (Fin 1 → k) →ₗ[k] k)) ∧
    Function.Exact ((LinearMap.single k (fun _ : Fin (n + 1) => k) 0).comp
      (LinearMap.proj (0 : Fin 1) : (Fin 1 → k) →ₗ[k] k)) (LinearMap.funLeft k k (Fin.succ : Fin n → Fin (n + 1))) := by
  refine ⟨fun x y e => ?_, fun y => ⟨fun e => ⟨fun _ => y 0, ?_⟩, ?_⟩⟩
  · funext i
    rw [Subsingleton.elim i 0]
    simpa using congrFun e 0
  · funext i
    refine Fin.cases (by simp) (fun j => ?_) i
    simpa using (congrFun e j).symm
  · rintro ⟨x, rfl⟩
    funext j
    simp [LinearMap.funLeft_apply]

end Tri

section Flag

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l}

theorem charPol_zero {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin 0 → ↥LL.1)} (hV : IsPst P ρ) (σ : ↥(Weil h)) :
    (wdPst P ι Bw h hj ρ).charPol σ = 1 := by
  rw [← (WD.charPol_monic _ σ).natDegree_eq_zero, WD.charPol_natDegree, lpDim_wdPst ι Bw h hj hV,
    LetterDim.finrank_wdSpace l P ι _ _ _ ρ hV, finrank_fin_fun]

include T in

theorem charPol_equiv {n : ℕ} {ρ₁ ρ₂ : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin n → ↥LL.1)}
    (e : (Fin n → ↥LL.1) ≃ₗ[↥LL.1] (Fin n → ↥LL.1)) (he : ∀ g x, e (ρ₁ g x) = ρ₂ g (e x)) (hV : IsPst P ρ₁) :
    IsPst P ρ₂ ∧ ∀ σ, (wdPst P ι Bw h hj ρ₁).charPol σ = (wdPst P ι Bw h hj ρ₂).charPol σ := by
  obtain ⟨p₀, p₂, H⟩ := charPol_exact T ι Bw h hj (ρ₀ := (1 : Representation ↥LL.1 ↥(GK Bw.Kw) (Fin 0 → ↥LL.1)))
    (i := 0) (p := e.toLinearMap) (fun g v => by simp) he (Function.injective_of_subsingleton _)
    (fun y => by simp [@eq_comm _ 0 y]) e.surjective hV
  exact ⟨p₂, fun σ => by rw [H, charPol_zero ι Bw h hj p₀, one_mul]⟩

include T in

theorem tri (n : ℕ) : ∀ (r : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g i j, j < i → (r g).val i j = 0) →
    (∀ g i, (r g).val i i = (c i g).val 0 0) →
    (Bw.IsdRE P LL r → ∀ τ a, Bw.multE P LL r τ a = ∑ i, Bw.multE P LL (c i) τ a) ∧
    (IsPst P (Bw.repE LL r) → (∀ i, IsPst P (Bw.repE LL (c i))) ∧
      ∀ σ, (wdPst P ι Bw h hj (Bw.repE LL r)).charPol σ = ∏ i, (wdPst P ι Bw h hj (Bw.repE LL (c i))).charPol σ) := by
  induction n with
  | zero =>
    intro r c _ _
    refine ⟨fun _ τ a => ?_, fun hV => ⟨fun i => i.elim0, fun σ => ?_⟩⟩
    · simp only [LocBridge.multE, Formalism.WeaklyAdmissibleFiltrations.multV, finrank_zero_of_subsingleton, Finset.univ_eq_empty, Finset.sum_empty,
        sub_self]
    · rw [charPol_zero ι Bw h hj hV, Finset.univ_eq_empty, Finset.prod_empty]
  | succ n ih =>
    intro r c hr hc
    obtain ⟨r', hr'⟩ := exists_tail r hr
    obtain ⟨ih₁, ih₂⟩ := ih r' (fun i => c i.succ)
      (fun g i j hij => by rw [hr', hr g _ _ (Fin.succ_lt_succ_iff.2 hij)]) (fun g i => by rw [hr', hc])
    obtain ⟨h1, h2⟩ := exact_line (k := ↥LL.1) (n := n)
    have h3 := LinearMap.funLeft_surjective_of_injective ↥LL.1 ↥LL.1 _ (Fin.succ_injective n)
    have hi : ∀ g v, ((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) (Bw.repE LL (c 0) g v) =
        Bw.repE LL r g (((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, hc, Fin.sum_univ_succ]
      · simp [Matrix.mulVec, dotProduct, hr _ j.succ 0 (Fin.succ_pos j), Fin.sum_univ_succ]
    have hp : ∀ g v, LinearMap.funLeft ↥LL.1 ↥LL.1 (Fin.succ : Fin n → Fin (n + 1)) (Bw.repE LL r g v) =
        Bw.repE LL r' g (LinearMap.funLeft ↥LL.1 ↥LL.1 Fin.succ v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, hr _ i.succ 0 (Fin.succ_pos i), Fin.sum_univ_succ, hr']
    refine ⟨fun hd τ a => ?_, fun hV => ?_⟩
    · obtain ⟨-, d₂, H⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T Bw.Kw LL _ _ _ _ _ _ _ _ hi hp h1 h3
        h2.linearMap_ker_eq.symm (by rw [IsDR, finrank_fin_fun]; exact hd)
      rw [IsDR, finrank_fin_fun] at d₂
      rw [Fin.sum_univ_succ, ← ih₁ d₂ τ a]
      exact (H τ a).2.1
    · obtain ⟨p₀, p₂, H⟩ := charPol_exact T ι Bw h hj hi hp h1 h2 h3 hV
      obtain ⟨q, H'⟩ := ih₂ p₂
      exact ⟨fun i => Fin.cases p₀ q i, fun σ => by rw [Fin.prod_univ_succ, H, H']⟩

theorem charPol_model {n : ℕ} {r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l)} {r₂ : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1}
    (hm₂ : IsModel Bw r LL r₂) (hV₂ : IsPst P (Bw.repE LL r₂)) (σ : ↥(Weil h)) :
    (wdAt P ι Bw h hj r).charPol σ = (wdPst P ι Bw h hj (Bw.repE LL r₂)).charPol σ := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj (r := r) ⟨LL, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ LL).1 := le_sup_left
  have h₂ : LL.1 ≤ (supExt L₁ LL).1 := le_sup_right
  have e := IsModel.unique Bw r (hm₁.enlarge h₁) (hm₂.enlarge h₂)
  rw [e₁, ← GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients P ι Bw h hj h₁ r₁ hV₁ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw h₁ r₁ hV₁),
    ← GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients P ι Bw h hj h₂ r₂ hV₂ (GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw h₂ r₂ hV₂), e]

theorem exists_diag {n : ℕ} {r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l)}
    {c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)} (hc : ∀ g i, (r g).val i i = (c i g).val 0 0)
    {r₂ : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1} (hm : IsModel Bw r LL r₂) :
    ∃ c₂ : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1, (∀ i, IsModel Bw (c i) LL (c₂ i)) ∧
      ∀ g i, (r₂ g).val i i = (c₂ i g).val 0 0 := by
  have er : ∀ g i, (((r₂ g).val i i : ↥LL.1) : Om l) = (c i g).val 0 0 := fun g i => by
    rw [← hc, ← hm.2]; rfl
  let f : Fin n → ↥(Dec (F := E) A) →* Matrix (Fin 1) (Fin 1) ↥LL.1 := fun i =>
    { toFun := fun g => Matrix.of fun _ _ => (r₂ g).val i i
      map_one' := by
        ext a b
        rw [Subsingleton.elim a b]
        simp
      map_mul' := fun g g' => by
        ext a b
        rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply,
          MulMemClass.coe_mul, er, er, er, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one] }
  refine ⟨fun i => (f i).toHomUnits, fun i => ⟨hm.1, ?_⟩, fun _ _ => rfl⟩
  ext g a b
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
  exact er g i

include T in

theorem flag {n : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l))
    (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)) (M : GL (Fin n) (Om l))
    (hr : ∀ g i j, j < i → (M * r g * M⁻¹).val i j = 0) (hc : ∀ g i, (M * r g * M⁻¹).val i i = (c i g).val 0 0) :
    (∀ τ J (J' : Fin n → Multiset ℤ), IsJumpsAt P Bw r τ J → (∀ i, IsJumpsAt P Bw (c i) τ (J' i)) → J = ∑ i, J' i) ∧
    (IsPstAt P Bw r → (∀ i, IsPstAt P Bw (c i)) ∧
      ∀ σ, (wdAt P ι Bw h hj r).charPol σ = ∏ i, (wdAt P ι Bw h hj (c i)).charPol σ) := by
  let r' : ↥(Dec (F := E) A) →* GL (Fin n) (Om l) := (MulAut.conj M).toMonoidHom.comp r
  have hr' : ∀ g, r' g = M * r g * M⁻¹ := fun _ => rfl
  have htri : ∀ {L : FinExt l} {r₂ : ↥(Dec (F := E) A) →* GL (Fin n) ↥L.1}, IsModel Bw r' L r₂ →
      ∀ g i j, j < i → (r₂ g).val i j = 0 := fun {L r₂} hm g i j hij => Subtype.ext (by
    have := hr g i j hij
    rw [← hr', ← hm.2] at this
    exact this)
  refine ⟨fun τ J J' hJ hJ' => ?_, fun ⟨L₁, r₁, hm₁, hV₁⟩ => ?_⟩
  · obtain ⟨L, r₂, hm, hd, τ₂, hτ, H⟩ :=
      (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw n r r' M hr').2.2.2 τ J hJ
    obtain ⟨c₂, hm', hc₂⟩ := exists_diag Bw (r := r') hc hm
    ext a
    have := (tri T ι Bw h hj n r₂ c₂ (htri hm) hc₂).1 hd τ₂ a
    rw [← H, Finset.sum_congr rfl fun i _ => ((hJ' i).count_eq P (hm' i) hτ a).symm] at this
    rw [Multiset.count_sum']
    exact_mod_cast this
  · obtain ⟨L, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model M hr' hm₁
    obtain ⟨c₂, hm', hc₂⟩ := exists_diag Bw (r := r') hc hm
    have q₁ := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge P Bw hL r₁ hV₁
    obtain ⟨q₂, H⟩ := charPol_equiv T ι Bw h hj e he q₁
    obtain ⟨q₃, H'⟩ := (tri T ι Bw h hj n r₂ c₂ (htri hm) hc₂).2 q₂
    refine ⟨fun i => ⟨L, c₂ i, hm' i, q₃ i⟩, fun σ => ?_⟩
    rw [charPol_model ι Bw h hj (hm₁.enlarge hL) q₁, H, H']
    exact Finset.prod_congr rfl fun i _ => (charPol_model ι Bw h hj (hm' i) (q₃ i) σ).symm

end Flag

end UpperTheory.V.Loc.PstExact
