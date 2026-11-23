import Development.AutomorphicSpectrum.Proofs.MetricProofs.AbelianPartHeightLinear

noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights TensorProduct

theorem abel_abstract :
    ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (L Ψ : Type) [Field L] [NumberField L] [Fintype Ψ] (B : HermitianBundle.{0} L)
      (F F' : Ψ → Submodule (𝓞 L) B.carrier) (m N : ℕ) (La : ℝ), 1 ≤ Fintype.card Ψ * m → 1 ≤ La →
      ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ Real.exp La → Module.finrank (𝓞 L) B.carrier ≤ Fintype.card Ψ * N →
      (∀ τ, B.rank (F τ) ≤ m) →
      B.slopeMax ≤ ((C₀ * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal) →
      ∑ τ, B.normDegree (F τ) + ∑ τ, B.normDegree (F' τ) ≤ B.normDegree ⊤ →
      (∀ τ, |B.normDegree (F τ) - B.normDegree (F' τ)| ≤ C₀ * N * La) →
      ∑ τ, B.normDegree (F τ) ≤ C * (Fintype.card Ψ * m) * La := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := LowerBound.InteriorDichotomy.proof C₀ 0 C₀ hC₀ le_rfl hC₀
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro L Ψ _ _ _ B F F' m N La hfm hLa hexp hrank hm hslope hsum0 hdd
  set f : ℝ := (Fintype.card Ψ : ℝ) with hf
  set h : ℝ := -B.normDegree ⊤ with hh
  set n : ℝ := (Module.finrank (𝓞 L) B.carrier : ℝ) with hn
  set g : ℝ := max ((Fintype.card Ψ * N : ℕ) : ℝ) 1 with hg
  set x : ℝ := ∑ τ, B.normDegree (F τ) with hx
  set y : ℝ := ∑ τ, B.normDegree (F' τ) with hy
  have hLa0 : 0 < La := by linarith
  have hf0 : 0 ≤ f := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hg1 : 1 ≤ g := le_max_right _ _
  have hfN : f * N ≤ g := by
    have : ((Fintype.card Ψ * N : ℕ) : ℝ) ≤ g := le_max_left _ _
    simpa [hf] using this
  have hng : n ≤ g := by
    have h1 : n ≤ ((Fintype.card Ψ * N : ℕ) : ℝ) := Nat.cast_le.2 hrank
    exact h1.trans (le_max_left _ _)
  have hfj : (1 : ℝ) ≤ f * m := by
    have : ((1 : ℕ) : ℝ) ≤ ((Fintype.card Ψ * m : ℕ) : ℝ) := by exact_mod_cast hfm
    simpa [hf] using this
  have hgexp : g ≤ Real.exp La := max_le hexp (Real.one_le_exp hLa0.le)

  set μ : ℝ := C₀ * Real.log (2 + n + max h 0) with hμ
  have harg : 1 ≤ 2 + n + max h 0 := by
    have h1 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have h2 := le_max_right h 0
    linarith
  have hμ0 : 0 ≤ μ := mul_nonneg hC₀ (Real.log_nonneg harg)
  have hμg : μ ≤ C₀ * Real.log (2 + g + max h 0) :=
    mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) (by linarith)) hC₀
  have hxle : x ≤ f * m * μ := by
    have h1 : ∀ τ, B.normDegree (F τ) ≤ m * μ := fun τ =>
      (HermitianBundle.normDegree_le_rank_mul B _ μ hslope).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hm τ) hμ0)
    calc x ≤ ∑ _τ : Ψ, (m : ℝ) * μ := Finset.sum_le_sum fun τ _ => h1 τ
      _ = f * m * μ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hf]; ring

  have hsum : x + y ≤ -h := by
    rw [hh, neg_neg]
    exact hsum0
  have hxy : x - y ≤ f * (C₀ * N * La) := by
    have h1 : x - y ≤ ∑ _τ : Ψ, C₀ * N * La := by
      rw [hx, hy, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun τ _ => (le_abs_self _).trans (hdd τ)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    exact h1
  have hfC : f * (C₀ * N * La) ≤ C₀ * g * La := by
    have : C₀ * (f * N) * La ≤ C₀ * g * La :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfN hC₀) hLa0.le
    calc f * (C₀ * N * La) = C₀ * (f * N) * La := by ring
      _ ≤ _ := this
  have hyp : LowerBound.InteriorDichotomy.Hyp C₀ 0 C₀ h (-x) g (f * m) La :=
    { one_le_g := hg1
      one_le_fj := hfj
      g_le_exp := hgexp
      one_le_La := hLa
      lower := by
        have h1 : f * m * μ ≤ f * m * (C₀ * Real.log (2 + g + max h 0)) :=
          mul_le_mul_of_nonneg_left hμg (by linarith)
        have h2 : f * m * (C₀ * Real.log (2 + g + max h 0) + 0 * La) =
            f * m * (C₀ * Real.log (2 + g + max h 0)) := by ring
        rw [h2]
        linarith
      upper := by linarith }
  have hfin := hC h (-x) g (f * m) La hyp
  have h1 : C * (f * m) * La ≤ max C 0 * (f * m) * La :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hLa0.le
  have h2 : x ≤ C * (f * m) * La := by linarith
  exact h2.trans h1

theorem mem_eigSp_iff {R M O : Type} [CommRing R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : O →+* R) (x : M) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

def intLift {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) : 𝓞 E →+* 𝓞 L where
  toFun a := ⟨σ a, map_isIntegral_int σ (RingOfIntegers.isIntegral a)⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ a b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ a b)

theorem intLift_apply {E L : Type} [Field E] [Field L] (σ : 𝓞 E →+* L) (a : 𝓞 E) :
    algebraMap (𝓞 L) L (intLift σ a) = σ a := rfl

theorem exists_smul_mem_of_eig {R M O ι : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [CommRing O]
    (ρ : O →+* Module.End R M) (σ : ι → (O →+* R)) (s : ι) (N : Submodule R M) (hN : N ≤ eigSp ρ (σ s))
    (T : Finset ι) (hT : ∀ t ∈ T, σ t ≠ σ s) :
    ∀ y ∈ eigSp ρ (σ s), y ∈ N ⊔ ⨆ t ∈ T, eigSp ρ (σ t) → ∃ d : R, d ≠ 0 ∧ d • y ∈ N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro y _ hy
    refine ⟨1, one_ne_zero, ?_⟩
    simpa using hy
  | insert t T ht ih =>
    intro y hy hy'
    obtain ⟨a, ha⟩ := DFunLike.ne_iff.1 (hT t (Finset.mem_insert_self _ _))
    let φ : M →ₗ[R] M := ρ a - σ t a • LinearMap.id
    have hφ : ∀ u, ∀ z ∈ eigSp ρ (σ u), φ z = (σ u a - σ t a) • z := fun u z hz => by
      change ρ a z - σ t a • z = _
      rw [(mem_eigSp_iff _ _ _).1 hz a, sub_smul]
    have hle : N ⊔ ⨆ u ∈ insert t T, eigSp ρ (σ u) ≤ (N ⊔ ⨆ u ∈ T, eigSp ρ (σ u)).comap φ := by
      refine sup_le (fun z hz => ?_) (iSup₂_le fun u hu z hz => ?_)
      · rw [Submodule.mem_comap, hφ s z (hN hz)]
        exact Submodule.mem_sup_left (N.smul_mem _ hz)
      · rw [Submodule.mem_comap, hφ u z hz]
        rcases Finset.mem_insert.1 hu with rfl | hu
        · rw [sub_self, zero_smul]
          exact Submodule.zero_mem _
        · exact Submodule.mem_sup_right (Submodule.smul_mem _ _
            (Submodule.mem_iSup_of_mem u (Submodule.mem_iSup_of_mem hu hz)))
    have h1 := hle hy'
    rw [Submodule.mem_comap, hφ s y hy] at h1
    obtain ⟨d, hd, h2⟩ := ih (fun u hu => hT u (Finset.mem_insert_of_mem hu)) _ (Submodule.smul_mem _ _ hy) h1
    exact ⟨d * (σ s a - σ t a), mul_ne_zero hd (sub_ne_zero.2 ha.symm), by rwa [mul_smul]⟩

theorem orthAt_saturation {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    {F F' G G' : Submodule (𝓞 L) B.carrier} (h : OrthAt B F F') (hG : ∀ x ∈ G, ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F)
    (hG' : ∀ x ∈ G', ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ F') : OrthAt B G G' := by
  intro σ x hx y hy
  obtain ⟨a, ha, hx⟩ := hG x hx
  obtain ⟨b, hb, hy⟩ := hG' y hy
  have h1 : inner ℂ (fibreVec B.metric σ (a • x)) (fibreVec B.metric σ (b • y)) = 0 := h σ _ hx _ hy
  rw [fibreVec_smul, fibreVec_smul, inner_smul_left, inner_smul_right] at h1
  have ha' : σ (a : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ha
  have hb' : σ (b : L) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hb
  exact (mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left ((map_ne_zero _).2 ha'))).resolve_left hb'

variable {E L Ψ V : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (ρM : 𝓞 E →+* Module.End (𝓞 L) A.Bq.carrier)

theorem eig_facts (hcard : 2 * Fintype.card Ψ = Module.finrank ℚ E)
    (hρ : ∀ (a : 𝓞 E) (x : A.Λ), A.f ⟨A.ρ a x, A.stable a x x.2⟩ = ρM a (A.f x)) :
    (∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s)) ∧
    (∀ s, A.Bq.normDegree (A.img s) ≤ A.Bq.normDegree (eigSp ρM (intLift (A.σ s)))) ∧
    ∑ s, A.Bq.normDegree (eigSp ρM (intLift (A.σ s))) ≤ A.Bq.normDegree ⊤ := by
  classical
  have h1 : ∀ s, A.img s ≤ eigSp ρM (intLift (A.σ s)) := by
    rintro s _ ⟨x, hx, rfl⟩
    have hx' : (x : V) ∈ eigSp A.ρ (A.σ s) := (Submodule.mem_inf.1 hx).2
    refine (mem_eigSp_iff _ _ _).2 fun a => ?_
    rw [← hρ, ← map_smul]
    congr 1
    refine Subtype.ext ?_
    change A.ρ a x = intLift (A.σ s) a • (x : V)
    rw [(mem_eigSp_iff _ _ _).1 hx' a, ← algebraMap_smul L (intLift (A.σ s) a), intLift_apply]
  have h2 : ∀ s, ∀ y ∈ eigSp ρM (intLift (A.σ s)), ∃ a : 𝓞 L, a ≠ 0 ∧ a • y ∈ A.img s := by
    intro s y hy
    have h3 : y ∈ CanonicalFiltration.saturation A.Bq (⨆ t, A.img t) := by
      rw [A.saturation_iSup_img hcard]
      exact Submodule.mem_top
    obtain ⟨c, hc, h3⟩ := h3
    have hle : (⨆ t, A.img t) ≤ A.img s ⊔ ⨆ t ∈ Finset.univ.erase s, eigSp ρM (intLift (A.σ t)) := by
      refine iSup_le fun t z hz => ?_
      by_cases hts : t = s
      · subst hts
        exact Submodule.mem_sup_left hz
      · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem t
          (Submodule.mem_iSup_of_mem (Finset.mem_erase.2 ⟨hts, Finset.mem_univ t⟩) (h1 t hz)))
    obtain ⟨d, hd, h4⟩ := exists_smul_mem_of_eig ρM (fun t => intLift (A.σ t)) s (A.img s) (h1 s) (Finset.univ.erase s)
      (fun t ht h => (Finset.mem_erase.1 ht).1 (A.σ_bij.1 (RingHom.ext fun a => by
        rw [← intLift_apply, ← intLift_apply (A.σ s)]
        exact congrArg _ (DFunLike.congr_fun h a)))) _ (Submodule.smul_mem _ c hy) (hle h3)
    exact ⟨d * c, mul_ne_zero hd hc, by rwa [mul_smul]⟩
  have mono : ∀ {X Y : Submodule (𝓞 L) A.Bq.carrier}, X ≤ Y → A.Bq.rank X ≤ A.Bq.rank Y := fun h =>
    Submodule.finrank_mono h
  have h5 : ∀ s, A.Bq.rank (eigSp ρM (intLift (A.σ s))) = A.Bq.rank (A.img s) := fun s =>
    le_antisymm ((mono (Y := CanonicalFiltration.saturation A.Bq (A.img s)) fun y hy => h2 s y hy).trans
      (CanonicalFiltration.rank_saturation A.Bq _).le) (mono (h1 s))
  refine ⟨h5, fun s => div_le_div_of_nonneg_right
    (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq (h1 s) (h5 s).symm) (Nat.cast_nonneg _), ?_⟩
  have hI := GlobalTheory.T.normalized_degree_orthogonal_sum L A.Bq (Ψ ⊕ Ψ) (fun s => eigSp ρM (intLift (A.σ s))) fun s s' h =>
    orthAt_saturation A.Bq (F := A.img s) (F' := A.img s') (by
      rw [A.img_eq, A.img_eq]
      exact A.orth s s' h) (h2 s) (h2 s')
  have hr : A.Bq.rank (⨆ s, eigSp ρM (intLift (A.σ s))) = A.Bq.rank ⊤ := by
    refine le_antisymm (mono le_top) ?_
    have := CanonicalFiltration.rank_saturation A.Bq (⨆ s, A.img s)
    rw [A.saturation_iSup_img hcard] at this
    rw [this]
    exact mono (iSup_mono h1)
  rw [← hI.1]
  exact div_le_div_of_nonneg_right (CanonicalFiltration.degree_le_of_le_of_rank_eq A.Bq le_top hr) (Nat.cast_nonneg _)

end LevelTowerAlt
