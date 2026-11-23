import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.LieCovol

theorem exists_transport (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ))
    (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] (j : ℕ) (r : R ≃ Fin j) :
    ∃ Ψ : (ι → R → ℂ) ≃L[ℝ] (InfinitePlace K → Fin j → ℂ), MeasurePreserving Ψ volume volume ∧
      ∀ x : R → K, Ψ (fun v q => τ v (x q)) = GlobalTheory.LatFacts.emb K j (fun a => x (r.symm a)) := by
  classical
  have hbij : Function.Bijective fun v => InfinitePlace.mk (τ v) := by
    refine ⟨fun v₁ v₂ h => ?_, fun w => (hτ w).exists⟩
    obtain ⟨v, -, hv⟩ := hτ (InfinitePlace.mk (τ v₂))
    exact (hv v₁ h).trans (hv v₂ rfl).symm
  let e : ι ≃ InfinitePlace K := Equiv.ofBijective _ hbij
  have he : ∀ w, InfinitePlace.mk (τ (e.symm w)) = w := fun w => e.apply_symm_apply w
  let g : InfinitePlace K → (ℂ ≃ₗᵢ[ℝ] ℂ) := fun w =>
    if w.embedding = τ (e.symm w) then LinearIsometryEquiv.refl ℝ ℂ else Complex.conjLIE
  let Ψl : (ι → R → ℂ) ≃ₗ[ℝ] (InfinitePlace K → Fin j → ℂ) :=
    ((LinearEquiv.funCongrLeft ℝ (R → ℂ) e.symm).trans
      (LinearEquiv.piCongrRight fun _ => LinearEquiv.funCongrLeft ℝ ℂ r.symm)).trans
      (LinearEquiv.piCongrRight fun w => LinearEquiv.piCongrRight fun _ => (g w).toLinearEquiv)
  have hΨ : ∀ c w a, Ψl c w a = g w (c (e.symm w) (r.symm a)) := fun c w a => rfl
  refine ⟨Ψl.toContinuousLinearEquiv, ?_, fun x => ?_⟩
  · have h12 : MeasurePreserving
        (MeasurableEquiv.arrowCongr' e (MeasurableEquiv.arrowCongr' r (MeasurableEquiv.refl ℂ))) volume volume :=
      volume_preserving_arrowCongr' _ _ (volume_preserving_arrowCongr' _ _ (MeasurePreserving.id _))
    have h3 : MeasurePreserving (fun (y : InfinitePlace K → Fin j → ℂ) w a => g w (y w a)) volume volume :=
      measurePreserving_pi _ _ fun w => measurePreserving_pi _ _ fun _ => (g w).measurePreserving
    convert h3.comp h12 using 1
    funext c w a
    rfl
  · funext w a
    show Ψl _ w a = _
    rw [hΨ]
    simp only [GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    by_cases hw : w.embedding = τ (e.symm w)
    · simp only [g, if_pos hw]
      rw [hw]
      rfl
    · simp only [g, if_neg hw, Complex.conjLIE_apply]
      have h2 := InfinitePlace.embedding_mk_eq (τ (e.symm w))
      rw [he w] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 hw
      · rw [h2, NumberField.ComplexEmbedding.conjugate_coe_eq]

theorem exists_act (ι : Type) [Fintype ι] (R : Type) [Fintype R] [DecidableEq R] (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1) :
    ∃ Φ : (ι → R → ℂ) ≃L[ℝ] (ι → R → ℂ), MeasurePreserving Φ volume volume ∧ ∀ c v, Φ c v = M v *ᵥ c v := by
  classical
  have hinv : ∀ v, Invertible (M v) := fun v => Matrix.invertibleOfIsUnitDet _ (by rw [hM v]; exact isUnit_one)
  let e : ∀ v, (R → ℂ) ≃ₗ[ℝ] (R → ℂ) := fun v => (Matrix.toLinearEquiv' (M v) (hinv v)).restrictScalars ℝ
  let Φ : (ι → R → ℂ) ≃ₗ[ℝ] (ι → R → ℂ) := LinearEquiv.piCongrRight e
  refine ⟨Φ.toContinuousLinearEquiv, ?_, fun c v => ?_⟩
  · have hv : ∀ v, MeasurePreserving (e v) volume volume := by
      intro v
      have hdet : LinearMap.det (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ)) = 1 := by
        show LinearMap.det ((Matrix.toLin' (M v)).restrictScalars ℝ) = 1
        rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', hM v, map_one]
      refine ⟨(LinearMap.continuous_of_finiteDimensional (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))).measurable, ?_⟩
      have h := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (R → ℂ))
        (f := (e v : (R → ℂ) →ₗ[ℝ] (R → ℂ))) (by rw [hdet]; norm_num)
      rw [hdet] at h
      simpa using h
    exact MeasureTheory.measurePreserving_pi (fun _ => volume) (fun _ => volume) hv
  · rfl

theorem vInv_pow_le (K : Type) [Field K] [NumberField K] :
    Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have ha : 0 ≤ |(discr K : ℝ)| := abs_nonneg _
  have hroot : (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))) ^ Formalism.HermitianLatticesTheory.fDeg K = |(discr K : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    congr 1
    have : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
    field_simp
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [div_pow, hroot]
  exact div_le_self (Real.rpow_nonneg ha _) (one_le_pow₀ (by norm_num))

set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_eq_relIndex_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ = L₁.toAddSubgroup.relIndex L₂.toAddSubgroup * ZLattice.covolume L₂ μ := by
  classical
  let b₂ := Module.Free.chooseBasis ℤ L₂
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ L₁) = Fintype.card (Module.Free.ChooseBasisIndex ℤ L₂) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ← Module.finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ L₁, ZLattice.rank ℝ L₂]
  let b₁ := (Module.Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq hc)
  let c := b₂.ofZLatticeBasis ℝ L₂
  have hself : ((↑) ∘ b₂ : _ → E) = c := by
    funext i; simp [c]
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ c, ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ c,
    hself, Module.Basis.det_self, abs_one, one_mul, mul_eq_mul_right_iff]
  left
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂, Nat.cast_natAbs, Int.cast_abs]
  congr 1
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Int.cast_det]
  congr 1
  ext i k
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]
  exact b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ k, h (Submodule.coe_mem _)⟩ i

private theorem mem_span_ratB_iff_forall_mem_range (K : Type) [Field K] [NumberField K] (j : ℕ) (z : Fin j → K) :
    z ∈ Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.ratB K j)) ↔ ∀ a, z a ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨a, i⟩, rfl⟩ := hx
      intro b
      simp only [GlobalTheory.LatFacts.ratB, Pi.basis_apply]
      by_cases hb : b = a
      · subst hb
        simp [NumberField.integralBasis_apply]
      · simp [Pi.single_eq_of_ne hb]
    | zero => intro b; exact ⟨0, by simp⟩
    | add x y _ _ hx hy => intro b; simpa using add_mem (hx b) (hy b)
    | smul n x _ hx => intro b; simpa using zsmul_mem (hx b) n
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine Submodule.sum_mem _ fun a _ => ?_
    have h1 : z a ∈ Submodule.span ℤ (Set.range (NumberField.integralBasis K)) :=
      (NumberField.mem_span_integralBasis K).2 (hz a)
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single ℤ (fun _ : Fin j => K) a) h1
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨⟨a, i⟩, by simp [GlobalTheory.LatFacts.ratB, Pi.basis_apply]⟩

private theorem mem_span_intB_iff_exists_emb (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (j : ℕ)
    (y : GlobalTheory.FlagBase.VecInf K j) :
    y ∈ Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j)) ↔
      ∃ x : Fin j → 𝓞 K, GlobalTheory.LatFacts.emb K j (fun a => (x a : K)) = y := by
  have hr : Set.range (GlobalTheory.LatFacts.intB K j) =
      (GlobalTheory.LatFacts.emb K j).toIntLinearMap '' Set.range (GlobalTheory.LatFacts.ratB K j) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact GlobalTheory.LatFacts.intB_apply K j i
  rw [hr, ← Submodule.map_span, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_span_ratB_iff_forall_mem_range] at hz
    choose x hx using hz
    refine ⟨x, ?_⟩
    show GlobalTheory.LatFacts.emb K j _ = GlobalTheory.LatFacts.emb K j z
    congr 1
    funext a
    exact hx a
  · rintro ⟨x, rfl⟩
    exact ⟨fun a => (x a : K), (mem_span_ratB_iff_forall_mem_range K j _).2 fun a => ⟨x a, rfl⟩, rfl⟩

theorem exists_domain (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι]
    (τ : ι → (K →+* ℂ)) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) (R : Type) [Fintype R] [DecidableEq R]
    (H : AddSubgroup (R → 𝓞 K)) (hH : H.index ≠ 0) (M : ι → Matrix R R ℂ) (hM : ∀ v, (M v).det = 1)
    (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (x q)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧
      volume Ω ≤ ENNReal.ofReal (H.index * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R) := by
  classical
  have : (MeasureTheory.volume : MeasureTheory.Measure (GlobalTheory.FlagBase.VecInf K (Fintype.card R))).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (ι → R → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  set j := Fintype.card R with hj
  let r : R ≃ Fin j := Fintype.equivFin R
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_transport K ι τ hτ R j r
  obtain ⟨Φ, hΦ, hΦe⟩ := exists_act ι R M hM
  let T : (ι → R → ℂ) ≃L[ℝ] GlobalTheory.FlagBase.VecInf K j := Φ.trans Ψ
  have hT : MeasurePreserving T volume volume := hΨ.comp hΦ
  let g0 : (R → 𝓞 K) →+ (Fin j → K) :=
    { toFun := fun x a => ((x (r.symm a) : 𝓞 K) : K)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  let f0 : (R → 𝓞 K) →+ GlobalTheory.FlagBase.VecInf K j := (GlobalTheory.LatFacts.emb K j).comp g0
  have hf0 : ∀ x, f0 x = GlobalTheory.LatFacts.emb K j (fun a => ((x (r.symm a) : 𝓞 K) : K)) := fun x => rfl
  have hf0inj : Function.Injective f0 := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
    funext q
    have h1 := congrFun (congrFun hxy w) (r q)
    simp only [hf0, GlobalTheory.LatFacts.emb, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Equiv.symm_apply_apply] at h1
    exact Subtype.val_injective (w.embedding.injective h1)
  let Lf : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := Submodule.span ℤ (Set.range (GlobalTheory.LatFacts.intB K j))
  let LH : Submodule ℤ (GlobalTheory.FlagBase.VecInf K j) := AddSubgroup.toIntSubmodule (H.map f0)
  have hLH : ∀ y, y ∈ LH ↔ ∃ x ∈ H, f0 x = y := fun y => AddSubgroup.mem_map
  have hLf : Lf.toAddSubgroup = (⊤ : AddSubgroup (R → 𝓞 K)).map f0 := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and]
    rw [mem_span_intB_iff_exists_emb]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun q => x (r q), by rw [hf0]; simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨fun a => x (r.symm a), rfl⟩
  have hle : LH ≤ Lf := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := (hLH y).1 hy
    have h2 : f0 x ∈ Lf.toAddSubgroup := by
      rw [hLf]
      exact AddSubgroup.mem_map_of_mem _ (AddSubgroup.mem_top x)
    exact h2
  have hidx : LH.toAddSubgroup.relIndex Lf.toAddSubgroup = H.index := by
    rw [hLf, AddSubgroup.toIntSubmodule_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hf0inj,
      AddSubgroup.relIndex_top_right]
  have hdLf : DiscreteTopology Lf := by
    dsimp only [Lf]
    infer_instance
  have : IsZLattice ℝ Lf := by
    dsimp only [Lf]
    infer_instance
  have : DiscreteTopology LH := DiscreteTopology.of_subset (s := (Lf : Set _)) hdLf hle
  have : IsZLattice ℝ LH := by
    refine ⟨eq_top_iff.2 ?_⟩
    rw [← IsZLattice.span_top (K := ℝ) (L := Lf), Submodule.span_le]
    intro y hy
    have hmem : (LH.toAddSubgroup.relIndex Lf.toAddSubgroup) • y ∈ LH.toAddSubgroup :=
      AddSubgroup.nsmul_relIndex_mem _ hy
    rw [hidx] at hmem
    have hn : (H.index : ℝ) ≠ 0 := by exact_mod_cast hH
    have hy' : y = (H.index : ℝ)⁻¹ • ((H.index : ℝ) • y) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [hy']
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Nat.cast_smul_eq_nsmul]
    exact hmem
  have hΛeq : Λ = ZLattice.comap ℝ LH T.toLinearMap := by
    ext c
    rw [hΛ]
    show _ ↔ T c ∈ LH
    rw [hLH]
    have hTc : T c = Ψ (fun v => M v *ᵥ c v) := by
      show Ψ (Φ c) = _
      congr 1
      funext v
      exact hΦe c v
    rw [hTc]
    constructor
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, ?_⟩
      have e1 := hΨe (fun q => ((x q : 𝓞 K) : K))
      rw [hf0, ← e1]
      congr 1
      funext v
      exact (hxe v).symm
    · rintro ⟨x, hx, hxe⟩
      refine ⟨x, hx, fun v => ?_⟩
      have e1 := hΨe (fun q => ((x q : 𝓞 K) : K))
      rw [hf0, ← e1] at hxe
      exact (congrFun (Ψ.injective hxe) v).symm
  subst hΛeq
  let b := Module.Free.chooseBasis ℤ (ZLattice.comap ℝ LH T.toLinearMap)
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZSpan.fundamentalDomain_measurableSet _,
    ZLattice.isAddFundamentalDomain b volume, ?_⟩
  have hfin : volume (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcovLf : ZLattice.covolume Lf volume = Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * j) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain Lf volume
      (ZSpan.isAddFundamentalDomain (GlobalTheory.LatFacts.intB K j) volume)]
    exact GlobalTheory.LatFacts.volume_fd_intB K j
  rw [← ofReal_measureReal hfin, ← ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZLattice.isAddFundamentalDomain b volume), ZLattice.covolume_comap LH volume volume hT,
    covolume_eq_relIndex_mul volume LH Lf hle, hidx, hcovLf]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [pow_mul]
  exact pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.vInv; positivity) (vInv_pow_le K) _

theorem index_le (K : Type) [Field K] [NumberField K] (R S : Type) [Fintype R] [Fintype S] [DecidableEq S]
    (A : Matrix S R (𝓞 K)) (D : Matrix S S (𝓞 K)) (hD : D.det ≠ 0) :
    ∃ H : AddSubgroup (R → 𝓞 K), (∀ x, x ∈ H ↔ ∃ z, A *ᵥ x + D *ᵥ z = 0) ∧ H.index ≠ 0 ∧
      (H.index : ℝ) ≤ ∏ w : InfinitePlace K, w (D.det : 𝓞 K) ^ w.mult := by
  classical
  let gD : (S → 𝓞 K) →ₗ[ℤ] (S → 𝓞 K) := (Matrix.toLin' D).restrictScalars ℤ
  let fA : (R → 𝓞 K) →+ (S → 𝓞 K) := (Matrix.toLin' A).toAddMonoidHom
  let N : AddSubgroup (S → 𝓞 K) := (LinearMap.range gD).toAddSubgroup
  have hgD : ∀ z, gD z = D *ᵥ z := fun z => rfl
  have hfA : ∀ x, fA x = A *ᵥ x := fun x => rfl
  have hinj : Function.Injective gD := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hgD] at hz
    have h2 : D.det • z = 0 := by
      calc D.det • z = (D.det • (1 : Matrix S S (𝓞 K))) *ᵥ z := by
            rw [Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = D.adjugate *ᵥ (D *ᵥ z) := by rw [← Matrix.adjugate_mul, Matrix.mulVec_mulVec]
        _ = 0 := by rw [hz, Matrix.mulVec_zero]
    exact (smul_eq_zero.mp h2).resolve_left hD
  have hdet : LinearMap.det gD = Algebra.norm ℤ D.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin']
  let e : (S → 𝓞 K) ≃ₗ[ℤ] LinearMap.range gD := LinearEquiv.ofInjective gD hinj
  have hN : N.index = (Algebra.norm ℤ D.det).natAbs := by
    have h1 := Submodule.natAbs_det_equiv (LinearMap.range gD) e
    calc N.index = Nat.card ((S → 𝓞 K) ⧸ LinearMap.range gD) := rfl
      _ = _ := h1.symm
      _ = (LinearMap.det gD).natAbs := by
        congr 2
      _ = _ := by rw [hdet]
  have hN0 : N.index ≠ 0 := by
    rw [hN, Int.natAbs_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hD
  have hdvd : (N.comap fA).index ∣ N.index := by
    rw [AddSubgroup.index_comap]
    exact AddSubgroup.relIndex_dvd_index_of_normal _ _
  refine ⟨N.comap fA, ?_, ?_, ?_⟩
  · intro x
    rw [AddSubgroup.mem_comap]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [Matrix.mulVec_neg, ← hgD, hz, hfA, add_neg_cancel]
    · rintro ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [LinearMap.map_neg, hgD, hfA]
      exact (neg_eq_of_add_eq_zero_right (by rw [add_comm]; exact hz))
  · exact fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  · have hle : ((N.comap fA).index : ℝ) ≤ N.index := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
    refine hle.trans (le_of_eq ?_)
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int, hN, Nat.cast_natAbs]
    push_cast
    rfl

theorem exists_rows {K : Type} [Field K] {P S : Type} [Fintype P] [Fintype S] [DecidableEq S] (β : Matrix P S K)
    (h : Function.Injective β.mulVec) : ∃ e : S → P, (β.submatrix e id).det ≠ 0 := by
  have hrank : β.rank = Fintype.card S := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj (by simpa [Matrix.coe_mulVecLin] using h),
      Module.finrank_fintype_fun_eq_card]
  have hspan : Submodule.span K (Set.range β.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fintype_fun_eq_card]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K β.row
  have : Finite κ := Finite.of_injective a ha
  let _ : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card S := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp, hspan, finrank_top,
      Module.finrank_fintype_fun_eq_card]
  let f : S ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ f, ?_⟩
  have hli' : LinearIndependent K (β.submatrix (a ∘ f) id).row := by
    have e : (β.submatrix (a ∘ f) id).row = (β.row ∘ a) ∘ f := by
      ext s t
      rfl
    rw [e]
    exact hli.comp f f.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli')).ne_zero

variable {K : Type} [Field K] {N : ℕ}

theorem mul_mul_apply (A x B : Matrix (Fin N) (Fin N) K) (T : Finset (Fin N × Fin N))
    (hx : ∀ i j, (i, j) ∉ T → x i j = 0) (a b : Fin N) :
    (A * x * B) a b = ∑ q ∈ T, A a q.1 * B q.2 b * x q.1 q.2 := by
  have hz : ∀ q : Fin N × Fin N, q ∉ T → A a q.1 * B q.2 b * x q.1 q.2 = 0 :=
    fun q hq => by rw [hx q.1 q.2 hq, mul_zero]
  rw [Finset.sum_subset (Finset.subset_univ T) (fun q _ hq => hz q hq), Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem det_upUni {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : U.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => (hU i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl

theorem upUni_inv {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) : IsUpUni U⁻¹ := by
  have hdet : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have := U.invertibleOfIsUnitDet hdet
  have ht : U⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (hU i j).1 hij)
  intro i j
  refine ⟨fun h => ht h, ?_⟩
  rintro rfl
  have h1 : (U * U⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hdet]; simp
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rwa [(hU i i).2 rfl, one_mul] at h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [(hU i k).1 h, zero_mul]
    · rw [ht h, mul_zero]
  · simp

def conjMat (U : Matrix (Fin N) (Fin N) K) (R : Finset (Fin N × Fin N)) : Matrix R R K :=
  fun q q' => U⁻¹ q.1.1 q'.1.1 * U q'.1.2 q.1.2

theorem det_of_key {n κ : Type} [Fintype n] [DecidableEq n] [LinearOrder κ] (M : Matrix n n K) (k : n → κ)
    (hk : Function.Injective k) (h : ∀ i j, k j < k i → M i j = 0) : M.det = ∏ i, M i i := by
  let _ : LinearOrder n := LinearOrder.lift' k hk
  convert Matrix.det_of_isUpperTriangular (M := M) (fun i j hij => h i j hij)

theorem det_conjMat {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) (R : Finset (Fin N × Fin N)) :
    (conjMat U R).det = 1 := by
  have hUi := upUni_inv hU
  rw [det_of_key (conjMat U R) (fun q : R => toLex (q.1.1, OrderDual.toDual q.1.2))]
  · exact Finset.prod_eq_one fun q _ => by simp [conjMat, (hUi _ _).2 rfl, (hU _ _).2 rfl]
  · intro q q' h
    have h' := Prod.ext_iff.1 (toLex.injective h)
    exact Subtype.ext (Prod.ext h'.1 (OrderDual.toDual.injective h'.2))
  · intro q q' h
    simp only [conjMat]
    rcases Prod.Lex.lt_iff.1 h with h1 | ⟨_, h2⟩
    · have h1' : q'.1.1 < q.1.1 := h1
      rw [(hUi _ _).1 h1', zero_mul]
    · have h2' : q.1.2 < q'.1.2 := h2
      rw [(hU _ _).1 h2', mul_zero]

section Cell

variable {Z U : Matrix (Fin N) (Fin N) K} {R : Finset (Fin N × Fin N)}

theorem conjMat_mulVec (hU : IsUpUni U) {x : Matrix (Fin N) (Fin N) K}
    (hx : ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    conjMat U R *ᵥ (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2 := by
  have hd : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hx' : x = U⁻¹ * (U * x * U⁻¹) * U := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  funext q
  conv_rhs => rw [hx']
  rw [mul_mul_apply U⁻¹ (U * x * U⁻¹) U R hx, ← Finset.sum_coe_sort R]
  simp only [Matrix.mulVec, dotProduct, conjMat]

theorem exists_lie (hU : IsUpUni U) (y : R → K) :
    ∃ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) ∧ ∀ q : R, x q.1.1 q.1.2 = y q := by
  have hd : IsUnit (conjMat U R).det := by rw [det_conjMat hU]; exact isUnit_one
  have hUd : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  let z := (conjMat U R)⁻¹ *ᵥ y
  let w : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ R then z ⟨(i, j), h⟩ else 0
  have hw : U * (U⁻¹ * w * U) * U⁻¹ = w := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUd, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hUd]
  have hsupp : ∀ i j, (i, j) ∉ R → (U * (U⁻¹ * w * U) * U⁻¹) i j = 0 := by
    intro i j hij; rw [hw]; simp [w, hij]
  refine ⟨U⁻¹ * w * U, hsupp, fun q => ?_⟩
  have h1 := congrFun (conjMat_mulVec hU hsupp) q
  rw [hw] at h1
  have hwz : (fun q : R => w q.1.1 q.1.2) = z := by
    funext q'; simp [w, q'.2]
  rw [← h1, hwz]
  simp only [z, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]

def coRoots (R : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  Finset.univ.filter fun q => q.1 < q.2 ∧ q ∉ R

def eqMat {A : Type} [CommRing A] (Z : Matrix (Fin N) (Fin N) A) (T : Finset (Fin N × Fin N)) :
    Matrix {q : Fin N × Fin N // q.1 ≤ q.2} T A :=
  fun a q => Z a.1.1 q.1.1 * Z.adjugate q.1.2 a.1.2

theorem mem_lieU_iff (hR : ∀ q ∈ R, q.1 < q.2) {x : Matrix (Fin N) (Fin N) K} (hx : StrUp x) :
    x ∈ lieU Z ↔ eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
      eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2) = 0 := by
  have hsupp : ∀ i j, (i, j) ∉ R ∪ coRoots R → x i j = 0 := by
    intro i j hij
    rcases le_or_gt j i with hji | hij'
    · exact hx i j hji
    · exfalso
      apply hij
      by_cases hq : (i, j) ∈ R
      · exact Finset.mem_union_left _ hq
      · exact Finset.mem_union_right _ (by simp [coRoots, hij', hq])
  have hdisj : Disjoint R (coRoots R) := by
    rw [Finset.disjoint_right]
    intro q hq
    simp only [coRoots, Finset.mem_filter] at hq
    exact hq.2.2
  have key : ∀ a : {q : Fin N × Fin N // q.1 ≤ q.2},
      (eqMat Z R *ᵥ (fun q : R => x q.1.1 q.1.2) +
        eqMat Z (coRoots R) *ᵥ (fun q : coRoots R => x q.1.1 q.1.2)) a =
        (Z * x * Z.adjugate) a.1.1 a.1.2 := by
    intro a
    rw [mul_mul_apply Z x Z.adjugate (R ∪ coRoots R) hsupp, Finset.sum_union hdisj]
    simp only [Pi.add_apply, mulVec, dotProduct, eqMat]
    rw [Finset.sum_coe_sort R (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2),
      Finset.sum_coe_sort (coRoots R) (fun q => Z a.1.1 q.1 * Z.adjugate q.2 a.1.2 * x q.1 q.2)]
  constructor
  · rintro ⟨-, hlo⟩
    funext a
    rw [key]
    exact hlo _ _ a.2
  · intro h
    refine ⟨hx, fun i j hij => ?_⟩
    have := congrFun h ⟨(i, j), hij⟩
    rwa [key] at this

theorem eqMat_injective (hU : IsUpUni U) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) :
    Function.Injective (eqMat Z (coRoots R)).mulVec := by
  intro v w hvw
  have h0 : eqMat Z (coRoots R) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  rw [← sub_eq_zero]
  set u := v - w with hu
  let x : Matrix (Fin N) (Fin N) K := fun i j => if h : (i, j) ∈ coRoots R then u ⟨(i, j), h⟩ else 0
  have hxs : StrUp x := by
    intro i j hji
    simp only [x]
    rw [dif_neg]
    intro hm
    simp only [coRoots, Finset.mem_filter] at hm
    exact absurd hm.2.1 (not_lt.2 hji)
  have hxR : (fun q : R => x q.1.1 q.1.2) = 0 := by
    funext q
    simp only [x, Pi.zero_apply]
    rw [dif_neg]
    intro hm
    simp only [coRoots, Finset.mem_filter] at hm
    exact hm.2.2 q.2
  have hxC : (fun q : coRoots R => x q.1.1 q.1.2) = u := by
    funext q
    simp only [x]
    rw [dif_pos q.2]
  have hmem : x ∈ lieU Z := by
    rw [mem_lieU_iff hR hxs, hxR, hxC, Matrix.mulVec_zero, zero_add]
    exact h0
  have hsupp := (hc x).1 hmem
  have hconj := conjMat_mulVec hU hsupp
  rw [hxR] at hconj
  have hy : (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (by rw [det_conjMat hU R]; exact one_ne_zero) hconj
  have hall : U * x * U⁻¹ = 0 := by
    ext i j
    by_cases hij : (i, j) ∈ R
    · exact congrFun hy ⟨(i, j), hij⟩
    · exact hsupp i j hij
  have hUu : IsUnit U.det := by rw [det_upUni hU]; exact isUnit_one
  have hx0 : x = 0 := by
    have e : U⁻¹ * (U * x * U⁻¹) * U = x := by
      calc U⁻¹ * (U * x * U⁻¹) * U = (U⁻¹ * U) * x * (U⁻¹ * U) := by simp only [Matrix.mul_assoc]
        _ = x := by rw [Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul, Matrix.mul_one]
    rw [← e, hall, Matrix.mul_zero, Matrix.zero_mul]
  rw [← hxC, hx0]
  rfl

private theorem two_mul_card_le_sq_of_forall_fst_lt_snd {N : ℕ} (T : Finset (Fin N × Fin N)) (hT : ∀ q ∈ T, q.1 < q.2) :
    2 * T.card ≤ N ^ 2 := by
  have hdisj : Disjoint T (T.image Prod.swap) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq'
    exact absurd ((hT _ hp).trans (hT _ hq)) (lt_irrefl _)
  have hc : (T.image Prod.swap).card = T.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have h := Finset.card_le_univ (T ∪ T.image Prod.swap)
  rw [Finset.card_union_of_disjoint hdisj, hc, Fintype.card_prod, Fintype.card_fin] at h
  rw [sq, two_mul]
  exact h

private theorem factorial_sq_le_pow_self_of_two_mul_le (c m : ℕ) (h : 2 * c ≤ m) : c.factorial ^ 2 ≤ m ^ m := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simpa using Nat.one_le_pow m m hm
  · calc c.factorial ^ 2 ≤ (c ^ c) ^ 2 := Nat.pow_le_pow_left (Nat.factorial_le_pow c) 2
      _ = c ^ (2 * c) := by ring
      _ ≤ m ^ (2 * c) := Nat.pow_le_pow_left (by omega) _
      _ ≤ m ^ m := Nat.pow_le_pow_right (by omega) h

end Cell

theorem norm_det_eqMat_le (φ : K →+* ℂ) (Z : Matrix (Fin N) (Fin N) K) (b : ℝ)
    (hb : ∀ (t : ℕ) (I J : Fin t → Fin N), ‖φ ((Z.submatrix I J).det)‖ ≤ b) (T : Finset (Fin N × Fin N))
    (hT : ∀ q ∈ T, q.1 < q.2) (e : T → {q : Fin N × Fin N // q.1 ≤ q.2}) :
    ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2 ≤ (4 * (N : ℝ) ^ 2 * max 1 b ^ 4) ^ N ^ 2 := by
  have hb1 : 1 ≤ b := by simpa using hb 0 Fin.elim0 Fin.elim0
  rw [max_eq_right hb1]
  have hZ : ∀ i j, ‖φ (Z i j)‖ ≤ b := fun i j => by
    simpa [Matrix.det_unique] using hb 1 (fun _ => i) (fun _ => j)
  have hA : ∀ i j, ‖φ (Z.adjugate i j)‖ ≤ b := by
    intro i j
    cases N with
    | zero => exact i.elim0
    | succ n =>
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, map_mul, norm_mul, map_pow, map_neg, map_one,
        norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hb n _ _
  have hent : ∀ i j, NormedField.toAbsoluteValue ℂ
      ((φ.mapMatrix ((eqMat Z T).submatrix e id)) i j) ≤ b ^ 2 := by
    intro i j
    show ‖φ (Z _ _ * Z.adjugate _ _)‖ ≤ b ^ 2
    rw [map_mul, norm_mul, sq]
    exact mul_le_mul (hZ _ _) (hA _ _) (norm_nonneg _) (by linarith)
  have hdet := Matrix.det_le hent
  rw [← RingHom.map_det, Fintype.card_coe, nsmul_eq_mul] at hdet
  have hx : ‖φ ((eqMat Z T).submatrix e id).det‖ ≤ (T.card.factorial : ℝ) * (b ^ 2) ^ T.card := hdet
  have hc := two_mul_card_le_sq_of_forall_fst_lt_snd T hT
  have hfac : ((T.card.factorial : ℝ)) ^ 2 ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) := by
    exact_mod_cast factorial_sq_le_pow_self_of_two_mul_le T.card (N ^ 2) hc
  calc ‖φ ((eqMat Z T).submatrix e id).det‖ ^ 2
        ≤ ((T.card.factorial : ℝ) * (b ^ 2) ^ T.card) ^ 2 := by gcongr
      _ = ((T.card.factorial : ℝ)) ^ 2 * b ^ (4 * T.card) := by ring
      _ ≤ ((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2) := by
        exact mul_le_mul hfac (pow_le_pow_right₀ hb1 (by linarith)) (by positivity) (by positivity)
      _ ≤ (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) := by
        have h4 : (4 * (N : ℝ) ^ 2 * b ^ 4) ^ (N ^ 2) = 4 ^ (N ^ 2) * (((N : ℝ) ^ 2) ^ (N ^ 2) * b ^ (4 * N ^ 2)) := by
          rw [mul_pow, mul_pow, pow_mul b 4]
          ring
        rw [h4]
        exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4))

private theorem bijective_mk_and_isTotallyComplex_of_unique_place [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ))
    (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hrk : finrank ℚ K = 2 * Fintype.card ι) :
    Function.Bijective (fun v => InfinitePlace.mk (τ v)) ∧ IsTotallyComplex K := by
  have hb : Function.Bijective (fun v => InfinitePlace.mk (τ v)) :=
    ⟨fun a b h => (hτ _).unique rfl h.symm, fun w => (hτ w).exists⟩
  refine ⟨hb, ?_⟩
  have hc := Fintype.card_of_bijective hb
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [← nrRealPlaces_eq_zero_iff]
  omega

private theorem eqMat_map_ringHom {A : Type} [CommRing A] (f : A →+* K) (Z : Matrix (Fin N) (Fin N) A)
    (T : Finset (Fin N × Fin N)) : (eqMat Z T).map f = eqMat (Z.map f) T := by
  ext a q
  have h := congrFun (congrFun (RingHom.map_adjugate f Z) q.1.2) a.1.2
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  simp only [eqMat, Matrix.map_apply, map_mul, h]

theorem domain_of_cell [NumberField K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) {Z U : Matrix (Fin N) (Fin N) K}
    {R : Finset (Fin N × Fin N)} (B : ℝ) (Bv : ι → ℝ) (hτ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w)
    (hrk : finrank ℚ K = 2 * Fintype.card ι) (hU : IsUpUni U) (hZ : EntIn ⊤ Z)
    (hBv : ∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v ((Z.submatrix I J).det)‖ ≤ Bv v)
    (hprod : ∏ v, max 1 (Bv v) ≤ B) (hR : ∀ q ∈ R, q.1 < q.2)
    (hc : ∀ x, x ∈ lieU Z ↔ ∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) (Λ : Submodule ℤ (ι → R → ℂ))
    (hΛ : ∀ c, c ∈ Λ ↔ ∃ x ∈ lieU Z, EntIn ⊤ x ∧ ∀ v (q : R), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) :
    ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ IsAddFundamentalDomain Λ Ω volume ∧ volume Ω ≤
      ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) *
        ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  classical
  obtain ⟨hbij, hTC⟩ := bijective_mk_and_isTotallyComplex_of_unique_place ι τ hτ hrk
  choose FinalForm _ hZo using hZ
  set Z' : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of FinalForm with hZ'
  have hZmap : Z'.map (algebraMap (𝓞 K) K) = Z := by
    ext i j; simp [Z', hZo]
  set S := coRoots R with hSdef
  have hinj := eqMat_injective hU hR hc
  obtain ⟨e, he⟩ := exists_rows _ hinj
  set Ao : Matrix S R (𝓞 K) := (eqMat Z' R).submatrix e id with hAodef
  set Do : Matrix S S (𝓞 K) := (eqMat Z' S).submatrix e id with hDodef
  have hAo : Ao.map (algebraMap (𝓞 K) K) = (eqMat Z R).submatrix e id := by
    rw [← hZmap, ← eqMat_map_ringHom]; rfl
  have hDo : Do.map (algebraMap (𝓞 K) K) = (eqMat Z S).submatrix e id := by
    rw [← hZmap, ← eqMat_map_ringHom]; rfl
  have hDdet : algebraMap (𝓞 K) K Do.det = ((eqMat Z S).submatrix e id).det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det hDo
  have hD : Do.det ≠ 0 := by
    intro h; apply he; rw [← hDdet, h, map_zero]
  obtain ⟨H, hH, hHi, hHle⟩ := index_le K R S Ao Do hD
  set M : ι → Matrix R R ℂ := fun v => (conjMat U R).map (τ v) with hMdef
  have hM : ∀ v, (M v).det = 1 := fun v => by
    rw [show M v = (τ v).mapMatrix (conjMat U R) from rfl, ← RingHom.map_det, det_conjMat hU, map_one]
  have hMinj : ∀ v (a b : R → ℂ), M v *ᵥ a = M v *ᵥ b → a = b := fun v a b h =>
    sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero (by rw [hM v]; exact one_ne_zero)
      (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hMx : ∀ x : Matrix (Fin N) (Fin N) K, (∀ i j, (i, j) ∉ R → (U * x * U⁻¹) i j = 0) → ∀ v,
      M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) = fun q : R => τ v (x q.1.1 q.1.2) := by
    intro x hsx v
    funext q
    have h := RingHom.map_mulVec (τ v) (conjMat U R) (fun q : R => (U * x * U⁻¹) q.1.1 q.1.2) q
    rw [conjMat_mulVec hU hsx] at h
    exact h.symm
  have hrows : ∀ x : Matrix (Fin N) (Fin N) K, x ∈ lieU Z →
      (eqMat Z R).submatrix e id *ᵥ (fun q : R => x q.1.1 q.1.2) +
        (eqMat Z S).submatrix e id *ᵥ (fun q : S => x q.1.1 q.1.2) = 0 := by
    intro x hx
    funext s
    exact congrFun ((mem_lieU_iff hR hx.1).1 hx) (e s)
  have hΛ' : ∀ c, c ∈ Λ ↔ ∃ y ∈ H, ∀ v, M v *ᵥ c v = fun q => τ v (y q) := by
    intro c
    rw [hΛ c]
    constructor
    · rintro ⟨x, hx, hxi, hcx⟩
      choose xo _ hxo using hxi
      have hsx := (hc x).1 hx
      refine ⟨fun q => xo q.1.1 q.1.2, ?_, ?_⟩
      · rw [hH]
        refine ⟨fun s => xo s.1.1 s.1.2, ?_⟩
        funext s
        apply RingOfIntegers.coe_injective
        have key := congrFun (hrows x hx) s
        have e1 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao (fun q : R => xo q.1.1 q.1.2) s
        have e2 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Do (fun q : S => xo q.1.1 q.1.2) s
        rw [hAo] at e1
        rw [hDo] at e2
        have e3 : (algebraMap (𝓞 K) K ∘ fun q : R => xo q.1.1 q.1.2) = fun q : R => x q.1.1 q.1.2 := by
          funext q; exact hxo _ _
        have e4 : (algebraMap (𝓞 K) K ∘ fun q : S => xo q.1.1 q.1.2) = fun q : S => x q.1.1 q.1.2 := by
          funext q; exact hxo _ _
        rw [e3] at e1
        rw [e4] at e2
        have : algebraMap (𝓞 K) K ((Ao *ᵥ fun q : R => xo q.1.1 q.1.2) s + (Do *ᵥ fun q : S => xo q.1.1 q.1.2) s) = 0 := by
          rw [map_add, e1, e2]; exact key
        simpa using this
      · intro v
        rw [show c v = fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2) from funext (hcx v), hMx x hsx v]
        funext q
        simp [hxo]
    · rintro ⟨y, hy, hMy⟩
      obtain ⟨z, hz⟩ := (hH y).1 hy
      obtain ⟨x, hsx, hxy⟩ := exists_lie hU (fun q : R => (y q : K))
      have hx : x ∈ lieU Z := (hc x).2 hsx
      have hxz : (fun q : S => x q.1.1 q.1.2) = fun q : S => (z q : K) := by
        have k1 := hrows x hx
        have k2 : (eqMat Z R).submatrix e id *ᵥ (fun q : R => (y q : K)) +
            (eqMat Z S).submatrix e id *ᵥ (fun q : S => (z q : K)) = 0 := by
          funext s
          have e1 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Ao y s
          have e2 := RingHom.map_mulVec (algebraMap (𝓞 K) K) Do z s
          rw [hAo] at e1
          rw [hDo] at e2
          have := congrArg (algebraMap (𝓞 K) K) (congrFun hz s)
          rw [Pi.add_apply, map_add, e1, e2] at this
          exact this
        have hxR : (fun q : R => x q.1.1 q.1.2) = fun q : R => (y q : K) := funext hxy
        rw [hxR] at k1
        have k3 : (eqMat Z S).submatrix e id *ᵥ ((fun q : S => x q.1.1 q.1.2) - fun q : S => (z q : K)) = 0 := by
          rw [Matrix.mulVec_sub]
          have := k1.trans k2.symm
          rw [add_right_inj] at this
          rw [this, sub_self]
        exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero he k3)
      refine ⟨x, hx, ?_, ?_⟩
      · intro i j
        by_cases hij : j ≤ i
        · exact ⟨0, Submodule.mem_top, by simp [hx.1 i j hij]⟩
        · by_cases hR' : (i, j) ∈ R
          · exact ⟨y ⟨(i, j), hR'⟩, Submodule.mem_top, (hxy ⟨(i, j), hR'⟩).symm⟩
          · have hS : (i, j) ∈ S := by
              simp only [hSdef, coRoots, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨lt_of_not_ge hij, hR'⟩
            exact ⟨z ⟨(i, j), hS⟩, Submodule.mem_top, (congrFun hxz ⟨(i, j), hS⟩).symm⟩
      · intro v
        have h2 : M v *ᵥ c v = M v *ᵥ (fun q : R => τ v ((U * x * U⁻¹) q.1.1 q.1.2)) := by
          rw [hMy v, hMx x hsx v]
          funext q
          simp [hxy]
        exact congrFun (hMinj v _ _ h2)
  obtain ⟨Ω, hΩm, hΩf, hΩv⟩ := exists_domain K ι τ hτ R H hHi M hM Λ hΛ'
  refine ⟨Ω, hΩm, hΩf, hΩv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hmult : ∀ w : InfinitePlace K, w.mult = 2 := fun w => InfinitePlace.mult_isComplex ⟨w, hTC.isComplex w⟩
  have hDK : ((Do.det : 𝓞 K) : K) = ((eqMat Z S).submatrix e id).det := hDdet
  have hSup : ∀ q ∈ S, q.1 < q.2 := fun q hq => (Finset.mem_filter.1 hq).2.1
  have hidx : (H.index : ℝ) ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) := by
    refine hHle.trans ?_
    have hp : ∏ w : InfinitePlace K, w ((Do.det : 𝓞 K) : K) ^ w.mult =
        ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2 := by
      refine (Fintype.prod_bijective _ hbij _ _ (fun v => ?_)).symm
      rw [hmult, hDK, InfinitePlace.apply]
    rw [hp]
    calc ∏ v, ‖τ v (((eqMat Z S).submatrix e id).det)‖ ^ 2
        ≤ ∏ v, (4 * (N : ℝ) ^ 2 * max 1 (Bv v) ^ 4) ^ N ^ 2 :=
          Finset.prod_le_prod (fun v _ => by positivity)
            (fun v _ => norm_det_eqMat_le (τ v) Z (Bv v) (fun t I J => hBv t I J v) S hSup e)
      _ = ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * (∏ v, max 1 (Bv v)) ^ 4) ^ N ^ 2 := by
          rw [Finset.prod_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, Finset.card_univ]
      _ ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ N ^ 2 := by
          have h0 : 0 ≤ ∏ v, max 1 (Bv v) := Finset.prod_nonneg (fun v _ => le_trans zero_le_one (le_max_left _ _))
          gcongr
  have hd1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have ha : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / 2 : ℝ) := Real.one_le_rpow hd1 (by norm_num)
  have hcard : Fintype.card R ≤ N ^ 2 := by
    simpa [Fintype.card_coe, sq] using Finset.card_le_univ R
  have hpow : (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R ≤ (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) :=
    pow_le_pow_right₀ ha hcard
  have hC : 0 ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) := le_trans (Nat.cast_nonneg _) hidx
  calc (H.index : ℝ) * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ Fintype.card R
      ≤ ((4 * (N : ℝ) ^ 2) ^ Fintype.card ι * B ^ 4) ^ (N ^ 2) * (|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) :=
        mul_le_mul hidx hpow (by positivity) hC
    _ = _ := mul_comm _ _

theorem lie_lattice_domain : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (τ : ι → (K →+* ℂ)) (N : ℕ) (L U : Matrix (Fin N) (Fin N) K) (p : Point K N) (B : ℝ) (Bv : ι → ℝ), (∀ v a, τ v (star a) = starRingEnd ℂ (τ v a)) → (∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (τ v) = w) → finrank ℚ K = 2 * Fintype.card ι → IsLoUni L → IsUpUni U → EntIn ⊤ (L * ptMat p * U) → 1 ≤ B → (∀ (t : ℕ) (I J : Fin t → Fin N) (v : ι), ‖τ v (((L * ptMat p * U).submatrix I J).det)‖ ≤ Bv v) → ∏ v, max 1 (Bv v) ≤ B → ∀ Λ : Submodule ℤ (ι → roots (ptMat p) → ℂ), (∀ c, c ∈ Λ ↔ ∃ x ∈ lieU (L * ptMat p * U), EntIn ⊤ x ∧ ∀ v (q : roots (ptMat p)), c v q = τ v ((U * x * U⁻¹) q.1.1 q.1.2)) → ∃ Ω : Set (ι → roots (ptMat p) → ℂ), MeasurableSet Ω ∧ MeasureTheory.IsAddFundamentalDomain Λ Ω MeasureTheory.volume ∧ MeasureTheory.volume Ω ≤ ENNReal.ofReal ((|(discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ (N ^ 2) * ((4 * (N : ℝ) ^ 2) ^ (Fintype.card ι) * B ^ 4) ^ (N ^ 2)) := by
  intro K _ _ _ ι _ τ N L U p B Bv _ hτ hrk hL hU hZ _ hBv hprod Λ hΛ
  obtain ⟨-, h2, -, h4⟩ := GlobalTheory.LoopV.Cell.stab_cell K N L U p hL hU
  exact domain_of_cell ι τ B Bv hτ hrk hU hZ hBv hprod
    (fun q hq => (Finset.mem_filter.1 hq).2.1) (fun x => (h2 x).trans (h4 _)) Λ hΛ

end GlobalTheory.LieCovol
