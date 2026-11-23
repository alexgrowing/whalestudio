import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.MeasurePreservingOfAddEquiv

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {n : ℕ} {ψ : AddChar (AF F) ℂ}
  {v : HeightOneSpectrum (𝓞 F)} {μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)} {νv : Measure (HermR (Fv F v) σ n)}
  {lam : Measure (Fin n → Fv F v ⊗[F] E)} {L₁ L₂ : AddSubgroup (Fin n → Fv F v ⊗[F] E)}
  {Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ} {g : HermR (Fv F v) σ n → ℂ} {T : HermR (Fv F v) σ n}

theorem isClosed_herm (σ : E →ₐ[F] E) (n : ℕ) :
    IsClosed ((HermR (Fv F v) σ n : AddSubgroup (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :
      Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
  isClosed_hermSet v σ n

theorem isCompact_ballH (R : ℝ) : IsCompact {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} :=
  (isClosed_herm (v := v) σ n).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_ballM (v := v) (p := n) (q := n) R)

theorem measurableSet_ballH (R : ℝ) : MeasurableSet {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} := by
  have hc : IsClosed {b : HermR (Fv F v) σ n | nM v b.1 ≤ R} :=
    isClosed_le ((continuous_nM (v := v) (p := n) (q := n)).comp continuous_subtype_val) continuous_const
  exact hc.measurableSet

theorem lattice_norm_ge_one (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) (b : HermR (Fv F v) σ n) :
    1 ≤ nu2 lam L₁ L₂ b.1 := by
  have := h.haar
  unfold nu2
  set S : Set (Fin n → Fv F v ⊗[F] E) := {x | ∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.1.mulVec y'} with hS
  have hsub : (L₁ : Set (Fin n → Fv F v ⊗[F] E)) ⊆ S := fun y hy =>
    ⟨y, hy, 0, L₂.zero_mem, by simp⟩
  have hpos : lam L₁ ≠ 0 := (h.co₁.1.measure_pos lam ⟨0, L₁.zero_mem⟩).ne'
  have hfin1 : lam L₁ ≠ ⊤ := h.co₁.2.measure_lt_top.ne
  have hcS : IsCompact S := by
    have e : S = (fun p : (Fin n → Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1 + b.1.mulVec p.2) ''
        ((L₁ : Set (Fin n → Fv F v ⊗[F] E)) ×ˢ (L₂ : Set (Fin n → Fv F v ⊗[F] E))) := by
      ext x
      constructor
      · rintro ⟨y, hy, y', hy', rfl⟩
        exact ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
      · rintro ⟨⟨y, y'⟩, ⟨hy, hy'⟩, rfl⟩
        exact ⟨y, hy, y', hy', rfl⟩
    rw [e]
    exact (h.co₁.2.prod h.co₂.2).image (continuous_fst.add (continuous_const.matrix_mulVec continuous_snd))
  have hfinS : lam S ≠ ⊤ := hcS.measure_lt_top.ne
  have h1 : 1 ≤ lam S / lam L₁ := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin1), one_mul]
    exact measure_mono hsub
  have h2 := ENNReal.toReal_mono (ENNReal.div_ne_top hfinS hpos) h1
  rwa [ENNReal.toReal_one] at h2

theorem continuous_lattice_norm (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    Continuous fun b : HermR (Fv F v) σ n => nu2 lam L₁ L₂ b.1 := by
  have hev : ∀ᶠ d in 𝓝 (0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)),
      ∀ y' ∈ (L₂ : Set (Fin n → Fv F v ⊗[F] E)), d.mulVec y' ∈ L₁ := by
    refine h.co₂.2.eventually_forall_of_forall_eventually fun y' _ => ?_
    have hc : Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) =>
        p.1.mulVec p.2 := continuous_fst.matrix_mulVec continuous_snd
    have h0 : (fun p : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) × (Fin n → Fv F v ⊗[F] E) => p.1.mulVec p.2)
        ((0 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)), y') ∈ (L₁ : Set (Fin n → Fv F v ⊗[F] E)) := by
      simp only [Matrix.zero_mulVec]
      exact L₁.zero_mem
    exact hc.continuousAt.preimage_mem_nhds (h.co₁.1.mem_nhds h0)
  have key : ∀ b c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
      (∀ y' ∈ (L₂ : Set (Fin n → Fv F v ⊗[F] E)), (c - b).mulVec y' ∈ L₁) →
      nu2 lam L₁ L₂ c = nu2 lam L₁ L₂ b := by
    intro b c hcb
    have e : ∀ x : Fin n → Fv F v ⊗[F] E, (∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + c.mulVec y') ↔
        (∃ y ∈ L₁, ∃ y' ∈ L₂, x = y + b.mulVec y') := by
      intro x
      constructor
      · rintro ⟨y, hy, y', hy', rfl⟩
        refine ⟨y + (c - b).mulVec y', L₁.add_mem hy (hcb y' hy'), y', hy', ?_⟩
        rw [Matrix.sub_mulVec]
        abel
      · rintro ⟨y, hy, y', hy', rfl⟩
        refine ⟨y - (c - b).mulVec y', L₁.sub_mem hy (hcb y' hy'), y', hy', ?_⟩
        rw [Matrix.sub_mulVec]
        abel
    simp only [nu2, e]
  refine continuous_iff_continuousAt.2 fun b => ?_
  have ht : Tendsto (fun c : HermR (Fv F v) σ n => c.1 - b.1) (𝓝 b) (𝓝 0) := by
    have h1 : Tendsto (fun c : HermR (Fv F v) σ n => c.1) (𝓝 b) (𝓝 b.1) := continuous_subtype_val.tendsto b
    have h2 := h1.sub_const b.1
    rwa [sub_self] at h2
  have hb := ht.eventually hev
  exact (continuousAt_const (y := nu2 lam L₁ L₂ b.1)).congr (hb.mono fun c hc => (key b.1 c.1 hc).symm)

theorem uu_bound (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    ∃ C, ∀ b, ‖uu σ J ψ v μv Φv T b‖ ≤ C := by
  refine ⟨∫ Y, ‖Φv Y‖ ∂μv, fun b => ?_⟩
  unfold uu jtR
  rw [norm_mul, norm_psiV h.chr, mul_one]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext Y
  rw [norm_mul, norm_psiV h.chr, mul_one]

private theorem auxc_trPair {α : Type*} [TopologicalSpace α] {f g : α → Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => trPair (Fv F v) (f a) (g a) := by
  unfold trPair
  refine continuous_const.mul ((IsModuleTopology.continuous_of_linearMap
    (Algebra.trace (Fv F v) (Fv F v ⊗[F] E))).comp ?_)
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp hf)).mul
    ((continuous_apply i).comp ((continuous_apply j).comp hg))

private theorem auxc_gramR (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous (fun X : Fin n → Fin M → Fv F v ⊗[F] E => gramR (Fv F v) σ J X) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gramR, hR, hform]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((continuous_sigR v σ).comp ((continuous_apply i).comp (continuous_apply a))).mul
    continuous_const).mul ((continuous_apply j).comp (continuous_apply b))

theorem continuous_uu (h : Hyp σ M J n ψ v μv νv lam L₁ L₂ Φv g T) :
    Continuous (uu σ J ψ v μv Φv T) := by
  have : μv.IsAddHaarMeasure := h.sdW.1
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  have : SecondCountableTopology (HermR (Fv F v) σ n) :=
    TopologicalSpace.Subtype.secondCountableTopology
      (HermR (Fv F v) σ n : Set (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)))
  have hψc : Continuous (psiV F ψ v) := continuous_psiV h.chr
  have hΦc : Continuous Φv := h.sb.1.continuous
  have hgram := auxc_gramR (v := v) (n := n) σ J
  have hjt : Continuous fun b : HermR (Fv F v) σ n => jtR (Fv F v) σ J (psiV F ψ v) μv Φv b := by
    unfold jtR
    refine continuous_of_dominated (bound := fun Y => ‖Φv Y‖) (fun b => ?_) (fun b => ?_) ?_ ?_
    · exact (hΦc.mul (hψc.comp (auxc_trPair continuous_const hgram))).aestronglyMeasurable
    · exact Eventually.of_forall fun Y => by rw [norm_mul, norm_psiV h.chr, mul_one]
    · exact hΦc.norm.integrable_of_hasCompactSupport h.sb.2.norm
    · exact Eventually.of_forall fun Y =>
        continuous_const.mul (hψc.comp (auxc_trPair continuous_subtype_val continuous_const))
  unfold uu
  exact hjt.mul (hψc.comp (auxc_trPair continuous_const continuous_subtype_val).neg)

end PositivityTheory.SiegelWeilFormula.SwLocFin
