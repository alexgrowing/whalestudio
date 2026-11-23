import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CanonicalPsiNeZeroOfPathBasis

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CrxMa

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem continuous_matrix_lower_left_block : Continuous (fun M : M2 n => M.toBlocks₂₁) := by
  have : (fun M : M2 n => M.toBlocks₂₁) = fun M => M.submatrix Sum.inr Sum.inl := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_matrix_lower_right_block : Continuous (fun M : M2 n => M.toBlocks₂₂) := by
  have : (fun M : M2 n => M.toBlocks₂₂) = fun M => M.submatrix Sum.inr Sum.inr := by funext M; rfl
  rw [this]; exact continuous_id.matrix_submatrix _ _

theorem continuous_cayley_first_block : Continuous (fun M : M2 n => u1 M) := by
  unfold u1
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).add continuous_matrix_lower_right_block

theorem continuous_cayley_second_block : Continuous (fun M : M2 n => u2 M) := by
  unfold u2
  exact ((continuous_const : Continuous fun _ : M2 n => Complex.I).smul continuous_matrix_lower_left_block).neg.add continuous_matrix_lower_right_block

theorem isOpen_OmZ (hFz : FzHol) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) : IsOpen {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  isOpen_setK (hFz n 0 0).1 Kg ι hι

theorem gset_sub_OmZ (hFz : FzHol) {Kg : Type} (ι : Kg → M2 n) (hιG : ∀ k, InG (ι k)) :
    GSet n ⊆ {x : M2 n | ∀ k, ι k * x ∈ DomZ n} :=
  fun _g hg k => (hFz n 0 0).2.1 (inG_mul (hιG k) hg)

theorem continuousOn_vacuum_at_zero (hFz : FzHol) (m : ℕ) : ContinuousOn (fun x : M2 n => fz m 0 0 x) (DomZ n) := by
  intro x hx
  have hA := (hFz n m 0).2.2 ((0 : ℂ), x) ⟨Set.mem_univ _, hx⟩
  have hmk : Continuous fun y : M2 n => ((0 : ℂ), y) := by fun_prop
  exact (hA.continuousAt.comp hmk.continuousAt).continuousWithinAt

theorem continuous_rhoP (hFz : FzHol) (m : ℕ) {Kg : Type} [TopologicalSpace Kg] (ι : Kg → M2 n)
    (hι : Continuous ι) (hιG : ∀ k, InG (ι k)) (Y : Matrix (Fin n) (Fin n) ℂ) : Continuous (rhoP ι m 0 Y) := by
  unfold rhoP
  have hfz : Continuous fun k => fz m 0 0 (ι k) :=
    (continuousOn_vacuum_at_zero hFz m).comp_continuous hι (fun k => (hFz n m 0).2.1 (hιG k))
  have hinv : Continuous fun k => (u2 (ι k))⁻¹ := by
    have e : (fun k => (u2 (ι k))⁻¹) = fun k => (u2 (ι k)).det⁻¹ • (u2 (ι k)).adjugate := by
      funext k; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [e]
    have hd := (continuous_cayley_second_block.comp hι).matrix_det
    exact (hd.inv₀ (fun k => det_second_cayley_block_ne_zero (hιG k))).smul ((continuous_cayley_second_block.comp hι).matrix_adjugate)
  exact (hfz.mul (((hinv.matrix_mul continuous_const).matrix_mul (continuous_cayley_first_block.comp hι)).matrix_trace)).star

theorem contDiffOn_PhiZ (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [TopologicalSpace Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasure μ] (ι : Kg → M2 n) (hι : Continuous ι)
    (c : Kg → ℂ) (hc : Continuous c) :
    ContDiffOn ℂ ∞ (fun x => ∫ k, Fd m (ι k * x) * c k ∂μ) {x : M2 n | ∀ k, ι k * x ∈ DomZ n} := by
  have hF : ContDiffOn ℂ ∞ (Fd (n := n) m) (DomZ n) := (hFd n m).1.of_le le_top
  exact (PositivityTheory.Rg.Sw.LVs.holInt n Kg μ _ (fun k x => Fd m (ι k * x) * c k) (isOpen_OmZ hFz Kg ι hι)
    (fun N => continuousOn_iteratedFDeriv_translate (Fd m) (DomZ n) (hFz n 0 0).1 hF Kg ι hι c hc N)
    (fun k => (hF.comp (contDiff_mulLeft (ι k)).contDiffOn
      (fun x (hx : x ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}) => hx k)).mul contDiffOn_const)).1

theorem fubini_gen (F : M2 n → ℂ) (U : Set (M2 n)) (hF : ContinuousOn F U) (hGU : GSet n ⊆ U)
    (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
    (hιG : ∀ k, InG (ι k)) (ρ : Kg → ℂ) (hρ : Continuous ρ) (a b : M2 n) (ha : InG a) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t =
      ∫ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) ∂μ := by
  have hherm : Continuous (herm (n := n)) := by
    unfold herm; fun_prop
  have hnU : Continuous fun x : Fin n → Fin n → ℝ => nU (herm x) := by
    unfold nU; exact Continuous.matrix_fromBlocks continuous_const hherm continuous_const continuous_const
  have hmap : Continuous fun z : Kg × (Fin n → Fin n → ℝ) => ι z.1 * a * nU (herm z.2) * b :=
    (((hι.comp continuous_fst).mul continuous_const).mul (hnU.comp continuous_snd)).mul continuous_const
  set Fp : Kg × (Fin n → Fin n → ℝ) → ℂ := fun z => F (ι z.1 * a * nU (herm z.2) * b) * ψ z.2 * ρ z.1 with hFpdef
  have hFc : Continuous Fp :=
    ((hF.comp_continuous hmap (fun z => hGU (inG_mul (inG_mul (inG_mul (hιG z.1) ha) (inG_nU_herm z.2)) hb))).mul
      (hψ.1.comp continuous_snd)).mul (hρ.comp continuous_fst)
  have hFs : HasCompactSupport Fp := by
    refine IsCompact.of_isClosed_subset (isCompact_univ.prod hψ.2.1) (isClosed_tsupport Fp) ?_
    refine closure_minimal (fun z hz => ⟨Set.mem_univ _, subset_tsupport ψ ?_⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
    intro h0; apply hz; simp [hFpdef, h0]
  have hFi : Integrable Fp (μ.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  have e1 : ∀ k, ρ k * (∫ t, F (1 * ι k * a * nU (herm t) * b) * ψ t) = ∫ t, Fp (k, t) := by
    intro k; rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hFpdef, Matrix.one_mul]; ring
  have e2 : ∀ t, (∫ k, F (ι k * (a * nU (herm t) * b)) * ρ k ∂μ) * ψ t = ∫ k, Fp (k, t) ∂μ := by
    intro t; rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hFpdef, Matrix.mul_assoc]; ring
  simp_rw [e1, e2]
  exact (integral_integral_swap (f := fun k x => Fp (k, x)) hFi).symm

theorem stepA_Z (hFd : FdProps) (hFz : FzHol) (m : ℕ) (Kg : Type) [Group Kg] [TopologicalSpace Kg]
    [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg)
    [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι) (hK : ∀ g, InK g ↔ ∃ k, ι k = g)
    (hneg : ∀ (P : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n), IsSingTest ψ → InG a →
      InG b → InG x → deriv (fun z => tOp μ ι (rhoP ι m 0 P) ψ a b (fz m 0 z) x) 0 = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) (a b : M2 n) (ha : InG a) (hb : InG b) :
    detD (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) = 0 := by
  have hιG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have hΩo := isOpen_OmZ hFz Kg ι hι
  have hGΩ := gset_sub_OmZ hFz ι hιG
  have hρ := continuous_rhoP hFz m ι hι hιG Y
  have hΦ := contDiffOn_PhiZ hFd hFz m Kg μ ι hι _ hρ
  have hpre : IsOpen {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} :=
    hΩo.preimage (contDiff_nU_sandwich a b).continuous
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈
      {H : Matrix (Fin n) (Fin n) ℂ | a * nU H * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}} := by
    show a * nU 0 * b ∈ {x : M2 n | ∀ k, ι k * x ∈ DomZ n}
    have : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, Matrix.fromBlocks_one]
    rw [this, mul_one]; exact hGΩ (inG_mul ha hb)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  refine singToDiff n (fun H => ∫ k, Fd m (ι k * (a * nU H * b)) * rhoP ι m 0 Y k ∂μ) r hr
    (hΦ.comp (contDiff_nU_sandwich a b).contDiffOn (fun H hH => hball hH)) ?_
  intro ψ hψ
  have h1 := hneg Y ψ a b 1 hψ ha hb inG_one
  rw [(hFd n m).2 Kg μ ι hι hK (rhoP ι m 0 Y) ψ a b 1 hρ hψ.1 hψ.2.1 ha hb inG_one] at h1
  rw [← h1]
  have hFc : ContinuousOn (Fd (n := n) m) (DomZ n) := (hFd n m).1.continuousOn
  exact fubini_gen (Fd m) (DomZ n) hFc (hFz n 0 0).2.1 Kg μ ι hι hιG _ hρ a b ha hb ψ hψ

end PositivityTheory.Rg.Sw.HSt.CrxMa
