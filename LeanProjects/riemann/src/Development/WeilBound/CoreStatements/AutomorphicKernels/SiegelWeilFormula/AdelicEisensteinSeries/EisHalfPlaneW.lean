import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.GodementSumW
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatSectionGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousDerivFamily
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.EisensteinGrowthForms.GrowForms

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.SiegelEis GlobalTheory.CompanionTheory.EisHalf

namespace PositivityTheory.SiegelWeilFormula.Aeis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem eis_half_plane_w {B : Base F E} (hB : B.IsGood σ) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (hH : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
      ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  have hKc : IsCompact (K : Set (G2 σ Y)) := isCompact_K_w hB hK
  obtain ⟨-, hpos⟩ := height_pos_w hB hK hH
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := godement_sum_w hB hb hK hH
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x : G2 σ Y,
      Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') := by
    intro σ' h x
    obtain ⟨_, _, h'⟩ := hσ σ' h
    exact (h' x).1
  have hterm : ∀ (z : ℂ) (x : G2 σ Y) (q : Cos σ Y),
      ‖eisTerm (flat a f s₁ z) x q‖ ≤ C * a ((Quotient.out q).1 * x) ^ (z.re + (n : ℝ) / 2) :=
    fun z x q => hC z _
  refine ⟨fun z x => ∑' q, eisTerm (flat a f s₁ z) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro z hz x
    have h1 : σ₀ < z.re + (n : ℝ) / 2 := by linarith
    exact (Summable.of_norm_bounded ((hsum _ h1 x).mul_left C) (hterm z x)).hasSum
  · intro x z hz
    have hz' : σ₀ - (n : ℝ) / 2 < z.re := hz
    obtain ⟨c, hc1, hc2⟩ := exists_between hz'
    set d : ℝ := z.re + 1 with hd
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hc3 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have hd3 : σ₀ < d + (n : ℝ) / 2 := by linarith
    have hu : Summable (fun q : Cos σ Y => |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2))) :=
      ((hsum _ hc3 x).add (hsum _ hd3 x)).mul_left _
    have hdiff : ∀ q : Cos σ Y,
        DifferentiableOn ℂ (fun w : ℂ => eisTerm (flat a f s₁ w) x q) {w : ℂ | c < w.re ∧ w.re < d} :=
      fun q => (differentiable_cpow_term (hpos _) s₁ _).differentiableOn
    have hle : ∀ (q : Cos σ Y) (w : ℂ), w ∈ {w : ℂ | c < w.re ∧ w.re < d} →
        ‖eisTerm (flat a f s₁ w) x q‖ ≤ |C| * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
          a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) := by
      intro q w hw
      have hA := hpos ((Quotient.out q).1 * x)
      have h2 := rpow_le_add_rpow (u := w.re + (n : ℝ) / 2) (c := c + (n : ℝ) / 2)
        (d := d + (n : ℝ) / 2) hA (by linarith [hw.1]) (by linarith [hw.2])
      have h3 := Real.rpow_nonneg hA.le (w.re + (n : ℝ) / 2)
      calc _ ≤ C * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) := hterm w x q
        _ ≤ |C| * a ((Quotient.out q).1 * x) ^ (w.re + (n : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h3
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
    have hD := Complex.differentiableOn_tsum_of_summable_norm hu hdiff hopen hle
    have hmem : {w : ℂ | c < w.re ∧ w.re < d} ∈ 𝓝 z :=
      hopen.mem_nhds ⟨hc2, by rw [hd]; linarith⟩
    exact (hD.differentiableAt hmem).differentiableWithinAt

theorem eis_half_mod_w {B : Base F E} (hB : B.IsGood σ) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) →
      (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧
      ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := height_pos_w hB hK ha
  have kc := isCompact_K_w hB hK
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := godement_sum_w hB hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)

theorem eisHalf_w {B : Base F E} (hB : B.IsGood σ) {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)}
    {a : G2 σ Y → ℝ} (hb : IsFrame2 σ Y b) (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) (χ : Chr F E) (s₁ : ℂ)
    (f : G2 σ Y → ℂ) (hf : IsSec K χ s₁ f) :
    ∃ (t : ℝ) (v : ℂ → modFun σ Y), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) ((v s).1 x)) ∧
      WHolo (growForms σ Y) v {s | t < s.re} := by
  obtain ⟨Ê, t, hsum, hhol⟩ := eis_half_plane_w hB hb hK ha χ s₁ f hf
  obtain ⟨t₀, hmod⟩ := eis_half_mod_w hB hb hK ha χ s₁ f hf
  obtain ⟨t', ht, ht₀⟩ : ∃ t' : ℝ, t ≤ t' ∧ t₀ ≤ t' := ⟨max t t₀, le_max_left _ _, le_max_right _ _⟩
  have hsum' : ∀ s : ℂ, t' < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x) :=
    fun s hs => hsum s (lt_of_le_of_lt ht hs)
  obtain ⟨hmem, hcont, hbd⟩ := hmod t' Ê ht₀ hsum'
  classical
  let v : ℂ → modFun σ Y := fun s => if h : t' < s.re then ⟨fun x => Ê s x, hmem s h⟩ else 0
  have hv : ∀ s : ℂ, t' < s.re → ∀ x, (v s).1 x = Ê s x := by
    intro s h x
    simp only [v, dif_pos h]
  refine ⟨t', v, fun s h x => by rw [hv s h x]; exact hsum' s h x, ?_⟩
  have hS : IsOpen {s : ℂ | t' < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine GlobalTheory.CompanionTheory.WeakHolo.wholo_growForms v hS ?_ ?_ ?_
  · intro x
    exact ((hhol x).mono fun s hs => lt_of_le_of_lt ht hs).congr fun s hs => hv s hs x
  · refine hcont.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    exact hv s hs x
  · intro Q hQ hQc
    rcases Q.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, 0, by simp⟩
    obtain ⟨z₁, hz₁, hmin⟩ := hQc.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨z₂, -, hmax⟩ := hQc.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨C, N, h⟩ := hbd z₁.re z₂.re (hQ hz₁)
    refine ⟨C, N, fun s hs x => ?_⟩
    rw [hv s (hQ hs) x]
    exact h s (hmin hs) (hmax hs) x

end PositivityTheory.SiegelWeilFormula.Aeis

end
