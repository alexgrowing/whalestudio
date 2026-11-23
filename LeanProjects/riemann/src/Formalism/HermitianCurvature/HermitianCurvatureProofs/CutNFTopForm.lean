import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimENF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowFibre
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def TopDMeasCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → KB.CutWord P p.l0 w →
      AEStronglyMeasurable (topD p X w) volume

def NFApxDomAll : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖topD p (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) w c‖ ≤ h c

def NFFormCpt : Prop :=
  P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (w : List C.Letter) (Cb : ℝ),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base X → TBB.AdmW P p.l0 Y w →
    AEStronglyMeasurable (topD p X w) volume →
      (p.RR X 0 w [] []).re = ∫ c, topD p X w c

section iter

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def ptJ {j : ℕ} (c : Fin j → ℂ) : C.LPt := List.ofFn fun l => ((1 : ℕ), c l)

theorem ptJ_snoc {j : ℕ} (c : Fin j → ℂ) (t : ℂ) :
    ptJ (Fin.snoc (α := fun _ => ℂ) c t) = ptJ c ++ [((1 : ℕ), t)] := by
  unfold ptJ
  rw [List.ofFn_succ', List.concat_eq_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem isLocPt_ptJ {j : ℕ} (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) : D.IsLocPt (ptJ c) j := by
  refine ⟨fun b hb => ?_, ?_⟩
  · unfold ptJ at hb
    rw [List.mem_ofFn] at hb
    obtain ⟨l, rfl⟩ := hb
    exact ⟨le_rfl, hc l⟩
  · simp [D.ptSize, ptJ, List.map_ofFn, List.sum_ofFn]

theorem normC_one (w : List C.Letter) : TBB.normC (fun _ => 1) w = 1 := by
  unfold TBB.normC
  induction w with
  | nil => rfl
  | cons a w ih => simp

theorem ae_all_ne_zero (j : ℕ) : ∀ᵐ c : Fin j → ℂ, ∀ l, c l ≠ 0 := by
  refine ae_all_iff.2 fun l => ?_
  have h0 : (volume : Measure (Fin j → ℂ)) (Function.eval l ⁻¹' {0}) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ => volume) (measure_singleton (0 : ℂ))
  rw [ae_iff]
  refine measure_mono_null (fun c hc => ?_) h0
  simpa using hc

def EE (p : KB.Pl P Wp Wq) (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (c : Fin j → ℂ) : ℝ :=
  TBB.Ew p (fun _ => 1) X j w (ptJ c)

theorem EE_top_nonneg (p : KB.Pl P Wp Wq) (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (c : Fin (P.r + 1) → ℂ) : 0 ≤ EE p X w (P.r + 1) c := by
  unfold EE TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  refine mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (by rw [normC_one]; exact zero_le_one)) ?_
  exact TBBx3.rr_top_re_nonneg p X (P.r + 1) w _ (by omega)

theorem fibre_step (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (w : List C.Letter) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hX : KB.CptCoef p.T.base X)
    (hw : TBB.AdmW P p.l0 Y w) (j : ℕ) (hj : j ≤ P.r) (c : Fin j → ℂ) (hc : ∀ l, c l ≠ 0) :
    Integrable (fun t : ℂ => EE p X w (j + 1) (Fin.snoc (α := fun _ => ℂ) c t)) ∧
      EE p X w j c = ∫ t : ℂ, EE p X w (j + 1) (Fin.snoc (α := fun _ => ℂ) c t) := by
  have hl := isLocPt_ptJ c hc
  have key : Integrable (fun t : ℂ => TBB.NP p (fun _ => 1) X (j + 1) w (ptJ c ++ [((1 : ℕ), t)])
      (ptJ c ++ [((1 : ℕ), t)])) ∧
      ∫ t : ℂ, TBB.NP p (fun _ => 1) X (j + 1) w (ptJ c ++ [((1 : ℕ), t)]) (ptJ c ++ [((1 : ℕ), t)]) =
        TBB.NP p (fun _ => 1) X j w (ptJ c) (ptJ c) := by
    rcases Nat.lt_or_ge j P.r with hjr | hjr
    · exact glFibre hA Wp Wq P p (fun _ => 1) X Y w.length Cb hCb hX (fun _ => one_pos) j hjr w hw le_rfl
        (ptJ c) (ptJ c) hl hl
    · have hje : j = P.r := le_antisymm hj hjr
      subst hje
      obtain ⟨h1, h2⟩ := GT.top_level_fibre hA Wp Wq P p (fun _ => 1) X w Cb hCb hX hw.1 (ptJ c) (ptJ c) hl hl
      exact ⟨h1, h2.symm⟩
  obtain ⟨hint, heq⟩ := key
  have e : ∀ t : ℂ, EE p X w (j + 1) (Fin.snoc (α := fun _ => ℂ) c t) =
      (TBB.NP p (fun _ => 1) X (j + 1) w (ptJ c ++ [((1 : ℕ), t)]) (ptJ c ++ [((1 : ℕ), t)])).re := by
    intro t
    unfold EE TBB.Ew
    rw [ptJ_snoc]
  simp_rw [e]
  refine ⟨hint.re, ?_⟩
  unfold EE TBB.Ew
  rw [← heq]
  exact (integral_re hint).symm

end iter

section iter2

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem iter_levels (hA : P5.ThmPActual) (p : KB.Pl P Wp Wq) (X : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ)
    (w : List C.Letter) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hX : KB.CptCoef p.T.base X)
    (hw : TBB.AdmW P p.l0 Y w) (hmeas : AEStronglyMeasurable (topD p X w) volume) :
    ∀ m j : ℕ, j + m = P.r + 1 →
      (∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) → 0 ≤ EE p X w j c) ∧
      AEMeasurable (fun c : Fin j → ℂ => ENNReal.ofReal (EE p X w j c)) ∧
      ∫⁻ c : Fin j → ℂ, ENNReal.ofReal (EE p X w j c) = ∫⁻ c, ENNReal.ofReal (topD p X w c) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain rfl : j = P.r + 1 := by omega
    exact ⟨fun c _ => EE_top_nonneg p X w c, hmeas.aemeasurable.ennreal_ofReal, rfl⟩
  | succ m ih =>
    intro j hj
    obtain ⟨hnn', hm', he'⟩ := ih (j + 1) (by omega)
    have hjr : j ≤ P.r := by omega
    let e : (Fin (j + 1) → ℂ) ≃ᵐ (Fin j → ℂ) × ℂ :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) (Fin.last j)).trans MeasurableEquiv.prodComm
    have hmp : MeasurePreserving e volume volume :=
      (Measure.measurePreserving_swap).comp (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) => ℂ) (Fin.last j))
    have he : ∀ c, e c = ((fun i => c i.castSucc), c (Fin.last j)) := by
      intro c
      simp [e, MeasurableEquiv.piFinSuccAbove]
      rfl
    set g : (Fin j → ℂ) × ℂ → ENNReal :=
      fun q => ENNReal.ofReal (EE p X w (j + 1) (Fin.snoc (α := fun _ => ℂ) q.1 q.2)) with hg
    have hge : ∀ c, g (e c) = ENNReal.ofReal (EE p X w (j + 1) c) := by
      intro c
      rw [he c, hg]
      dsimp only
      congr 2
      exact Fin.snoc_init_self c
    have hgm : AEMeasurable g (volume.prod volume) := by
      have h1 : AEMeasurable (fun q => ENNReal.ofReal (EE p X w (j + 1) (e.symm q))) volume :=
        hm'.comp_quasiMeasurePreserving hmp.symm.quasiMeasurePreserving
      refine h1.congr (Filter.Eventually.of_forall fun q => ?_)
      dsimp only
      rw [← hge (e.symm q), e.apply_symm_apply]
    have hfib : ∀ c : Fin j → ℂ, (∀ l, c l ≠ 0) →
        0 ≤ EE p X w j c ∧ ENNReal.ofReal (EE p X w j c) = ∫⁻ t, g (c, t) := by
      intro c hc
      obtain ⟨hint, heq⟩ := fibre_step hA p X Y w Cb hCb hX hw j hjr c hc
      have hnnt : 0 ≤ᵐ[volume] fun t : ℂ => EE p X w (j + 1) (Fin.snoc (α := fun _ => ℂ) c t) := by
        filter_upwards [PBL.ae_ne_zero_complex] with t ht
        refine hnn' _ fun l => ?_
        induction l using Fin.lastCases with
        | last => simpa using ht
        | cast i => simpa using hc i
      refine ⟨heq ▸ integral_nonneg_of_ae hnnt, ?_⟩
      rw [heq, ofReal_integral_eq_lintegral_ofReal hint hnnt]
    have hae : (fun c : Fin j → ℂ => ENNReal.ofReal (EE p X w j c)) =ᵐ[volume] fun c => ∫⁻ t, g (c, t) := by
      filter_upwards [ae_all_ne_zero j] with c hc
      exact (hfib c hc).2
    refine ⟨fun c hc => (hfib c hc).1, ?_, ?_⟩
    · exact (hgm.lintegral_prod_right').congr hae.symm
    · rw [lintegral_congr_ae hae, ← lintegral_prod _ hgm, ← he']
      rw [show (volume.prod volume : Measure ((Fin j → ℂ) × ℂ)) = volume from rfl,
        ← hmp.lintegral_comp_emb e.measurableEmbedding]
      exact lintegral_congr fun c => hge c

theorem normal_form_compact_support_holds : NFFormCpt := by
  intro hA Wp Wq _ _ _ _ _ _ P p X Y w Cb hCb hX hw hmeas
  obtain ⟨-, -, h0⟩ := iter_levels hA p X Y w Cb hCb hX hw hmeas (P.r + 1) 0 (by omega)
  have hc0 : ∀ c : Fin 0 → ℂ, EE p X w 0 c = (p.RR X 0 w [] []).re := by
    intro c
    unfold EE ptJ
    rw [List.ofFn_zero, TBBx3.ew_zero_nil, normC_one, div_one]
  have hvol : (volume : Measure (Fin 0 → ℂ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  simp_rw [hc0] at h0
  rw [lintegral_const, hvol, mul_one] at h0
  have hnn : 0 ≤ᵐ[volume] topD p X w := Filter.Eventually.of_forall fun c => EE_top_nonneg p X w c
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas, ← h0]
  have hpos : 0 ≤ (p.RR X 0 w [] []).re := by
    have := (iter_levels hA p X Y w Cb hCb hX hw hmeas (P.r + 1) 0 (by omega)).1 Fin.elim0
      (fun l => l.elim0)
    rwa [hc0] at this
  rw [ENNReal.toReal_ofReal hpos]

end iter2

section assembly

theorem nfHyp_monoC {Cb C c : ℝ} {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    {p : KB.Pl P Wp Wq} {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} {A₀ : ℝ} {p₀ : ℕ} {χ : ℝ → ℝ} {N : ℕ}
    (hH : NFHyp Cb C p f A₀ p₀ χ N) (hc : c ≤ C) : NFHyp Cb c p f A₀ p₀ χ N := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hH
  refine ⟨a1, a2, a3, a4, le_trans ?_ a5, a6⟩
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by
    positivity
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) =
      x * (((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)) :=
    fun x => by ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc hX

theorem nFTopFormAll_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) : NFTopFormAll := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH (le_max_left C1 C2)
  have hH2 := nfHyp_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hform : ∀ n, (p.RR (apx H n) 0 w [] []).re = ∫ c, topD p (apx H n) w c := fun n =>
    normal_form_compact_support_holds hA Wp Wq P p (apx H n) Y w Cb hCb (hcpt' n) hw
      (hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1)
  have hlim0 : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (p.RR H 0 w [] []).re) := by
    have := (Complex.continuous_re.tendsto _).comp (hlim 0 w hw.1 hN [] [])
    refine this.congr fun n => ?_
    exact hform n
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hdct : Tendsto (fun n => ∫ c, topD p (apx H n) w c) atTop (𝓝 (∫ c, topD p H w c)) :=
    tendsto_integral_of_dominated_convergence h
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) hint hb
      (Filter.Eventually.of_forall hptw)
  exact tendsto_nhds_unique hlim0 hdct

theorem nFTopInt_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) (Cb : ℝ) : ∃ Cc : ℝ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (Y : Finset ℝ) (N : ℕ),
      NFHyp Cb Cc p f A₀ p₀ χ N → ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∀ ε : ℝ, 0 < ε →
        Integrable (topD p (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) w) := by
  obtain ⟨C1, H1⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨C2, H2⟩ := hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_monoC hH (le_max_left C1 C2)
  have hH2 := nfHyp_monoC hH (le_max_right C1 C2)
  obtain ⟨hχ, hCb, hf, hfA, hthr, -⟩ := hH1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF'ck : B.CkOn ⊤ (B.GV P.k P.r) F' := by
    rw [hF', fpm_id]
    exact ckOn_Gpow_smul _ _ p₀ hf
  obtain ⟨hcpt, hlim⟩ := H1 Wp Wq P p F' χ ε (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) N (cutN P.k P.r) hCb hχ hε
    hF'ck (inCC_fpm_id p p₀ hfA) hthr (fun _ _ => rfl)
  set H := D.cutF p.T.base χ F' ε with hHdef
  have hcpt' : ∀ n, KB.CptCoef p.T.base (apx H n) := hcpt
  have hptw : ∀ c, Tendsto (fun n => topD p (apx H n) w c) atTop (𝓝 (topD p H w c)) := by
    intro c
    unfold topD TBB.Ew TBB.NP
    exact (Complex.continuous_re.tendsto _).comp
      (tendsto_const_nhds.mul (hlim (P.r + 1) w hw.1 hN (TBB.bigPt P.r c) (TBB.bigPt P.r c)))
  obtain ⟨h, hint, hb⟩ := H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε
  have hm : AEStronglyMeasurable (topD p H w) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => hMeas Wp Wq P p (apx H n) w Cb hCb (hcpt' n) hw.1) (Filter.Eventually.of_forall hptw)
  refine hint.mono' hm ?_
  have hb' : ∀ᵐ c, ∀ n, ‖topD p (apx H n) w c‖ ≤ h c := ae_all_iff.2 hb
  filter_upwards [hb'] with c hc
  exact le_of_tendsto' ((continuous_norm.tendsto _).comp (hptw c)) hc

end assembly

end

end Formalism.FourierDecayAlt.P.CutBP
