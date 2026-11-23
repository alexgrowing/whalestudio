import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.DomProof

section Maj

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sc (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) : E →L[ℝ] E :=
  ((2 : ℝ) ^ k)⁻¹ • ContinuousLinearMap.id ℝ E

theorem sc_apply (k : ℕ) (u : E) : sc E k u = ((2 : ℝ) ^ k)⁻¹ • u := rfl

theorem norm_sc_apply (k : ℕ) (u : E) : ‖sc E k u‖ = ((2 : ℝ) ^ k)⁻¹ * ‖u‖ := by
  rw [sc_apply, norm_smul, norm_inv, norm_pow, Real.norm_ofNat]

theorem norm_sc_le (k : ℕ) : ‖sc E k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [norm_sc_apply, one_mul]
  have h : ((2 : ℝ) ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two)
  exact mul_le_of_le_one_left (norm_nonneg _) h

theorem iter_term (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (z : ℂ) (k n : ℕ) (u : E) :
    iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u =
      z • (iteratedFDeriv ℝ n b (sc E k u)).compContinuousLinearMap fun _ => sc E k := by
  have h1 : ContDiff ℝ ∞ (b ∘ sc E k) := hb.comp (sc E k).contDiff
  have e : (fun v => z * b (sc E k v)) = z • (b ∘ sc E k) := rfl
  rw [e, iteratedFDeriv_const_smul_apply (h1.contDiffAt.of_le (by exact_mod_cast le_top)),
    (sc E k).iteratedFDeriv_comp_right hb u (by exact_mod_cast le_top)]

theorem term_bound (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (A : ℕ → ℝ) (hA : ∀ n x, ‖iteratedFDeriv ℝ n b x‖ ≤ A n)
    (z : ℂ) (k n : ℕ) (u : E) : ‖iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u‖ ≤ ‖z‖ * A n := by
  rw [iter_term b hb, norm_smul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h : ∏ _i : Fin n, ‖sc E k‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_sc_le k
  exact (mul_le_of_le_one_right (norm_nonneg _) h).trans (hA n _)

theorem term_zero (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0)
    (z : ℂ) (k n : ℕ) (u : E) (hu : (2 : ℝ) ^ (k + 1) < ‖u‖) :
    iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u = 0 := by
  rw [iter_term b hb, hs n _ ?_]
  · ext m
    simp
  · rw [norm_sc_apply, pow_succ] at *
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [inv_mul_eq_div, lt_div_iff₀ h2]
    linarith

theorem term_decay (b : E → ℂ) (hb : ContDiff ℝ ∞ b) (A : ℕ → ℝ) (hA : ∀ n x, ‖iteratedFDeriv ℝ n b x‖ ≤ A n)
    (hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0) (z : ℂ) (k n p : ℕ) (u : E) :
    ‖u‖ ^ p * ‖iteratedFDeriv ℝ n (fun v => z * b (sc E k v)) u‖ ≤ ((2 : ℝ) ^ (k + 1)) ^ p * (‖z‖ * A n) := by
  by_cases hu : (2 : ℝ) ^ (k + 1) < ‖u‖
  · rw [term_zero b hb hs z k n u hu, norm_zero, mul_zero]
    have : 0 ≤ A n := (norm_nonneg _).trans (hA n 0)
    positivity
  · have h1 := term_bound b hb A hA z k n u
    have h2 : ‖u‖ ^ p ≤ ((2 : ℝ) ^ (k + 1)) ^ p := pow_le_pow_left₀ (norm_nonneg _) (not_lt.1 hu) p
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)

def cf (C : ℕ → ℝ) (k : ℕ) : ℝ := ⨅ N : ℕ, C N * (2 / (2 : ℝ) ^ k) ^ N

theorem cf_nonneg {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (k : ℕ) : 0 ≤ cf C k :=
  le_ciInf fun N => mul_nonneg (hC N) (by positivity)

theorem cf_le {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (k N : ℕ) : cf C k ≤ C N * (2 / (2 : ℝ) ^ k) ^ N :=
  ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact mul_nonneg (hC M) (by positivity)⟩ N

theorem le_cf {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) {r y : ℝ} (hr : 0 ≤ r) (h : ∀ N : ℕ, (1 + r) ^ N * y ≤ C N) {k : ℕ}
    (hk : (2 : ℝ) ^ k ≤ 2 * (1 + r)) : y ≤ cf C k := by
  refine le_ciInf fun N => ?_
  have h1 : (0 : ℝ) < 1 + r := by linarith
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have h3 : 1 / (1 + r) ≤ 2 / (2 : ℝ) ^ k := by
    rw [div_le_div_iff₀ h1 h2]
    linarith
  have h4 : y ≤ C N * (1 / (1 + r)) ^ N := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h N
  exact h4.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 N) (hC N))

theorem summable_weighted {C : ℕ → ℝ} (hC : ∀ N, 0 ≤ C N) (p : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Summable fun k => ((2 : ℝ) ^ (k + 1)) ^ p * (‖(cf C k : ℂ)‖ * a) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_two.mul_left (2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * a))
  rw [Complex.norm_real, Real.norm_of_nonneg (cf_nonneg hC k)]
  have h1 := cf_le hC k (p + 1)
  have h2 : ((2 : ℝ) ^ (k + 1)) ^ p * (C (p + 1) * (2 / (2 : ℝ) ^ k) ^ (p + 1)) =
      2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * (1 / 2) ^ k := by
    have h0 : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [div_pow, one_div, inv_pow, pow_succ (2 : ℝ) k, mul_pow, pow_succ ((2 : ℝ) ^ k) p]
    field_simp
  calc ((2 : ℝ) ^ (k + 1)) ^ p * (cf C k * a)
      ≤ ((2 : ℝ) ^ (k + 1)) ^ p * ((C (p + 1) * (2 / (2 : ℝ) ^ k) ^ (p + 1)) * a) := by gcongr
    _ = 2 ^ p * (C (p + 1) * 2 ^ (p + 1)) * a * (1 / 2) ^ k := by
        rw [← mul_assoc, h2]
        ring

end Maj

section MajMain

open scoped ContDiff

theorem real_maj (E X : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : X → E) (w : X → ℝ) (h : ∀ N : ℕ, ∃ C : ℝ, ∀ x, (1 + ‖P x‖) ^ N * w x ≤ C) :
    ∃ F : SchwartzMap E ℂ, (∀ u, 0 ≤ (F u).re ∧ (F u).im = 0) ∧ ∀ x, w x ≤ (F (P x)).re := by
  choose C₀ hC₀ using h
  set C : ℕ → ℝ := fun N => max (C₀ N) 0 with hCd
  have hC : ∀ N, 0 ≤ C N := fun N => le_max_right _ _
  have hw : ∀ x N, (1 + ‖P x‖) ^ N * w x ≤ C N := fun x N => (hC₀ N x).trans (le_max_left _ _)
  let φ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  set b : E → ℂ := fun u => ((φ u : ℝ) : ℂ) with hbd
  have hb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp φ.contDiff
  have hsupp : tsupport b ⊆ Metric.closedBall (0 : E) 2 := by
    have : tsupport b ⊆ tsupport φ := closure_mono fun x hx h0 => hx (by simp [hbd, h0])
    rwa [φ.tsupport_eq] at this
  have hbs : HasCompactSupport b :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset (isClosed_tsupport b) hsupp
  have hA : ∀ n : ℕ, ∃ A : ℝ, ∀ x, ‖iteratedFDeriv ℝ n b x‖ ≤ A := fun n =>
    (hb.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support (hbs.iteratedFDeriv n)
  choose A hA using hA
  have hA0 : ∀ n, 0 ≤ A n := fun n => (norm_nonneg _).trans (hA n 0)
  have hs : ∀ n x, 2 < ‖x‖ → iteratedFDeriv ℝ n b x = 0 := by
    intro n x hx
    by_contra hne
    have h1 : x ∈ tsupport b := support_iteratedFDeriv_subset n hne
    have h2 := hsupp h1
    rw [mem_closedBall_zero_iff] at h2
    linarith
  set f : ℕ → E → ℂ := fun k v => (cf C k : ℂ) * b (sc E k v) with hfd
  have hf : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k => contDiff_const.mul (hb.comp (sc E k).contDiff)
  set v : ℕ → ℕ → ℝ := fun n k => ‖(cf C k : ℂ)‖ * A n with hvd
  have hsum : ∀ n, Summable (v n) := fun n => by
    have h0 := summable_weighted hC 0 (A n) (hA0 n)
    simp only [pow_zero, one_mul] at h0
    exact h0
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ ⊤ → Summable (v k) := fun k _ => hsum k
  have hd : ∀ (k i : ℕ) (x : E), (k : ℕ∞) ≤ ⊤ → ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i :=
    fun k i x _ => term_bound b hb A hA _ i k x
  let F : SchwartzMap E ℂ :=
    { toFun := fun x => ∑' k, f k x
      smooth' := contDiff_tsum hf hv hd
      decay' := fun p n => ⟨∑' k, ((2 : ℝ) ^ (k + 1)) ^ p * (‖(cf C k : ℂ)‖ * A n), fun x => by
        rw [iteratedFDeriv_tsum_apply hf hv hd (le_top) x]
        have hn : Summable fun k => ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hd n k x le_top) (hsum n)
        calc ‖x‖ ^ p * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ p * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hn
          _ = ∑' k, ‖x‖ ^ p * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ _ := (hn.mul_left _).tsum_le_tsum (fun k => term_decay b hb A hA hs _ k n p x)
              (summable_weighted hC p (A n) (hA0 n))⟩ }
  have hcf : Summable fun k => cf C k := by
    have := summable_weighted hC 0 1 zero_le_one
    simpa [Complex.norm_real, Real.norm_of_nonneg (cf_nonneg hC _), abs_of_nonneg (cf_nonneg hC _)] using this
  have hr : ∀ u, Summable fun k => cf C k * φ (sc E k u) := fun u =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (cf_nonneg hC k) φ.nonneg)
      (fun k => mul_le_of_le_one_right (cf_nonneg hC k) φ.le_one) hcf
  have hF : ∀ u, F u = ((∑' k, cf C k * φ (sc E k u) : ℝ) : ℂ) := fun u => by
    rw [Complex.ofReal_tsum]
    show ∑' k, f k u = _
    simp [hfd, hbd]
  refine ⟨F, fun u => ?_, fun x => ?_⟩
  · rw [hF, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨tsum_nonneg fun k => mul_nonneg (cf_nonneg hC k) φ.nonneg, rfl⟩
  · rw [hF, Complex.ofReal_re]
    obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (x := 1 + ‖P x‖) (y := (2 : ℝ))
      (by linarith [norm_nonneg (P x)]) one_lt_two
    have hk : (2 : ℝ) ^ (n + 1) ≤ 2 * (1 + ‖P x‖) := by
      rw [pow_succ]
      linarith
    have hone : φ (sc E (n + 1) (P x)) = 1 := by
      refine φ.one_of_mem_closedBall ?_
      rw [mem_closedBall_zero_iff, norm_sc_apply, inv_mul_eq_div]
      have h2' : (0 : ℝ) < 2 ^ (n + 1) := by positivity
      rw [div_le_iff₀ h2']
      show ‖P x‖ ≤ 1 * 2 ^ (n + 1)
      linarith
    have h3 := le_cf hC (norm_nonneg (P x)) (hw x) hk
    have h4 := (hr (P x)).le_tsum (n + 1) (fun k _ => mul_nonneg (cf_nonneg hC k) φ.nonneg)
    rw [hone, mul_one] at h4
    exact h3.trans h4

end MajMain

theorem fin_gen {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [AddCommGroup Y] [IsTopologicalAddGroup Y]
    (Pr : X → Y) (hPc : Continuous Pr) (U : Set Y) (hUc : IsClopen U) (hUk : IsCompact U) (h0 : (0 : Y) ∈ U)
    (g : X → ℂ) (hg : g ∈ WeilM.SB X) :
    ∃ G ∈ WeilM.SB Y, (∀ y, 0 ≤ (G y).re ∧ (G y).im = 0) ∧ ∀ x, ‖g x‖ ≤ (G (Pr x)).re := by
  obtain ⟨hl, hc⟩ := hg
  obtain ⟨C, hC⟩ := hl.continuous.bounded_above_of_compact_support hc
  have hK : IsCompact (Pr '' tsupport g) := hc.isCompact.image hPc
  have hHom : ∀ y : Y, IsClopen ((fun z => y + z) '' U) ∧ IsCompact ((fun z => y + z) '' U) := fun y =>
    ⟨⟨(Homeomorph.addLeft y).isClosed_image.2 hUc.1, (Homeomorph.addLeft y).isOpen_image.2 hUc.2⟩, hUk.image (continuous_const.add continuous_id)⟩
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun y => (fun z => y + z) '' U) fun y _ =>
    (hHom y).1.2.mem_nhds ⟨0, h0, add_zero y⟩
  set K : Set Y := ⋃ y ∈ t, (fun z => y + z) '' U with hKd
  have hKc : IsClopen K := t.finite_toSet.isClopen_biUnion fun y _ => (hHom y).1
  have hKk : IsCompact K := t.finite_toSet.isCompact_biUnion fun y _ => (hHom y).2
  set C' : ℝ := max C 0 with hC'
  have hC0 : 0 ≤ C' := le_max_right _ _
  have hnn : ∀ y, 0 ≤ (K.indicator (fun _ => ((C' : ℝ) : ℂ)) y).re ∧ (K.indicator (fun _ => ((C' : ℝ) : ℂ)) y).im = 0 := by
    intro y
    by_cases hy : y ∈ K
    · simp [Set.indicator_of_mem hy, hC0]
    · simp [Set.indicator_of_notMem hy]
  refine ⟨K.indicator fun _ => ((C' : ℝ) : ℂ), ⟨?_, ?_⟩, hnn, fun x => ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const Y ((C' : ℝ) : ℂ)) hKc).isLocallyConstant
  · refine hKk.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (fun y hy => by
      by_contra h
      exact hy (Set.indicator_of_notMem h _)) hKc.1
  · by_cases hx : g x = 0
    · simpa [hx] using (hnn (Pr x)).1
    · have hm : Pr x ∈ K := ht ⟨x, subset_tsupport g hx, rfl⟩
      rw [Set.indicator_of_mem hm, Complex.ofReal_re]
      exact (hC x).trans (le_max_left _ _)

theorem fin_dom (D : D7) (a b c : ℕ) (ι : Fin c → Fin b)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ G ∈ WeilM.SB (Fin a → Fin c → Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ y, 0 ≤ (G y).re ∧ (G y).im = 0) ∧ ∀ x, ‖g x‖ ≤ (G fun i j => x i (ι j)).re := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI h1 : IsTopologicalAddGroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.topologicalAddGroup (Af D.host.F) _
  haveI h2 : IsTopologicalAddGroup (Fin c → Af D.host.F ⊗[D.host.F] D.host.E) := Pi.topologicalAddGroup
  haveI h3 : IsTopologicalAddGroup (Fin a → Fin c → Af D.host.F ⊗[D.host.F] D.host.E) := Pi.topologicalAddGroup
  obtain ⟨U, hUc, hUk, h0⟩ := GlobalTheory.AfTensNbhd.exists_clopen_compact_nbhd_zero D a c
  exact fin_gen (fun x i j => x i (ι j))
    (continuous_pi fun i => continuous_pi fun j => (continuous_apply (ι j)).comp (continuous_apply i))
    U hUc hUk h0 g hg

theorem real_dom {T : Type} [Fintype T] (a b c : ℕ) (ι : Fin c → Fin b) (f : SchwartzMap (T → Fin a → Fin b → ℂ) ℂ) :
    ∃ F : SchwartzMap (T → Fin a → Fin c → ℂ) ℂ, (∀ u, 0 ≤ (F u).re ∧ (F u).im = 0) ∧
      ∀ v, ‖f v‖ ≤ (F fun τ i j => v τ i (ι j)).re := by
  refine real_maj (T → Fin a → Fin c → ℂ) (T → Fin a → Fin b → ℂ) (fun v τ i j => v τ i (ι j)) (fun v => ‖f v‖) fun N => ?_
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun v => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f v
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  have hP : ‖(fun τ i j => v τ i (ι j) : T → Fin a → Fin c → ℂ)‖ ≤ ‖v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun τ =>
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
          (norm_le_pi_norm (v τ i) (ι j)).trans ((norm_le_pi_norm (v τ) i).trans (norm_le_pi_norm v τ))
  gcongr

theorem pure_dom (D : D7) (θ : InfFam D) (a b c : ℕ) (ι : Fin c → Fin b)
    (f : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (g : (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ WeilM.SB (Fin a → Fin b → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ M ∈ schwartzA θ a c, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
      ∀ x : Mx D a b, ‖f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))‖ ≤
        (M (x.submatrix id ι)).re := by
  obtain ⟨F, hF, hFd⟩ := real_dom a b c ι f
  obtain ⟨G, hG, hG0, hGd⟩ := fin_dom D a b c ι g hg
  refine ⟨fun y => F (fun τ i j => compAt θ τ y i j) * G (fun i j => finPart D (y i j)),
    Submodule.subset_span ⟨F, G, hG, rfl⟩, fun y => ?_, fun x => ?_⟩
  · obtain ⟨h1, h2⟩ := hF (fun τ i j => compAt θ τ y i j)
    obtain ⟨h3, h4⟩ := hG0 (fun i j => finPart D (y i j))
    simp only [Complex.mul_re, Complex.mul_im, h2, h4, mul_zero, zero_mul, add_zero, sub_zero, and_true]
    exact mul_nonneg h1 h3
  · have h1 := hFd (fun τ i j => compAt θ τ x i j)
    have h2 := hGd (fun i j => finPart D (x i j))
    have e1 : (fun τ i j => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin a → Fin b → ℂ) τ i (ι j)) =
        (fun τ i j => compAt θ τ (x.submatrix id ι) i j) := rfl
    have e2 : (fun i j => (fun i j => finPart D (x i j) : Fin a → Fin b → _) i (ι j)) =
        (fun i j => finPart D ((x.submatrix id ι) i j)) := rfl
    rw [e1] at h1
    rw [e2] at h2
    obtain ⟨-, h4⟩ := hF (fun τ i j => compAt θ τ (x.submatrix id ι) i j)
    simp only [norm_mul, Complex.mul_re, h4, zero_mul, sub_zero]
    exact mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

end GlobalTheory.CompanionTheory.ColumnSplitting.DomProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem dom : Dom := by
  intro D θ _ a b c ι _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact DomProof.pure_dom D θ a b c ι f g hg
  | zero => exact ⟨0, zero_mem _, fun _ => by simp, fun _ => by simp⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨M₁, m₁, p₁, d₁⟩ := h1
    obtain ⟨M₂, m₂, p₂, d₂⟩ := h2
    refine ⟨M₁ + M₂, add_mem m₁ m₂, fun y => ?_, fun x => ?_⟩
    · simp only [Pi.add_apply, Complex.add_re, Complex.add_im, (p₁ y).2, (p₂ y).2, add_zero, and_true]
      exact add_nonneg (p₁ y).1 (p₂ y).1
    · simp only [Pi.add_apply, Complex.add_re]
      exact (norm_add_le _ _).trans (add_le_add (d₁ x) (d₂ x))
  | smul k φ _ h =>
    obtain ⟨M, m, p, d⟩ := h
    refine ⟨((‖k‖ : ℝ) : ℂ) • M, Submodule.smul_mem _ _ m, fun y => ?_, fun x => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        (p y).2, zero_mul, mul_zero, sub_zero, add_zero, and_true]
      exact mul_nonneg (norm_nonneg _) (p y).1
    · simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left (d x) (norm_nonneg _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
