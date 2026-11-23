import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhaseA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Finset

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem fnZ_const_mul (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) : fnZ P (fun _ => c) * f = c • f := by
  have hmem : (fun _ : MA.Qp P.r P.TT => c) ∈ MA.smSub P.r P.TT :=
    (MA.smSub P.r P.TT).algebraMap_mem c
  unfold fnZ MA.toSm
  rw [dif_pos hmem]
  apply Subtype.ext
  funext q
  simp

theorem sm_const_inj (P : M.Par) (q0 : MA.Qp P.r P.TT) {c c' : ℂ}
    (h : c • (1 : MA.SmQ P.r P.TT) = c' • (1 : MA.SmQ P.r P.TT)) : c = c' := by
  have h1 := congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) q0) h
  simpa using h1

theorem ss_fst_apply (P : M.Par) (l : ℕ) (τ σ : M.Ty P) (f : MA.SmQ P.r P.TT) :
    ((MA.SS P (MA.DQ P) l) τ σ).1 f =
      (if M.Up P l σ τ then (((Real.sqrt (M.Nrm P l σ)) : ℝ) : ℂ) else 0) • f := by
  unfold MA.SS
  simp only [Matrix.of_apply]
  split_ifs
  · rfl
  · rw [zero_smul]
    rfl

theorem star_ss_fst_apply (P : M.Par) (l : ℕ) (τ σ : M.Ty P) (f : MA.SmQ P.r P.TT) :
    ((star (MA.SS P (MA.DQ P) l)) τ σ).1 f =
      (if M.Up P l τ σ then (((Real.sqrt (M.Nrm P l τ)) : ℝ) : ℂ) else 0) • f := by
  rw [Matrix.star_apply]
  unfold MA.SS
  simp only [Matrix.of_apply]
  split_ifs
  · show ((algebraMap ℂ (MA.DQ P).Pr _).2.unop) f = _
    show (algebraMap ℂ (Module.End ℂ (MA.DQ P).R) (starRingEnd ℂ _)) f = _
    rw [Complex.conj_ofReal]
    rfl
  · simp; rfl

theorem pr_fst_smul (P : M.Par) (x : (MA.DQ P).Pr) (c : ℂ) (f : MA.SmQ P.r P.TT) :
    x.1 (c • f) = c • x.1 f := map_smul x.1 c f

theorem dzQ_smul (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) : dzQ P (c • f) = c • dzQ P f := map_smul ((MA.DQ P).dzP).1 c f

theorem dzbQ_smul (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) : dzbQ P (c • f) = c • dzbQ P f := map_smul ((MA.DQ P).dzbP).1 c f

theorem mulQ_smul (P : M.Par) (x : (MA.DQ P).Pr) (c : ℂ) (f : MA.SmQ P.r P.TT) :
    mulQ P x (c • f) = c • mulQ P x f := map_smul x.1 c f

theorem second_shift_phase_holds : GTSSPhase := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn s t hL hst
  classical
  obtain ⟨hpl, hk2, hcs, hLv, hSL, hRel, hQ⟩ := hH
  have hP : P.OK := hpl.1
  have hTT : 0 < P.TT := mul_pos hP.T_pos hP.T'_pos
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => 1), ((Real.sqrt P.TT + 1 : ℝ) : ℂ)), ⟨fun _ => one_ne_zero, ann_pt P hTT⟩⟩

  let CV : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' → (M.Ty P → ℂ) → Prop :=
    fun Ψ c => trR P Bs e Ψ = fun σ => c σ • (1 : MA.SmQ P.r P.TT)
  have cv_eq : ∀ Ψ c c', CV Ψ c → CV Ψ c' → c = c' := by
    intro Ψ c c' h1 h2
    funext σ
    exact sm_const_inj P q0 (congrFun (h1.symm.trans h2) σ)
  have cv_SS : ∀ l ∈ Icc 1 (P.k - 1), ∀ Ψ c, CV Ψ c → CV ((d.SS l).1 Ψ) (fun τ => ∑ σ, s l τ σ * c σ) := by
    intro l hl Ψ c h
    funext τ
    rw [(hL l hl Ψ τ).1, h, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [fnZ_const_mul, smul_smul]
  have cv_St : ∀ l ∈ Icc 1 (P.k - 1), ∀ Ψ c, CV Ψ c →
      CV ((star (d.SS l)).1 Ψ) (fun τ => ∑ σ, t l τ σ * c σ) := by
    intro l hl Ψ c h
    funext τ
    rw [(hL l hl Ψ τ).2, h, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [fnZ_const_mul, smul_smul]
  have cv_K : ∀ f Ψ c, CV Ψ c → CV ((d.κ f).1 Ψ) (fun τ => f τ * c τ) := by
    intro f Ψ c h
    funext τ
    rw [hk f Ψ, actA_kap, h, smul_smul]
  choose U hU using fun ρ : M.Ty P =>
    SSTr.exists_tr P Bs hpl hk2 e he (fun τ => if τ = ρ then (1 : MA.SmQ P.r P.TT) else 0)
  have cvU : ∀ ρ, CV (U ρ) (fun τ => if τ = ρ then 1 else 0) := by
    intro ρ
    show trR P Bs e (U ρ) = _
    rw [(hU ρ).1]
    funext τ
    by_cases h : τ = ρ <;> simp [h]

  have F1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ τ, ¬ M.Up P l ρ τ → s l τ ρ = 0 := by
    intro l hl ρ τ hnu
    have hr := hRel.2.2.2.1 l (fun σ => if σ = ρ then 1 else 0) (fun σ => if M.Up P l ρ σ then 1 else 0) (by
      intro σ σ' hU'
      by_cases h : σ = ρ
      · subst h; simp [hU']
      · have : ¬ M.Up P l ρ σ' := fun h2 => h (Formalism.FourierDecayAlt.P.Mx4.up_inj P l σ' σ ρ hU' h2)
        simp [h, this])
    have c1 := cv_K (fun σ => if M.Up P l ρ σ then 1 else 0) _ _ (cv_SS l hl _ _ (cvU ρ))
    have c2 := cv_SS l hl _ _ (cv_K (fun σ => if σ = ρ then 1 else 0) _ _ (cvU ρ))
    have e12 : (d.κ fun σ => if M.Up P l ρ σ then (1 : ℂ) else 0).1 ((d.SS l).1 (U ρ)) =
        (d.SS l).1 ((d.κ fun σ => if σ = ρ then (1 : ℂ) else 0).1 (U ρ)) :=
      congrArg (fun a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => a.1 (U ρ)) hr
    rw [e12] at c1
    have h := congrFun (cv_eq _ _ _ c1 c2) τ
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_neg hnu,
      zero_mul] at h
    rw [← h]

  have F2 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' →
      star (s l ρ' ρ) * s l ρ' ρ = ((M.Nrm P l ρ : ℝ) : ℂ) := by
    intro l hl ρ ρ' hU1
    have hN := hRel.2.2.2.2.2 l hl
    have c1 := cv_St l hl _ _ (cv_SS l hl _ _ (cvU ρ))
    have c2 := cv_K (fun σ => ((M.Nrm P l σ : ℝ) : ℂ)) _ _ (cvU ρ)
    have e12 : (star (d.SS l)).1 ((d.SS l).1 (U ρ)) = (d.κ fun σ => ((M.Nrm P l σ : ℝ) : ℂ)).1 (U ρ) :=
      congrArg (fun a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => a.1 (U ρ)) hN
    rw [e12] at c1
    have h := congrFun (cv_eq _ _ _ c1 c2) ρ
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h, Finset.sum_eq_single ρ', hst l hl ρ ρ']
    · intro σ _ hσ
      have : ¬ M.Up P l ρ σ := fun h2 => hσ (Formalism.FourierDecayAlt.P.Mx4.up_fun P l ρ σ ρ' h2 hU1)
      rw [F1 l hl ρ σ this, mul_zero]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  have L1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρl : M.Ty P, M.Up P l ρ ρl → ∀ (g : M.Ty P → ℂ) (c : ℂ),
      ∑ σ, g σ * (s l σ ρ * c) = g ρl * (s l ρl ρ * c) := by
    intro l hl ρ ρl hU1 g c
    rw [Finset.sum_eq_single ρl]
    · intro σ _ hσ
      have : ¬ M.Up P l ρ σ := fun h2 => hσ (Formalism.FourierDecayAlt.P.Mx4.up_fun P l ρ σ ρl h2 hU1)
      rw [F1 l hl ρ σ this, zero_mul, mul_zero]
    · intro h0; exact absurd (Finset.mem_univ _) h0

  have hIS : Wd.IsStart d.QQ (M.qC P) := by
    have h := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X).1
    rwa [show X.QQ = d.QQ from funext hQ] at h
  have hX := Formalism.FourierDecayAlt.P.shift_extra P _ d hP hSL hRel hIS
  have F3 : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
      s j ρlj ρl * s l ρl ρ * ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) =
        s l ρlj ρj * s j ρj ρ * ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) := by
    intro l hl j hj hjl ρ ρl ρj ρlj h1 h2 h3 h4
    have hc := ((hX.2 l hl).2 j hj hjl).1
    have c1 := cv_SS j hj _ _ (cv_SS l hl _ _
      (cv_K (fun σ => ((M.rho P σ j - M.rho P σ l - 1 : ℝ) : ℂ)) _ _ (cvU ρ)))
    have c2 := cv_SS l hl _ _ (cv_SS j hj _ _
      (cv_K (fun σ => ((M.rho P σ j - M.rho P σ l + 1 : ℝ) : ℂ)) _ _ (cvU ρ)))
    have e12 : (d.SS j).1 ((d.SS l).1 ((d.κ fun σ => ((M.rho P σ j - M.rho P σ l - 1 : ℝ) : ℂ)).1 (U ρ))) =
        (d.SS l).1 ((d.SS j).1 ((d.κ fun σ => ((M.rho P σ j - M.rho P σ l + 1 : ℝ) : ℂ)).1 (U ρ))) :=
      congrArg (fun a : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => a.1 (U ρ)) hc
    rw [e12] at c1
    have h := congrFun (cv_eq _ _ _ c1 c2) ρlj
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [L1 l hl ρ ρl h1, L1 j hj ρ ρj h2] at h
    rw [← mul_assoc, ← mul_assoc] at h
    exact h

  let sq : ℕ → M.Ty P → ℂ := fun l ρ => ((Real.sqrt (M.Nrm P l ρ) : ℝ) : ℂ)
  have hpos : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → 0 < M.Nrm P l ρ :=
    fun l hl ρ ρ' hU1 => ((Formalism.FourierDecayAlt.P.nrmFacts_statement P hP l hl ρ).1 ρ' hU1).1
  have hsq0 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → sq l ρ ≠ 0 := by
    intro l hl ρ ρ' hU1
    have := Real.sqrt_pos.2 (hpos l hl ρ ρ' hU1)
    show ((Real.sqrt (M.Nrm P l ρ) : ℝ) : ℂ) ≠ 0
    exact_mod_cast this.ne'
  let w : ℕ → M.Ty P → M.Ty P → ℂ := fun l ρ ρ' => s l ρ' ρ / sq l ρ
  have hsw : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → s l ρ' ρ = w l ρ ρ' * sq l ρ := by
    intro l hl ρ ρ' hU1
    exact (div_mul_cancel₀ _ (hsq0 l hl ρ ρ' hU1)).symm
  have hnorm_s : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖s l ρ' ρ‖ = Real.sqrt (M.Nrm P l ρ) := by
    intro l hl ρ ρ' hU1
    have h := F2 l hl ρ ρ' hU1
    rw [Complex.star_def, Complex.conj_mul'] at h
    have h' : ‖s l ρ' ρ‖ ^ 2 = M.Nrm P l ρ := by exact_mod_cast h
    rw [← h', Real.sqrt_sq (norm_nonneg _)]
  have hw1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖w l ρ ρ'‖ = 1 := by
    intro l hl ρ ρ' hU1
    have hs := Real.sqrt_pos.2 (hpos l hl ρ ρ' hU1)
    show ‖s l ρ' ρ / sq l ρ‖ = 1
    rw [norm_div, hnorm_s l hl ρ ρ' hU1]
    simp only [sq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact div_self hs.ne'
  have hcoc : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
        w j ρl ρlj * w l ρ ρl = w l ρj ρlj * w j ρ ρj := by
    intro l hl j hj hjl ρ ρl ρj ρlj h1 h2 h3 h4
    have f3 := F3 l hl j hj hjl ρ ρl ρj ρlj h1 h2 h3 h4
    rw [hsw j hj ρl ρlj h3, hsw l hl ρ ρl h1, hsw l hl ρj ρlj h4, hsw j hj ρ ρj h2] at f3
    have cr := (Formalism.FourierDecayAlt.P.Mx4.corner P hP l j hl hj hjl ρ ρl ρj h1 h2).1
    have cr' : sq j ρl * sq l ρ * ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) =
        sq l ρj * sq j ρ * ((M.rho P ρ j - M.rho P ρ l + 1 : ℝ) : ℂ) := by
      simp only [sq]; exact_mod_cast cr
    have hd := Formalism.FourierDecayAlt.P.Mx4.gap P hP l j hl hj hjl ρ ρl ρj h1 h2
    have hm : ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) ≠ 0 := by
      have : M.rho P ρ j - M.rho P ρ l - 1 ≠ 0 := by rcases hd with h | h <;> intro h0 <;> linarith
      exact_mod_cast this
    have hK : sq j ρl * sq l ρ * ((M.rho P ρ j - M.rho P ρ l - 1 : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hsq0 j hj ρl ρlj h3) (hsq0 l hl ρ ρl h1)) hm
    apply mul_right_cancel₀ hK
    linear_combination f3 - w l ρj ρlj * w j ρ ρj * cr'
  obtain ⟨u, hu1, hu⟩ := phase_exists P w hw1 hcoc
  have huS : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((fun ρ (_ : ℂ) => u ρ) ρ) (Ann P) ∧
      ∀ ζ ∈ Ann P, ‖(fun ρ (_ : ℂ) => u ρ) ρ ζ‖ = 1 := fun ρ => ⟨contDiffOn_const, fun _ _ => hu1 ρ⟩
  have hsu : ∀ ρ, star (u ρ) * u ρ = 1 := fun ρ => star_mul_self_of_norm (hu1 ρ)
  have tr' : ∀ Φ ρ, trR P Bs (fun ρ ζ => u ρ • e ρ ζ) Φ ρ = star (u ρ) • trR P Bs e Φ ρ := by
    intro Φ ρ
    rw [trR_phase P Bs e (fun ρ _ => u ρ) huS Φ ρ]
    exact fnZ_const_mul P _ _
  have tr'' : ∀ Φ ρ, trR P Bs e Φ ρ = u ρ • trR P Bs (fun ρ ζ => u ρ • e ρ ζ) Φ ρ := by
    intro Φ ρ
    rw [tr', smul_smul, mul_comm, hsu, one_smul]
  refine ⟨fun ρ ζ => u ρ • e ρ ζ, isFrameB_phase P Bs e (fun ρ _ => u ρ) he huS,
    kapF_phase P Bs d e (fun ρ _ => u ρ) huS hk, ?_, ?_⟩
  · intro Φ
    constructor
    · funext ρ
      rw [tr', (hn Φ).1, actA_nabA, actA_nabA, tr']
      rw [dzQ_smul, mulQ_smul, mulQ_smul, smul_add, smul_comm (star (u ρ)) ((M.aC P ρ : ℝ) : ℂ)]
    · funext ρ
      rw [tr', (hn Φ).2, actA_nabsA, actA_nabsA, tr']
      rw [dzbQ_smul, mulQ_smul, mulQ_smul, smul_add, smul_neg, smul_comm (star (u ρ)) ((M.aC P ρ : ℝ) : ℂ)]
  · intro l hl Φ
    constructor
    · funext τ
      rw [tr', (hL l hl Φ τ).1]
      show _ = ∑ σ, ((MA.SS P (MA.DQ P) l) τ σ).1 (trR P Bs (fun ρ ζ => u ρ • e ρ ζ) Φ σ)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [ss_fst_apply, fnZ_const_mul, tr'' Φ σ, smul_smul, smul_smul]
      congr 1
      by_cases hU1 : M.Up P l σ τ
      · rw [if_pos hU1, hsw l hl σ τ hU1, hu l hl σ τ hU1, star_mul]
        have h1 := hsu σ
        have h2 : star (w l σ τ) * w l σ τ = 1 := star_mul_self_of_norm (hw1 l hl σ τ hU1)
        linear_combination (sq l σ * star (u σ) * u σ) * h2 + sq l σ * h1
      · rw [if_neg hU1, F1 l hl σ τ hU1]; ring
    · funext τ
      rw [tr', (hL l hl Φ τ).2]
      show _ = ∑ σ, ((star (MA.SS P (MA.DQ P) l)) τ σ).1 (trR P Bs (fun ρ ζ => u ρ • e ρ ζ) Φ σ)
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [star_ss_fst_apply, fnZ_const_mul, tr'' Φ σ, smul_smul, smul_smul, hst l hl τ σ]
      congr 1
      by_cases hU1 : M.Up P l τ σ
      · rw [if_pos hU1, hsw l hl τ σ hU1, hu l hl τ σ hU1, star_mul]
        have h1 := hsu τ
        have h2 : star (w l τ σ) * w l τ σ = 1 := star_mul_self_of_norm (hw1 l hl τ σ hU1)
        have hr : star (sq l τ) = sq l τ := by simp [sq]
        rw [hr]
        linear_combination (sq l τ * star (u τ) * u τ) * h2 + sq l τ * h1
      · rw [if_neg hU1, F1 l hl τ σ hU1, star_zero]; ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
