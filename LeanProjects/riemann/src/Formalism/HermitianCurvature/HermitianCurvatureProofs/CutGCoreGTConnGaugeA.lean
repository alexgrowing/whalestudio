import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem torus_parameter : GTCTT := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH
  have hOK : P.OK := hH.1.1
  show 0 ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  first
  | rfl
  | (simp [B.hsVec]; done)
  | (unfold B.hsVec; rw [← WithLp.toLp_smul]; rfl)

theorem star_mul_self_of_norm {z : ℂ} (h : ‖z‖ = 1) : star z * z = 1 := by
  calc star z * z = (starRingEnd ℂ) z * z := rfl
    _ = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
    _ = 1 := by rw [h]; norm_num

theorem isFrameB_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ) (he : IsFrameB P Bs e)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1) :
    IsFrameB P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  obtain ⟨hs, hf⟩ := he
  refine ⟨fun ρ => (hu ρ).1.smul (hs ρ), fun ζ hζ => ?_⟩
  obtain ⟨hF, hO, hX⟩ := hf ζ hζ
  have hn : ∀ ρ, star (u ρ ζ) * u ρ ζ = 1 := fun ρ => star_mul_self_of_norm ((hu ρ).2 ζ hζ)
  refine ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun X hXF => ?_⟩
  · have h1 := hF ρ
    beta_reduce
    simp only [NF.Fib, Set.mem_setOf_eq] at h1 ⊢
    intro p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h1 p hp]
  · beta_reduce
    rw [hsVec_smul, hsVec_smul, inner_smul_left, inner_smul_right, hO ρ ρ']
    split_ifs with h
    · subst h
      rw [mul_one]
      exact hn ρ
    · rw [mul_zero, mul_zero]
  · conv_lhs => rw [hX X hXF]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    beta_reduce
    rw [hsVec_smul, inner_smul_left, smul_smul]
    congr 1
    rw [show (starRingEnd ℂ) (u ρ ζ) = star (u ρ ζ) from rfl]
    linear_combination (-(inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X))) * hn ρ

end frame

section trans

theorem comp_snd_mem_smSub (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    (fun q : MA.Qp P.r P.TT => v q.1.2) ∈ MA.smSub P.r P.TT := by
  show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => v q.1.2)) (MA.Qset P.r P.TT)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => v x.2) (MA.Qset P.r P.TT) :=
    hv.comp contDiff_snd.contDiffOn (fun x hx => show P.TT < Complex.normSq x.2 from hx.2)
  exact h1.congr (fun x hx => by simp [MA.ext, hx])

theorem fnZ_eq_mk (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    fnZ P v = ⟨fun q => v q.1.2, comp_snd_mem_smSub P hv⟩ := by
  unfold fnZ MA.toSm
  exact dif_pos (comp_snd_mem_smSub P hv)

theorem toSm_mulZ (P : M.Par) {v w : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P))
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ann P)) (hvw : ∀ ζ ∈ Ann P, w ζ * v ζ = 1)
    (g : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (fun q => v q.1.2 * g q) = fnZ P v * MA.toSm P g := by
  by_cases hg : g ∈ MA.smSub P.r P.TT
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hv) hg
    rw [fnZ_eq_mk P hv]
    unfold MA.toSm
    rw [dif_pos hvg, dif_pos hg]
    rfl
  · have hvg : (fun q : MA.Qp P.r P.TT => v q.1.2 * g q) ∉ MA.smSub P.r P.TT := by
      intro h
      apply hg
      have h2 := (MA.smSub P.r P.TT).mul_mem (comp_snd_mem_smSub P hw) h
      convert h2 using 1
      funext q
      have h3 : w q.1.2 * v q.1.2 = 1 := hvw q.1.2 q.2.2
      simp only [Pi.mul_apply]
      rw [← mul_assoc, h3, one_mul]
    unfold MA.toSm
    rw [dif_neg hvg, dif_neg hg, mul_zero]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rawR_phase (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (u : M.Ty P → ℂ → ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μsec (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fun q => star (u ρ q.1.2) * rawR P μsec e Φ ρ q := by
  funext q
  simp only [rawR, hsVec_smul, inner_smul_left]
  rw [show star (u ρ q.1.2) = (starRingEnd ℂ) (u ρ q.1.2) from rfl]
  ring

theorem conj_smooth {v : ℂ → ℂ} {s : Set ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ => star (v ζ)) s := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  exact hs.comp_contDiffOn hv

theorem trR_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) :
    trR P Bs (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fnZ P (fun ζ => star (u ρ ζ)) * trR P Bs e Φ ρ := by
  simp only [trR]
  rw [rawR_phase]
  exact toSm_mulZ P (conj_smooth (hu ρ).1) (hu ρ).1
    (fun ζ hζ => by
      show u ρ ζ * star (u ρ ζ) = 1
      rw [mul_comm]
      exact star_mul_self_of_norm ((hu ρ).2 ζ hζ)) _

end trans

section act

def mulQ (P : M.Par) (x : (MA.DQ P).Pr) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := x.1 f

theorem actA_diag (P : M.Par) (x : M.Ty P → (MA.DQ P).Pr) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (Matrix.diagonal x : MA.A P (MA.DQ P)) g ρ = (x ρ).1 (g ρ) := by
  unfold MA.actA
  refine (Fintype.sum_eq_single ρ (fun b hb => ?_)).trans ?_
  · have h0 := congrArg (fun m : (MA.DQ P).Pr => m.1 (g b)) (Matrix.diagonal_apply_ne x (Ne.symm hb))
    exact h0.trans (by first | rfl | simp)
  · exact congrArg (fun m : (MA.DQ P).Pr => m.1 (g ρ)) (Matrix.diagonal_apply_eq x ρ)

theorem algebraMap_fst_apply (P : M.Par) (c : ℂ) (f : MA.SmQ P.r P.TT) :
    (algebraMap ℂ (MA.DQ P).Pr c).1 f = c • f := rfl

theorem actA_kap (P : M.Par) (f : M.Ty P → ℂ) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.kap P (MA.DQ P) f) g ρ = f ρ • g ρ := by
  have hk : (MA.kap P (MA.DQ P) f : MA.A P (MA.DQ P)) =
      Matrix.diagonal (fun π => algebraMap ℂ (MA.DQ P).Pr (f π)) := by
    first
    | rfl
    | (ext i j; simp [MA.kap, Matrix.diagonal_apply])
  rw [hk, actA_diag, algebraMap_fst_apply]

theorem actA_nabA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabA P (MA.DQ P)) g ρ =
      dzQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zbP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabA
  rw [actA_diag]
  rfl

theorem actA_nabsA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.nabsA P (MA.DQ P)) g ρ =
      -dzbQ P (g ρ) + (M.aC P ρ : ℂ) • mulQ P (MA.DQ P).zP (mulQ P ((MA.DQ P).ggiP P.TT) (g ρ)) := by
  unfold MA.nabsA
  rw [actA_diag]
  rfl

end act

section kap

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem kapF_phase (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (u : M.Ty P → ℂ → ℂ)
    (hu : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1)
    (hk : KapF P Bs d e) : KapF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  unfold KapF at hk ⊢
  intro f Φ
  funext ρ
  rw [actA_kap, trR_phase P Bs e u hu, trR_phase P Bs e u hu, hk f Φ, actA_kap, mul_smul_comm]

end kap

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
