import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadDZCompLeft
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCRadSpSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section pts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem annZ_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    AnnZ P Bs = {ζ : ℂ | P.TT < Complex.normSq ζ} := by
  ext ζ
  simp only [Set.mem_setOf_eq]
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (X.fn j Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.2) •
        NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q := by
  unfold NF.radR
  rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
  exact X.fn_apply j Φ _ (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq)

theorem fnVal_zero (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 0 (NF.muZ P.k P.r Bs.μsec ζ) = ζ := by
  show Q.zetaL _ _ _ _ _ _ = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem fnVal_two (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 2 (NF.muZ P.k P.r Bs.μsec ζ) = starRingEnd ℂ ζ := by
  show star (Q.zetaL _ _ _ _ _ _) = _
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]
  rfl

theorem fnVal_five (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    {ζ : ℂ} (hζ : ζ ∈ AnnZ P Bs) : Q.fnVal P.k P.r Bs.z Bs.z' 5 (NF.muZ P.k P.r Bs.μsec ζ) =
      (((Complex.normSq ζ - Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' : ℝ)) : ℂ)⁻¹ := by
  show (((Q.GGl _ _ _ _ _ : ℝ)) : ℂ)⁻¹ = _
  unfold Q.GGl
  rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ]

theorem ggi_smooth (c : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)⁻¹)
      {ζ : ℂ | c < Complex.normSq ζ} := by
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => (((Complex.normSq ζ - c : ℝ)) : ℂ)) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - c) := by
      simp only [Complex.normSq_apply]
      exact ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)).sub contDiff_const
    exact Complex.ofRealCLM.contDiff.comp this
  refine hn.contDiffOn.inv fun ζ hζ h0 => ?_
  have h : c < Complex.normSq ζ := hζ
  have : Complex.normSq ζ - c = 0 := by exact_mod_cast h0
  linarith

theorem conj_smooth' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => starRingEnd ℂ ζ) :=
  Complex.conjCLE.contDiff

theorem radDZ_fn_left (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (j : Fin 6) (hj : j = 0 ∨ j = 2 ∨ j = 5)
    {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs (X.fn j * T) := by
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun ζ => Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec ζ)) (AnnZ P Bs) := by
    rcases hj with rfl | rfl | rfl
    · exact (contDiffOn_id (s := AnnZ P Bs)).congr fun ζ hζ => fnVal_zero P Bs hpl hζ
    · exact conj_smooth'.contDiffOn.congr fun ζ hζ => fnVal_two P Bs hpl hζ
    · exact (ggi_smooth _).congr fun ζ hζ => fnVal_five P Bs hpl hζ
  refine radDZ_fun_left hT _ hs fun Φ q hq => ?_
  rw [Module.End.mul_apply, radR_fn P Bs hpl X j _ q hq]

def Lp [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ) :
    (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
  ((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.Lin (B.hsVec (e ρ ζ)))).smulRight (e ρ ζ)).restrictScalars ℝ

theorem Lp_apply [FiniteDimensional ℂ Wp] {P : M.Par} (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (ζ : ℂ)
    (Xv : Wq →L[ℂ] Wp) : Lp e ρ ζ Xv = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec Xv) • e ρ ζ := rfl

theorem Lp_smooth [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)} (he : IsFrameB P Bs e) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Lp e ρ) (AnnZ P Bs) := by
  rw [contDiffOn_clm_apply]
  intro y
  rw [annZ_eq P Bs hpl]
  exact (((Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff.comp_contDiffOn (he.1 ρ)).inner ℂ contDiffOn_const).smul (he.1 ρ)).congr
    fun ζ _ => rfl

theorem radR_fib (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ) (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' q.2 := by
  intro p hp
  unfold NF.radR
  rw [Set.indicator_of_mem hq]
  have hx := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq
  have h := Θ.2.2.2 _ hx p.1 hp.1 p.2 hp.2.1
  simp only at h
  rw [hp.2.2] at h
  exact h.symm

theorem radR_kap [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      ∑ ρ, f ρ • (inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) • e ρ q.2) := by
  obtain ⟨hpl, hk2, -, -, -, -, -⟩ := hH
  have hζ : P.TT < Complex.normSq q.2 := by
    have h := hq.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1] at h
    exact h
  let q' : MA.Qp P.r P.TT := ⟨q, hq.1, hζ⟩
  have hw : ((wR P.k P.TT q.2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
    exact Real.sqrt_pos.2 (pow_pos (sub_pos.2 hζ) _)
  have hcoef : ∀ ρ, inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
      ((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) =
      f ρ * inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q)) := by
    intro ρ
    have hK := congrFun (hk f Φ) ρ
    rw [actA_kap] at hK
    have s1 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he ((d.κ f).1 Φ) ρ
    have s2 := radial_space_smoothness Wp Wq P Bs hpl hk2 e he Φ ρ
    unfold trR at hK
    rw [Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s1, Formalism.FourierDecayAlt.P.CutMP.Gauge.toSm_of_mem P s2] at hK
    have h3 := congrFun (congrArg Subtype.val hK) q'
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, rawR] at h3
    unfold NF.radR
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    have h4 : ((wR P.k P.TT q.2 : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.2))
        (B.hsVec (((d.κ f).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2))) =
        ((wR P.k P.TT q.2 : ℝ) : ℂ) * (f ρ * inner ℂ (B.hsVec (e ρ q.2))
          (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (NF.muZ P.k P.r Bs.μsec q.2)))) := by
      rw [h3]; ring
    exact mul_left_cancel₀ hw h4
  rw [(he.2 q.2 hζ).2.2 _ (radR_fib P Bs hpl _ q hq)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [hcoef ρ, mul_smul]

def dl {P : M.Par} (ρ : M.Ty P) : M.Ty P → ℂ := fun ρ' => if ρ' = ρ then 1 else 0

theorem radR_kap_dl [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ)
    (hq : q ∈ NF.QR P.k P.r Bs.z Bs.z') :
    NF.radR P.k P.r Bs.z Bs.z' Bs.μsec ((d.κ (dl ρ)).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q =
      Lp e ρ q.2 (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q) := by
  rw [radR_kap P Bs X d hH e he hk _ Φ q hq, Finset.sum_eq_single ρ]
  · simp [dl, Lp_apply]
  · intro b _ hb; simp [dl, hb]
  · intro h; exact absurd (Finset.mem_univ ρ) h

theorem radDZ_kap_left [FiniteDimensional ℂ Wp] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (hH : GTHyp P Bs X d) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (ρ : M.Ty P) {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : RadDZ P Bs T) :
    RadDZ P Bs ((d.κ (dl ρ)).1 * T) :=
  radDZ_comp_left hT (Lp e ρ) (Lp_smooth P Bs hH.1 he ρ) fun Φ q hq => by
    rw [Module.End.mul_apply, radR_kap_dl P Bs X d hH e he hk ρ _ q hq]

end pts

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.LNab
