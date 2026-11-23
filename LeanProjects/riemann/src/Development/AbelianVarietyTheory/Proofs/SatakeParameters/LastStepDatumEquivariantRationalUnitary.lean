import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrimeStatement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopRat

section Frames
variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {u : Pr.Word} {j : ℕ}

theorem frsF_rat_notG (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
      g.1 * frsF sel mu p P := by
  unfold frsF
  rw [dif_neg hP, dif_neg hP]
  show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
  simp

theorem frsF_rat_G (hq : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∃ κ : ↥(GLint X.E (R.N j) P.1),
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG X.E (R.N j) Pr.vGs × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * frsF sel mu p P * κ.1 ∧
      ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x) ∈ stdAt X.E (R.N j) P.1 := by
  obtain ⟨κ, he, hr⟩ := liftFr_smul p.deco (g, (1 : GLG X.E (R.N j) Pr.vGs)) ⟨P.1, hP⟩
  refine ⟨κ, ?_, fun x hx => ?_⟩
  · unfold frsF
    rw [dif_pos hP, dif_pos hP]
    exact he
  · rw [GlobalTheory.TopStep.mem_stdAt]
    intro i
    have hkx := GlobalTheory.TopStep.mem_stdAt.1 ((κ.2 x).2 hx) i
    have hxi := GlobalTheory.TopStep.mem_stdAt.1 hx i
    have h1 := congrFun (hr x hx) i
    simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.one_mulVec] at h1
    have hred : redP P.1 (κ.1 x i - x i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hkx hxi]
      have h2 : redP P.1 (κ.1 x i) = redP P.1 (x i) := h1
      rw [h2, sub_self]
    have h := GlobalTheory.TopStep.intAt_div_of_redP (hq P hP) (GlobalTheory.TopStep.intAt_sub hkx hxi) hred
    have e : (((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x)) i = (κ.1 x i - x i) / (qOf P.1 : X.E) := by
      simp [div_eq_inv_mul]
    rw [e]
    exact h

end Frames

theorem xiPt_top_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG t.X.E (D.R.N (i + 1)) t.Pr.vGs × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi hlt β β' x x' p p' _hp _hp' g g' w
  have hm := m_eq t μ
  obtain rfl : i = t.m2 + 1 := by omega
  have hn1 : ¬ (t.m2 + 1 < t.m2) := by omega
  have hn2 : t.m2 + 1 ≠ t.m2 := by omega
  unfold xiPt
  rw [dif_neg hn1, if_neg hn2, dif_neg hn1, if_neg hn2, XiTop_eq, XiTop_eq]
  congr 1
  · exact phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w
  · have hX : t.X.Ok := hPin.fields.ok
    have hok := t.idx_ok μ
    have hc := hok.cst_ok
    have hrep : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q := by
      intro q
      obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
        (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ⟨y, hy⟩
    have hy0 := GlobalTheory.T.intAt_scaled_baseCosetRep_of_adTie D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β
    refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
    have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
    have hyy : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
      unfold y0At
      rw [dif_pos rfl]
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hq2 : ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∈ t.Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 :=
        fun P hP => GlobalTheory.TopStep.qOf_notMem_sq hX t.pr_ok hP
      obtain ⟨κ, hF, hκc⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p g P hP
      obtain ⟨κ', hF', hκc'⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p' g' P hP
      have hD1 : (t.cst μ).D P = 1 := hok.depthG P hP
      have hκD : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc
      have hκD' : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc'
      have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_true, pow_one] using h
      have key1 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P * κ.1 →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_true, pow_zero, inv_one, one_mul, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P * κ.1) (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) =
            κ'.1.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w ∘ₗ κ.1.toLinearMap := by
          refine LinearMap.ext fun v => ?_
          show κ'.1.symm ((frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) (κ.1 v)))))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P * κ.1).symm u1 = κ.1.symm ((frsF t.sel (t.tup μ) p P).symm (g.1.symm u1)) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hbd : ∀ z : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 ((z - A.y0 β P) l)) →
            ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * z l) := by
          intro z hz l
          have e : (qOf P.1 : t.X.E) * z l = (qOf P.1 : t.X.E) * (z - A.y0 β P) l + (qOf P.1 : t.X.E) * A.y0 β P l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact (hqI.mul (hz l)).add (hy0P l)
        have hw : (qOf P.1 : t.X.E) • κ.1.symm v1 ∈ stdAt t.X.E _ P.1 :=
          GlobalTheory.TopStep.mem_stdAt.2 fun l => by simpa using hbd _ h1 l
        have hw1 : (qOf P.1 : t.X.E) • v1 ∈ stdAt t.X.E _ P.1 := by
          have h := (κ.2 ((qOf P.1 : t.X.E) • κ.1.symm v1)).2 hw
          rwa [map_smul, LinearEquiv.apply_symm_apply] at h
        have hv1 : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * v1 l) := fun l => by
          simpa using GlobalTheory.TopStep.mem_stdAt.1 hw1 l
        rw [GlobalTheory.TwV.AwayTopG.topDat_frames_vGs A dtU a hPin hTie P hP κ.1 κ'.1 κ.2 hκD κ'.2 hκD' Yw v1 hv1]
        have hs := GlobalTheory.TwV.AwayTopG.symm_near κ.2 hκc hw1
        rw [map_smul, ← smul_sub, smul_smul, pow_one, inv_mul_cancel₀ hq0, one_smul] at hs
        have hdiff : v1 - v ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (v1 - v) l = (κ.1.symm v1 - A.y0 β P) l - (κ.1.symm v1 - v1) l - (v - A.y0 β P) l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (GlobalTheory.TopStep.intAt_sub (h1 l) (GlobalTheory.TopStep.mem_stdAt.1 hs l)) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun _ => hbd _ h2)
          (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
        exact h
      rw [hF']
      exact key1 _ _ _ hF (hrep _ P) (hrep _ P)
    · have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, if_false] using h
      have hqM : (qOf P.1 : t.X.E) ^ (t.cst μ).M ≠ 0 := pow_ne_zero _ hq0
      have key2 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, if_false, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P) (g'.1 * frsF t.sel (t.tup μ) p' P)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w := by
          refine LinearMap.ext fun v => ?_
          show (frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) v)))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P).symm u1 = (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hv : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * v l) := by
          intro l
          have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
              (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l := by
            simp only [Pi.sub_apply]
            field_simp
            ring
          rw [e]
          exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul (h2 l)).add (hy0P l)
        have hdiff : ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v) ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v)) l =
              ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v1 - A.y0 β P) l - ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l := by
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (h1 l) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun h => absurd h hP)
          (fun _ => hv) (fun h => absurd h hP) (fun _ => hdiff)
        exact h
      rw [frsF_rat_notG t.sel (t.tup μ) p' g' P hP]
      exact key2 _ _ _ (frsF_rat_notG t.sel (t.tup μ) p g P hP) (hrep _ P) (hrep _ P)

end GlobalTheory.TopRat
end
