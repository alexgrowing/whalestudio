import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXPS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MMatEntryMeasurable
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NChartP
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.KapEqParts
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXHU

noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

section Real

variable {r k : ℕ}

theorem reim_cont (b : Bool) : Continuous fun c : ℂ => LsNc5.reim c b := by
  cases b <;> simp only [LsNc5.reim, Bool.false_eq_true, if_false, if_true] <;>
    first | exact Complex.continuous_re | exact Complex.continuous_im | fun_prop

def idxC : WlocSk.NB.CI k r × Bool ⊕ Fin r → LsNc5.CIdx r k
  | Sum.inl (Sum.inl p, b) => Sum.inl (Sum.inl (p, b))
  | Sum.inl (Sum.inr (Sum.inl (a, j)), b) =>
      if h : j.val < k then Sum.inr (Sum.inl (a, ⟨j.val, h⟩, b)) else Sum.inl (Sum.inr (a, b))
  | Sum.inl (Sum.inr (Sum.inr p), b) => Sum.inr (Sum.inr (Sum.inl (p, b)))
  | Sum.inr a => Sum.inr (Sum.inr (Sum.inr a))

def idxC' : LsNc5.CIdx r k → WlocSk.NB.CI k r × Bool ⊕ Fin r
  | Sum.inl (Sum.inl (p, b)) => Sum.inl (Sum.inl p, b)
  | Sum.inl (Sum.inr (a, b)) => Sum.inl (Sum.inr (Sum.inl (a, Fin.last k)), b)
  | Sum.inr (Sum.inl (a, j, b)) => Sum.inl (Sum.inr (Sum.inl (a, Fin.castSucc j)), b)
  | Sum.inr (Sum.inr (Sum.inl (p, b))) => Sum.inl (Sum.inr (Sum.inr p), b)
  | Sum.inr (Sum.inr (Sum.inr a)) => Sum.inr a

def eIdx : WlocSk.NB.CI k r × Bool ⊕ Fin r ≃ LsNc5.CIdx r k where
  toFun := idxC
  invFun := idxC'
  left_inv := by
    rintro (⟨c, b⟩ | a)
    · rcases c with p | ⟨a, j⟩ | p
      · rfl
      · simp only [idxC]
        split_ifs with h
        · simp only [idxC']
          congr
        · simp only [idxC']
          congr
          all_goals exact Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      · rfl
    · rfl
  right_inv := by
    rintro ((⟨p, b⟩ | ⟨a, b⟩) | (⟨a, j, b⟩ | (⟨p, b⟩ | a)))
    · rfl
    · simp [idxC', idxC]
    · simp only [idxC', idxC, Fin.coe_castSucc, dif_pos j.isLt]
    · rfl
    · rfl

def Rc (t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) (i : LsNc5.CIdx r k) : ℝ :=
  match eIdx.symm i with
  | Sum.inl (c, b) => LsNc5.reim (t.1 c) b
  | Sum.inr a => t.2 a

theorem Rc_idx (t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) (j : WlocSk.NB.CI k r × Bool ⊕ Fin r) :
    Rc t (eIdx j) = (match j with | Sum.inl (c, b) => LsNc5.reim (t.1 c) b | Sum.inr a => t.2 a) := by
  rw [Rc, Equiv.symm_apply_apply]

theorem Rc_cont : Continuous (Rc (k := k) (r := r)) := by
  refine continuous_pi fun i => ?_
  obtain ⟨j, rfl⟩ := eIdx.surjective i
  rcases j with ⟨c, b⟩ | a
  · simp only [Rc_idx]
    exact (reim_cont b).comp ((continuous_apply c).comp continuous_fst)
  · simp only [Rc_idx]
    exact (continuous_apply a).comp continuous_snd

theorem volume_reim (P Q : Set ℝ) (hP : MeasurableSet P) (hQ : MeasurableSet Q) :
    (volume : Measure ℂ) {z | LsNc5.reim z false ∈ P ∧ LsNc5.reim z true ∈ Q} = volume P * volume Q := by
  have h : {z : ℂ | LsNc5.reim z false ∈ P ∧ LsNc5.reim z true ∈ Q} =
      Complex.measurableEquivRealProd ⁻¹' (P ×ˢ Q) := by
    ext z
    exact Iff.rfl
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]

theorem map_Rc : (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Rc = volume := by
  show Measure.map Rc (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) =
    Measure.pi fun _ => volume
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : Rc ⁻¹' Set.univ.pi s =
      (Set.univ.pi fun c => {z : ℂ | LsNc5.reim z false ∈ s (eIdx (Sum.inl (c, false))) ∧
        LsNc5.reim z true ∈ s (eIdx (Sum.inl (c, true)))}) ×ˢ
      (Set.univ.pi fun a => s (eIdx (Sum.inr a))) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨fun c => ⟨?_, ?_⟩, fun a => ?_⟩
      · simpa only [Rc_idx] using h (eIdx (Sum.inl (c, false)))
      · simpa only [Rc_idx] using h (eIdx (Sum.inl (c, true)))
      · simpa only [Rc_idx] using h (eIdx (Sum.inr a))
    · rintro ⟨h1, h2⟩ i
      obtain ⟨j, rfl⟩ := eIdx.surjective i
      rcases j with ⟨c, b⟩ | a
      · rw [Rc_idx]
        cases b
        · exact (h1 c).1
        · exact (h1 c).2
      · rw [Rc_idx]
        exact h2 a
  rw [Measure.map_apply Rc_cont.measurable (MeasurableSet.univ_pi hs), hpre, Measure.volume_eq_prod,
    Measure.prod_prod, volume_pi_pi, volume_pi_pi]
  simp only [volume_reim _ _ (hs _) (hs _)]
  conv_rhs => rw [← eIdx.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.prod_bool, Finset.prod_mul_distrib]
  ring

end Real

section Loc

variable {n r k : ℕ}

def xL (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (g : Formalism.REAL.UJ ε) : Matrix (Fin r) (Fin r) ℂ :=
  fun b a => hJ ε (f b) (uMat g *ᵥ e a)

def aL (ε : Fin n → Bool) (f : Fin r → Fin n → ℂ) (g : Formalism.REAL.UJ ε) : Matrix (Fin r) (Fin r) ℂ :=
  fun b a => hJ ε (f b) (uMat g *ᵥ f a)

def mL (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (g : Formalism.REAL.UJ ε) : Matrix (Fin r) (Fin r) ℂ :=
  (xL ε e f g)⁻¹ * aL ε f g

def kapL (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Formalism.REAL.UJ ε) : LsNc5.CIdx r k → ℝ := fun i =>
  match i with
  | Sum.inl (Sum.inl (p, t)) => LsNc5.reim (xL ε e f g p.1.1 p.1.2) t
  | Sum.inl (Sum.inr (b, t)) => LsNc5.reim (hJ ε (f b) (uMat g *ᵥ z)) t
  | Sum.inr (Sum.inl (b, j, t)) => LsNc5.reim (hJ ε (f b) (uMat g *ᵥ w j)) t
  | Sum.inr (Sum.inr (Sum.inl (p, t))) =>
      LsNc5.reim ((mL ε e f g p.1.1 p.1.2 - star (mL ε e f g p.1.2 p.1.1)) / 2) t
  | Sum.inr (Sum.inr (Sum.inr a)) => (mL ε e f g a a).im

end Loc

section Bessel

variable {r k : ℕ}

def Kc (T : ℝ) (m : Mt k r) : LsNc5.CIdx r k → ℝ := fun i =>
  match i with
  | Sum.inl (Sum.inl (p, t)) => LsNc5.reim (m (eI k r p.1.1) (eI k r p.1.2)) t
  | Sum.inl (Sum.inr (a, t)) => LsNc5.reim (((Real.sqrt T : ℝ) : ℂ) * m (eI k r a) (wI k r (Fin.last k))) t
  | Sum.inr (Sum.inl (a, j, t)) => LsNc5.reim (m (eI k r a) (wI k r (Fin.castSucc j))) t
  | Sum.inr (Sum.inr (Sum.inl (p, t))) => LsNc5.reim (WlocSk.NB.kof m p.1.1 p.1.2) t
  | Sum.inr (Sum.inr (Sum.inr a)) => (WlocSk.NB.mof m a a).im

theorem Kc_cont (T : ℝ) : Continuous (Kc (k := k) (r := r) T) := by
  refine continuous_pi fun i => ?_
  have hE : ∀ a b, Continuous fun m : Mt k r => m a b := fun a b =>
    (continuous_apply b).comp (continuous_apply a)
  have hM : ∀ a b, Continuous fun m : Mt k r => WlocSk.NB.mof m a b := by
    intro a b
    simp only [WlocSk.NB.mof, WlocSk.NB.bF, WlocSk.NB.bC, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact continuous_finset_sum _ fun c _ => ((hE _ _).star).mul (hE _ _)
  rcases i with ((⟨p, u⟩ | ⟨a, u⟩) | (⟨a, j, u⟩ | (⟨p, u⟩ | a)))
  · exact (reim_cont u).comp (hE _ _)
  · exact (reim_cont u).comp (continuous_const.mul (hE _ _))
  · exact (reim_cont u).comp (hE _ _)
  · exact (reim_cont u).comp (((hM _ _).sub (hM _ _).star).div_const 2)
  · exact Complex.continuous_im.comp (hM a a)

def dY (T : ℝ) : LsNc5.CIdx r k → ℝ
  | Sum.inl (Sum.inr _) => Real.sqrt T
  | _ => 1

theorem reim_ofReal_mul (c : ℝ) (z : ℂ) (t : Bool) : LsNc5.reim ((c : ℂ) * z) t = c * LsNc5.reim z t := by
  cases t <;> simp [LsNc5.reim]

theorem chart_kappa_coordinates (T : ℝ) (t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ)) (i : LsNc5.CIdx r k) :
    Kc T (WlocSk.NB.phi0 t.1 t.2) i = dY T i * Rc t i := by
  obtain ⟨x, s⟩ := t
  have h := WlocSk.NB.nilpotent_chart_right_inverse x s
  rcases i with ((⟨p, u⟩ | ⟨a, u⟩) | (⟨a, j, u⟩ | (⟨p, u⟩ | a))) <;>
    dsimp only [Kc, dY, Rc, eIdx, Equiv.coe_fn_symm_mk, idxC']
  · rw [one_mul, show x (Sum.inl p) = WlocSk.NB.psiC (WlocSk.NB.phi0 x s) (Sum.inl p) by rw [h.1]]
    rfl
  · rw [reim_ofReal_mul, show x (Sum.inr (Sum.inl (a, Fin.last k))) =
      WlocSk.NB.psiC (WlocSk.NB.phi0 x s) (Sum.inr (Sum.inl (a, Fin.last k))) by rw [h.1]]
    rfl
  · rw [one_mul, show x (Sum.inr (Sum.inl (a, Fin.castSucc j))) =
      WlocSk.NB.psiC (WlocSk.NB.phi0 x s) (Sum.inr (Sum.inl (a, Fin.castSucc j))) by rw [h.1]]
    rfl
  · rw [one_mul, show x (Sum.inr (Sum.inr p)) =
      WlocSk.NB.psiC (WlocSk.NB.phi0 x s) (Sum.inr (Sum.inr p)) by rw [h.1]]
    rfl
  · rw [one_mul, show s a = WlocSk.NB.psiR (WlocSk.NB.phi0 x s) a by rw [h.2]]
    rfl

instance instDecEqCIdx : DecidableEq (LsNc5.CIdx r k) := Classical.decEq _

def LyM (T : ℝ) : (LsNc5.CIdx r k → ℝ) →ₗ[ℝ] (LsNc5.CIdx r k → ℝ) := Matrix.toLin' (Matrix.diagonal (dY T))

theorem LyM_apply (T : ℝ) (v : LsNc5.CIdx r k → ℝ) (i : LsNc5.CIdx r k) : LyM T v i = dY T i * v i := by
  simp [LyM, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem det_LyM_ne {T : ℝ} (hT : 0 < T) : LinearMap.det (LyM (k := k) (r := r) T) ≠ 0 := by
  rw [LyM, LinearMap.det_toLin', Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rcases i with ((_ | _) | (_ | _)) <;> simp [dY, Real.sqrt_ne_zero', hT]

end Bessel

section LocFrame

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {w : Fin k → Fin (2 * r + k + 1) → ℂ}

theorem hJ_f_col {z0 : Fin (2 * r + k + 1) → ℂ} (g : Formalism.REAL.UJ ε) (b : Fin r) (j : Fin (2 * r + k + 1)) :
    hJ ε (f b) (uMat g *ᵥ colQ e f w z0 j) = (Qi ε e f w z0 * uMat g * Qm e f w z0) (eI k r b) j := by
  rw [(Qi_mulVec_eI (ε := ε) (e := e) (f := f) (wf := w) (z0 := z0) _ b).symm, Matrix.mulVec_mulVec]
  rfl

private theorem col_of_unipotent_entries {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h1 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), (a : ℕ) ≤ i →
      m i (eI k r a) = if i = eI k r a then 1 else 0)
    (h2 : ∀ (i j : Fin (2 * r + k + 1)), r ≤ (j : ℕ) → (j : ℕ) ≤ r + k → r ≤ (i : ℕ) →
      m i j = if i = j then 1 else 0) :
    WlocSk.UnitaryGroupBasics.col k r m := by
  unfold WlocSk.UnitaryGroupBasics.col
  intro i j hj hor
  by_cases hjr : (j : ℕ) < r
  · have he : eI k r ⟨j, hjr⟩ = j := Fin.ext rfl
    have := h1 ⟨j, hjr⟩ i (by show (j : ℕ) ≤ i; omega)
    rwa [he] at this
  · exact h2 i j (by omega) hj (by omega)

theorem kapL_eq {z : Fin (2 * r + k + 1) → ℂ} {T : ℝ} (hF : IsFrameJ ε e f w (z0v T z)) (hT : 0 < T)
    (g : Formalism.REAL.UJ ε) (hg : Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) ∈ Nset k r) :
    kapL ε e f w z g = Kc T (cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) g) := by
  dsimp only [cM]
  set M := Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) with hMdef
  have hcol : ∀ (b : Fin r) (j : Fin (2 * r + k + 1)),
      hJ ε (f b) (uMat g *ᵥ colQ e f w (z0v T z) j) = M (eI k r b) j := fun b j => hJ_f_col g b j
  have cE : ∀ a : Fin r, colQ e f w (z0v T z) (eI k r a) = e a := by
    intro a
    have hv : (eI k r a).val = a.val := rfl
    unfold colQ
    rw [dif_pos (by omega)]
    all_goals rfl
  have cF : ∀ a : Fin r, colQ e f w (z0v T z) (esI k r a) = f a := by
    intro a
    have ha := a.isLt
    have hv : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold colQ
    rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
    congr 1
    all_goals (apply Fin.ext; show 2 * r + k - (esI k r a).val = a.val; omega)
  have cW : ∀ j : Fin k, colQ e f w (z0v T z) (wI k r (Fin.castSucc j)) = w j := by
    intro j
    have hj := j.isLt
    have hv : (wI k r (Fin.castSucc j)).val = r + j.val := rfl
    unfold colQ
    rw [dif_neg (by omega), dif_pos (by omega)]
    congr 1
    all_goals (apply Fin.ext; show (wI k r (Fin.castSucc j)).val - r = j.val; omega)
  have cZ : colQ e f w (z0v T z) (wI k r (Fin.last k)) = z0v T z := by
    have hv : (wI k r (Fin.last k)).val = r + k := rfl
    unfold colQ
    rw [dif_neg (by omega), dif_neg (by omega), dif_pos hv]
  have hX : xL ε e f g = WlocSk.NB.bA M := by
    funext b a
    show hJ ε (f b) (uMat g *ᵥ e a) = M (eI k r b) (eI k r a)
    rw [← cE a]
    exact hcol b _
  have hA : aL ε f g = WlocSk.NB.bC M := by
    funext b a
    show hJ ε (f b) (uMat g *ᵥ f a) = M (eI k r b) (esI k r a)
    rw [← cF a]
    exact hcol b _
  have hg' := hg
  simp only [Nset, Set.mem_setOf_eq] at hg'
  obtain ⟨hU, h1, h2⟩ := hg'
  have hCB : WlocSk.NB.ColB M := WlocSk.NB.colB_of (col_of_unipotent_entries h1 h2)
  have hMm : mL ε e f g = WlocSk.NB.mof M := by
    rw [mL, hX, hA, Matrix.inv_eq_left_inv (WlocSk.NB.rel_F hCB hU)] <;> rfl
  have hs : ((Real.sqrt T : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
  funext i
  rcases i with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a))) <;> dsimp only [kapL, Kc]
  · rw [hX] <;> rfl
  · congr 1
    rw [← hcol, cZ]
    simp only [z0v, Matrix.mulVec_smul, hJ, dotProduct_smul, smul_eq_mul, Complex.real_smul,
      Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  · congr 1
    rw [← cW j]
    exact hcol b _
  · rw [hMm] <;> rfl
  · rw [hMm] <;> rfl

end LocFrame

theorem lebLoc {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    ∃ lam : Measure (Formalism.REAL.UJ ε), IsHaarLoc (NLoc ε e z) lam ∧ AEMeasurable (kapL ε e f w z) lam ∧
      lam.map (kapL ε e f w z) = volume := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  let ψ : Mt k r → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun x => (WlocSk.NB.psiC x, WlocSk.NB.psiR x)
  have hψc : Continuous ψ := WlocSk.NB.continuous_psiC.prodMk WlocSk.NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := fun t => by
    obtain ⟨h1, h2⟩ := WlocSk.NB.nilpotent_chart_right_inverse t.1 t.2
    show (WlocSk.NB.psiC (WlocSk.NB.phi0 t.1 t.2), WlocSk.NB.psiR (WlocSk.NB.phi0 t.1 t.2)) = t
    rw [h1, h2]
  have hΦe : MeasurableEmbedding Φ := by
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have hr : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [hr]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  set ν := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ with hν
  haveI : SigmaFinite ν := hΦe.sigmaFinite_map
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [hν, Measure.map_eq_zero_iff hΦe.measurable.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) Set.univ_nonempty
      (by rw [h0, Measure.coe_zero, Pi.zero_apply])
  have hrange : ∀ t, ∃ g : Formalism.REAL.UJ ε, Ψ g = Φ t := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  set lam0 := Measure.comap Ψ ν with hlam0
  have hmap : lam0.map Ψ = ν := by
    rw [hlam0, emb.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hν, hΦe.map_apply]
    convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨g, hg⟩ := hrange t
    exact ⟨g, hg⟩
  haveI : SigmaFinite lam0 := SigmaFinite.of_map _ emb.measurable.aemeasurable (by rw [hmap]; infer_instance)
  have hNz : NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) = NLoc ε e z := by rw [hQz]
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  have hHaar : IsHaarLoc (NLoc ε e z) lam0 := by
    refine ⟨inferInstance, fun h0 => hν0 (by rw [← hmap, h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
    · rw [hlam0, emb.comap_apply, hν, hΦe.map_apply]
      convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
      ext t
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      intro g hg hgt
      apply hg
      rw [← hNz]
      refine inN_of_conj hFJ (inWb_zB T) ?_
      have : (Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2 := hgt
      rw [this]; exact hΦN t
    · have hs' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat s) := by
        have h1 : s ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hs
        exact h1
      have h0 : Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) ∈ Nset k r :=
        conj_mem_Nset hFJ hz0 (uMat_mem s) hs'
      set m0 := Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) with hm0
      have hfun : Ψ ∘ (fun x => s * x) = lmulM m0 ∘ Ψ := by
        funext x
        show (Qi ε e f w (z0v T z) * uMat (s * x) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
          m0 * (Qi ε e f w (z0v T z) * uMat x * Qm e f w (z0v T z))
        rw [uMat_mul, hm0]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qi ε e f w (z0v T z) * uMat s) (Qm e f w (z0v T z)) (Qi ε e f w (z0v T z)),
          Qm_mul_Qi hFJ, Matrix.mul_one]
      have hsh : lmulM m0 ∘ Φ = Φ ∘ (fun t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) =>
          (t.1 + WlocSk.NB.shG m0 t.1, t.2 + WlocSk.NB.shH m0 t.1)) := by
        funext t
        obtain ⟨h1, h2⟩ := WlocSk.NB.lmul_coord h0 t.1 t.2
        have hmem := WlocSk.UnitaryGroupBasics.mem_n_mul h0 (WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2)
        show m0 * WlocSk.NB.phi0 t.1 t.2 =
          WlocSk.NB.phi0 (t.1 + WlocSk.NB.shG m0 t.1) (t.2 + WlocSk.NB.shH m0 t.1)
        rw [← h1, ← h2]
        exact (WlocSk.NB.nilpotent_chart_left_inverse hmem).symm
      have hmp := WlocSk.NB.shear_mp (d := r) WlocSk.NB.rk (WlocSk.NB.shG m0) (WlocSk.NB.shH m0)
        (fun i => (WlocSk.NB.continuous_shG m0 i).measurable) (fun i x y h => WlocSk.NB.shG_dep m0 i x y h)
        (WlocSk.NB.continuous_shH m0).measurable
      have key : (lam0.map (fun x => s * x)).map Ψ = lam0.map Ψ := by
        rw [Measure.map_map emb.measurable (measurable_const_mul s), hfun,
          ← Measure.map_map (measurable_lmulM m0) emb.measurable, hmap, hν,
          Measure.map_map (measurable_lmulM m0) hΦe.measurable, hsh,
          ← Measure.map_map hΦe.measurable hmp.measurable, hmp.map_eq]
      rw [← emb.comap_map (lam0.map (fun x => s * x)), key, emb.comap_map]
  have hkc : ∀ᵐ g ∂lam0, kapL ε e f w z g = (Kc T ∘ Ψ) g := by
    filter_upwards [(ae_iff.2 hHaar.2.2.1 : ∀ᵐ g ∂lam0, g ∈ NLoc ε e z)] with g hg
    have hg' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat g) := by
      have h1 : g ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hg
      exact h1
    exact kapL_eq hFJ hT g (conj_mem_Nset hFJ hz0 (uMat_mem g) hg')
  have hdet := det_LyM_ne (k := k) (r := r) hT
  set c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (LyM (k := k) (r := r) T))⁻¹| with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasK : AEMeasurable (kapL ε e f w z) lam0 :=
    ((Kc_cont T).measurable.comp emb.measurable).aemeasurable.congr (Filter.EventuallyEq.symm hkc)
  refine ⟨c⁻¹ • lam0, isHaarLoc_smul hHaar (ENNReal.inv_ne_zero.2 hcT) (ENNReal.inv_ne_top.2 hc0),
    hmeasK.smul_measure _, ?_⟩
  have hcomp : Kc T ∘ Φ = LyM (k := k) (r := r) T ∘ Rc := by
    funext t
    funext i
    rw [Function.comp_apply, Function.comp_apply, LyM_apply]
    exact chart_kappa_coordinates T t i
  rw [Measure.map_smul, Measure.map_congr hkc, ← Measure.map_map (Kc_cont T).measurable emb.measurable, hmap, hν,
    Measure.map_map (Kc_cont T).measurable hΦe.measurable, hcomp,
    ← Measure.map_map (LyM (k := k) (r := r) T).continuous_of_finiteDimensional.measurable Rc_cont.measurable,
    map_Rc, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, ← hc, smul_smul, ENNReal.inv_mul_cancel hc0 hcT,
    one_smul]

theorem map_uncurry_volume {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (Measure.pi fun _ : ι => (volume : Measure (κ → ℝ))).map
      (fun F : ι → κ → ℝ => fun p : ι × κ => F p.1 p.2) = volume := by
  have hm : Measurable (fun F : ι → κ → ℝ => fun p : ι × κ => F p.1 p.2) :=
    measurable_pi_lambda _ fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  show _ = Measure.pi fun _ : ι × κ => (volume : Measure ℝ)
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hpre : (fun F : ι → κ → ℝ => fun p : ι × κ => F p.1 p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i => Set.univ.pi fun j => s (i, j) := by
    ext F
    simp [Set.mem_univ_pi, Prod.forall]
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi, Fintype.prod_prod_type]
  simp only [volume_pi_pi]

section Glob

variable {D : D7} (X : HidaSetting D)

theorem kapV_eq (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (s : X.B.I.Ginf) :
    (fun i => LsNc5.kapV X u v s i) =
      kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v) := by
  funext i
  rcases i with ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a))) <;> rfl

end Glob

theorem lebHaar_holds : LsNc5.LebHaar := by
  intro D X u
  have hloc := fun v : InfinitePlace X.B.I.F => lebLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
    (ProductExactness.zV X u v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v) (fX_ww X u v) (fX_ew X u v)
    (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v)
  choose lam hH hM hmap using hloc
  haveI : ∀ v, SigmaFinite (lam v) := fun v => (hH v).1
  have hco : X.NinfU u = (ProductExactness.NinfG X u : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X u).symm
  refine ⟨Measure.pi lam, ⟨inferInstance, ProductExactness.PiM.pi_ne_zero _ fun v => (hH v).2.1, ?_, ?_⟩, ?_⟩
  · rw [hco, ProductExactness.NinfG, Subgroup.coe_pi]
    exact ProductExactness.PiM.pi_conc _ _ fun v => (hH v).2.2.1
  · intro g hg
    rw [hco] at hg
    exact ProductExactness.PiM.pi_map_mul_left _ g fun v => (hH v).2.2.2 (g v) (hg v (Set.mem_univ v))
  · have hK' : (fun (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) =>
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) =
        (MeasurableEquiv.curry (InfinitePlace X.B.I.F) (LsNc5.CIdx D.R.rS D.R.k) ℝ) ∘ LsNc5.kap X u := by
      funext s v i
      exact (congrFun (kapV_eq X u v s) i).symm
    have hK'm : Measurable (fun (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) =>
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) := by
      rw [hK']
      exact (MeasurableEquiv.curry _ _ ℝ).measurable.comp (LsNc5.kap_measurable X u)
    have hkap : LsNc5.kap X u = (fun F : InfinitePlace X.B.I.F → LsNc5.CIdx D.R.rS D.R.k → ℝ =>
        fun p : InfinitePlace X.B.I.F × LsNc5.CIdx D.R.rS D.R.k => F p.1 p.2) ∘ (fun (s : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) =>
          kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) := by
      funext s p
      exact congrFun (kapV_eq X u p.1 s) p.2
    have hunc : Measurable (fun F : InfinitePlace X.B.I.F → LsNc5.CIdx D.R.rS D.R.k → ℝ =>
        fun p : InfinitePlace X.B.I.F × LsNc5.CIdx D.R.rS D.R.k => F p.1 p.2) :=
      measurable_pi_lambda _ fun p : InfinitePlace X.B.I.F × LsNc5.CIdx D.R.rS D.R.k =>
        (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
    haveI : ∀ v, SigmaFinite ((lam v).map
        (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v))) := fun v => by
      rw [hmap v]; infer_instance
    rw [hkap, ← Measure.map_map hunc hK'm, Measure.pi_map_pi (fun v => hM v)]
    simp_rw [hmap]
    exact map_uncurry_volume

theorem covolN_of_coordCovol (hC : LsNc5.CoordCovol) : LsNc5.CovolN := by
  exact LsNc5.covolN_of_four LsNc5.kapInj haarUnique_holds lebHaar_holds hC

end Formalism.L2.SG.Pf.NcReal.JX
