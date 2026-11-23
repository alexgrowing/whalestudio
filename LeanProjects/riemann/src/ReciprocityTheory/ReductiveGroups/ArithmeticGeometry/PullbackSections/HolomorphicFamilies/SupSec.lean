import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExtProof
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfRsmulRight

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec

open NumberField ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def toGT (X : PT E) : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := by
    intro x hx
    rcases X.eps_pm x hx with h | h <;> simp [h]

lemma one_col {V : Type} (w : Fin 1 → V) : (fun _ : Fin 1 => w 0) = w := by
  funext i
  rw [Subsingleton.elim i 0]

lemma sec_mem (X : PT E) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    (fun v : Vsp X.dim => s (fun _ => v)) ∈ (toGT X).Sec 1 := by
  obtain ⟨hd, hper⟩ := hs
  refine ⟨hd.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have h := hper (fun _ => γ) (fun _ => hγ) (fun _ => v)
  simp only [HC, Fin.sum_univ_one, Fin.prod_univ_one, pow_one] at h
  exact h

lemma thetaSectionPointwiseNormSq_eq (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) (w : Fin 1 → Vsp X.dim) :
    X.ptN2 1 s w = (toGT X).ptN2 1 (fun v => s (fun _ => v)) (w 0) := by
  have hw := one_col w
  have hre : (HC w w).re = ‖w 0‖ ^ 2 := by
    simp only [HC, Fin.sum_univ_one, Hf]
    rw [EuclideanSpace.norm_sq_eq, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  show ‖s w‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * (HC w w).re) =
    ‖s (fun _ => w 0)‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖w 0‖ ^ 2)
  rw [hw, hre]

lemma symmetricMeasure_l2Norm_eq_resolutionL2 (X : PT E) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    X.l2 1 s = (toGT X).l2 1 (fun v => s (fun _ => v)) := by
  have hmp := MeasureTheory.volume_preserving_funUnique (Fin 1) (Vsp X.dim)
  have hfd : X.fd 1 =
      (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim)) ⁻¹' ZSpan.fundamentalDomain X.b := by
    ext v
    show (∀ k, v k ∈ ZSpan.fundamentalDomain X.b) ↔ v default ∈ ZSpan.fundamentalDomain X.b
    exact ⟨fun h => h _, fun h k => by rwa [Subsingleton.elim k default]⟩
  have hpt : ∀ v, X.ptN2 1 s v = (toGT X).ptN2 1 (fun u => s (fun _ => u))
      (MeasurableEquiv.funUnique (Fin 1) (Vsp X.dim) v) := fun v => thetaSectionPointwiseNormSq_eq X s v
  show (⨍ v in X.fd 1, X.ptN2 1 s v) =
    ⨍ v in ZSpan.fundamentalDomain X.b, (toGT X).ptN2 1 (fun u => s (fun _ => u)) v
  simp only [hpt]
  rw [hfd, MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  erw [hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)
      ((toGT X).ptN2 1 (fun u => s (fun _ => u))) (ZSpan.fundamentalDomain X.b)]
  simp only [MeasureTheory.measureReal_def]
  erw [hmp.measure_preimage_equiv]

theorem supSec : SupSecSt := by
  unfold SupSecSt
  intro E' _ _ _ X s hs v
  have h := gSup Ext.all.1 (Idx X.dim) (toGT X) 1 le_rfl _ (sec_mem X hs) (v 0)
  have hla : (toGT X).la1 = X.la1 := rfl
  rw [thetaSectionPointwiseNormSq_eq, symmetricMeasure_l2Norm_eq_resolutionL2]
  simpa [hla] using h

end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
