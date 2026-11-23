import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiMLocal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasLPsM
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChain

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace CasG

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

lemma lhol_clm (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ) {G : Matrix (Fin n) (Fin n) ℂ → E}
    {z : Matrix (Fin n) (Fin n) ℂ} (hG : DifferentiableAt ℂ G z) :
    Lhol X (fun w => L (G w)) z = L (Lhol X G z) := by
  unfold Lhol
  have h1 : (fun w => L (G w)) = L ∘ G := rfl
  rw [h1]
  have h2 := (L.hasFDerivAt.comp z hG.hasFDerivAt).fderiv
  exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E' => A (X * z)) h2

lemma lhol_neg (X : Matrix (Fin n) (Fin n) ℂ) (G : Matrix (Fin n) (Fin n) ℂ → E)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol X (fun w => -G w) z = -Lhol X G z := by
  unfold Lhol
  by_cases hG : DifferentiableAt ℂ G z
  · have h2 := hG.hasFDerivAt.neg.fderiv
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ →L[ℂ] E => A (X * z)) h2
  · have h3 : ¬ DifferentiableAt ℂ (fun w => -G w) z := fun h => hG (differentiableAt_neg_iff.1 h)
    simp [fderiv_zero_of_not_differentiableAt hG, fderiv_zero_of_not_differentiableAt h3]

lemma lhol_congr (X : Matrix (Fin n) (Fin n) ℂ) {G G' : Matrix (Fin n) (Fin n) ℂ → E}
    {z : Matrix (Fin n) (Fin n) ℂ} (h : G =ᶠ[nhds z] G') : Lhol X G z = Lhol X G' z := by
  unfold Lhol
  rw [h.fderiv_eq]

lemma lhol_clm_eventually (L : E →L[ℂ] E') (X : Matrix (Fin n) (Fin n) ℂ)
    {G : Matrix (Fin n) (Fin n) ℂ → E} {V : Set (Matrix (Fin n) (Fin n) ℂ)} (hV : IsOpen V)
    (hG : DifferentiableOn ℂ G V) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ V) :
    Lhol X (fun w => L (G w)) =ᶠ[nhds z] fun w => L (Lhol X G w) := by
  filter_upwards [hV.mem_nhds hz] with w hw
  exact lhol_clm L X (hG.differentiableAt (hV.mem_nhds hw))

end CasG

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psiM_smooth (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    SmoothOnGV ε (PsiM T μ) := by
  intro g₀ hg₀
  obtain ⟨U, hUo, hpU, hd, -, -⟩ := casL_psM T μ lam hμ
  obtain ⟨W, k₀, hWo, hgW, hWU, hloc⟩ := psiM_local T μ hμ U hUo hpU hg₀
  refine ⟨W, fun g => ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) (psM T μ (g⁻¹ * toMK k₀)),
    hWo, hgW, ?_, fun g hg hgu => by rw [hloc g hg hgu]; rfl⟩
  exact contDiffOn_of_local hUo
    ((ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀)).differentiable.comp_differentiableOn hd) hWo hWU

theorem psiM_continuousOn (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ContinuousOn (PsiM T μ) {g | inUJ ε g} := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hEq⟩ := psiM_smooth T μ hμ g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine (hFc.continuousWithinAt (s := {g | inUJ ε g})).congr_of_eventuallyEq ?_ (hEq g₀ hg₀U hg₀)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgJ
  exact hEq g hgU hgJ

theorem psiM_casimir (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : casimirV ε (PsiM T μ) g = ((casVal lam : ℝ) : ℂ) • PsiM T μ g := by
  obtain ⟨U, hUo, hpU, hd, hdL, hcas⟩ := casL_psM T μ lam hμ
  obtain ⟨W, k₀, hWo, hgW, hWU, hloc⟩ := psiM_local T μ hμ U hUo hpU hg
  set Lk := ContinuousLinearMap.mul ℂ (T.V →L[ℂ] T.V) (T.op k₀) with hLk
  have hf : ∀ g' ∈ W, inUJ ε g' → PsiM T μ g' = (Lk ∘ psM T μ) (g'⁻¹ * toMK k₀) :=
    fun g' hg' hgu' => by rw [hloc g' hg' hgu']; rfl
  have hd0 : DifferentiableOn ℂ (Lk ∘ psM T μ) U := Lk.differentiable.comp_differentiableOn hd
  have hinner : ∀ a b : Fin n, ∀ g' ∈ W, inUJ ε g' →
      EabV ε b a (PsiM T μ) g' =
        (fun z => -(Lk (Lhol (Matrix.single b a 1) (psM T μ) z))) (g'⁻¹ * toMK k₀) := by
    intro a b g' hg' hgu'
    rw [eabV_of_local ε hUo hd0 hWo hWU hf b a hg' hgu']
    have hz := (hWU g' hg').2
    rw [show (⇑Lk ∘ psM T μ) = fun w => Lk (psM T μ w) from rfl,
      CasG.lhol_clm Lk (Matrix.single b a 1) (G := psM T μ) (hd.differentiableAt (hUo.mem_nhds hz))]
  have hdi : ∀ a b : Fin n,
      DifferentiableOn ℂ (fun z => -(Lk (Lhol (Matrix.single b a 1) (psM T μ) z))) U :=
    fun a b => (Lk.differentiable.comp_differentiableOn (hdL _)).neg
  have hm := (hWU g hgW).2
  have hterm : ∀ a b : Fin n, EabV ε a b (EabV ε b a (PsiM T μ)) g =
      Lk (Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (psM T μ)) (g⁻¹ * toMK k₀)) := by
    intro a b
    rw [eabV_of_local ε hUo (hdi a b) hWo hWU (hinner a b) a b hgW hg, CasG.lhol_neg, neg_neg,
      CasG.lhol_clm Lk (Matrix.single a b 1) (G := Lhol (Matrix.single b a 1) (psM T μ))
        ((hdL _).differentiableAt (hUo.mem_nhds hm))]
  unfold casimirV
  simp only [hterm]
  calc ∑ a, ∑ b, Lk (Lhol (Matrix.single a b 1) (Lhol (Matrix.single b a 1) (psM T μ)) (g⁻¹ * toMK k₀))
      = Lk (casL (psM T μ) (g⁻¹ * toMK k₀)) := by simp only [casL, map_sum]
    _ = ((casVal lam : ℝ) : ℂ) • PsiM T μ g := by
      rw [hcas _ hm, map_smul, hf g hgW hg]
      rfl

end ReciprocityTheory.ChartRestriction.DS.S7
