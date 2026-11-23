import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

section Analysis

variable {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))

def baseCLM : V (d + 1) →L[ℂ] V 1 :=
  (EuclideanSpace.proj (𝕜 := ℂ) (e.symm none)).smulRight (EuclideanSpace.single 0 1)

theorem baseCLM_apply (v : V (d + 1)) : baseCLM e v = base e v := by
  ext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  simp [baseCLM, base]

theorem baseCLM_single (j : Fin (d + 1)) :
    baseCLM e (EuclideanSpace.single j 1) = (baseDiag (e j) : ℂ) • EuclideanSpace.single 0 1 := by
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  rcases s with _ | s <;> simp [baseCLM, baseDiag]

theorem formMat_extTrace_base {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
    {K : V 1 → Matrix (m ⊕ l) (m ⊕ l) ℂ} {v : V (d + 1)} (h : MContDiffAt 1 K (base e v))
    (hp : ∀ᶠ x in 𝓝 (base e v), (K x).PosDef) :
    formMat (extTrace (fun x => K (base e x)) v) =
      ((Real.pi * (2 * diagVal (extTrace K (base e v)) (EuclideanSpace.single 0 1)) : ℝ) : ℂ) •
        diagonal fun j => (baseDiag (e j) : ℂ) := by
  simp only [← baseCLM_apply] at h hp ⊢
  have hs (c : ℂ) (ξ : V 1) : secondForm K (baseCLM e v) (c • ξ) = c • secondForm K (baseCLM e v) ξ := by
    rw [secondForm_eq, secondForm_eq, conn_smul_vec]; rfl
  have hn := trace_mul_adj_nonneg (posDef_subGram hp.self_of_nhds) (posDef_quotGram hp.self_of_nhds)
    (secondForm K (baseCLM e v) (EuclideanSpace.single 0 1))
  have e₁ : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have hk : kappa ≠ 0 := by
    rw [kappa]
    exact div_ne_zero Complex.I_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
  ext j l
  rw [formMat, of_apply, extTrace_comp_holo h hp (baseCLM e).contDiff.contDiffAt, ContinuousLinearMap.fderiv,
    baseCLM_single, baseCLM_single, diagVal, extTrace_eq h hp, extTrace_eq h hp, ← mul_assoc (-Complex.I), e₁,
    Complex.re_ofReal_mul, mul_div_cancel_left₀ _ hk, secondFormAdj, secondFormAdj, hs, hs]
  have e₂ (t : ℝ) : Real.pi * (2 * (1 / (2 * Real.pi) * t)) = t := by
    have := Real.pi_ne_zero
    field_simp
  rw [e₂, ← Complex.eq_re_of_ofReal_le hn]
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  obtain ⟨t, rfl⟩ := e.symm.surjective l
  rcases s with _ | s <;> rcases t with _ | t <;> simp [baseDiag, adj, diagonal_apply]

theorem bcMat_eq_of_gram {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    {S : ShortComplex X.Modules} {S' : ShortComplex Y.Modules}
    {n s : ℕ} {h : Met p σ S.X₂ (n + s)} {h' : Met q σ S'.X₂ (n + s)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ n) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ n)
    (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf) (a : AdaptedChart S n s)
    (a' : AdaptedChart S' n s) (c : AlgChart p σ 1) (c' : AlgChart q σ (d + 1)) {y : CxPts p σ}
    {z : CxPts q σ} (hy : y ∈ c.e.source) (hz : z ∈ c'.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : z ∈ ptsIn q σ a'.U) (he : base e (c'.e z) = c.e y)
    (hg : ∀ᶠ v in 𝓝 (c'.e z), h'.gram a'.frame (c'.e.symm v) = h.gram a.frame (c.e.symm (base e v))) :
    bcMat h' hS' h₁' h₃' c' z = ((Real.pi * h.bcDens hS h₁ h₃ c y : ℝ) : ℂ) •
      diagonal fun j => (baseDiag (e j) : ℂ) := by
  have hd := ((H.gram a.frame ha).mContDiffAt c hy).of_le (j := 1) (by norm_cast)
  have hp := h.eventually_posDef hS a c hy ha
  rw [← he] at hd hp
  rw [bcMat, Met.bcForm_eq (h := h') hS' a' _ c' H' hz ha' (Met.exists_adapted hS' h₁' h₃' z).choose_spec,
    Met.bcDens_eq hS h₁ h₃ a c H hy ha, Met.bcForm, Met.bcForm, extTrace_congr hg, ← he]
  have key := formMat_extTrace_base e hd hp
  exact key

end Analysis

theorem flagMat_pull_cell : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (E : B.Modules) (s : ℕ) (h : VMetric q E s), h.IsCInf → ∀ (m : Vert.Flag E s) (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)), IsCell e π w c c' → ∀ y ∈ c'.e.source, flagMat (h.pull π w) (m.pull π) σ c' y = ((Real.pi * ∑ i, ((h.stepMet m i).met σ).bcDens (VMetric.stepSeq_shortExact m i) (m.isVB i.castSucc) (m.isVB_gr i) c (PtsOver.map π w (spMap σ) y) : ℝ) : ℂ) • diagonal fun j => (baseDiag (e j) : ℂ) := by
  intro k _ B Y q p π w ι _ r d e σ E s h H m c c' hc y hy
  obtain ⟨hs, -, hb⟩ := hc
  have hy' : PtsOver.map π w (spMap σ) y ∈ c.e.source := (hs ▸ hy).1
  rw [flagMat, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨a, ha⟩ := Met.exists_adapted (VMetric.stepSeq_shortExact m i) (m.isVB i.castSucc)
    (m.isVB_gr i) (PtsOver.map π w (spMap σ) y)
  have ha' : y ∈ ptsIn p σ (π ⁻¹ᵁ a.U) := ha
  have H₁ : (h.stepMet m i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π w).stepMet (m.pull π) i).IsCInf := (H.pull π w).restrict _ _
  have hn := (ChartGlue.isOpen_over c'.e (isOpen_ptsIn (π ⁻¹ᵁ a.U))).mem_nhds (ChartGlue.mem_over c'.e hy ha')
  refine bcMat_eq_of_gram e _ _ _ _ _ _ (H₁ σ) (H₂ σ) a (VMetric.pullStep m π i a) c c' hy' hy ha ha'
    (hb y hy) ?_
  filter_upwards [hn] with v hv
  have h₁ := c'.e.map_target hv.1
  have h₂ := hb _ h₁
  rw [c'.e.right_inv hv.1] at h₂
  have h₃ : PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ c.e.source := (hs ▸ h₁).1
  rw [h₂, c.e.left_inv h₃]
  exact VMetric.gram_pullStep h w a hv.2

end GlobalTheory.MixDens
