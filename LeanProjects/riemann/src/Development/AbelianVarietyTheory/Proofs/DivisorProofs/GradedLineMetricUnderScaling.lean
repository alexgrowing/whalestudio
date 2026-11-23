import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionalQuadraticRelations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.GradedScale

open GlobalTheory.HermFrame
open scoped ComplexOrder

theorem quotGram_smul {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] {c : ℂ} (hc : c ≠ 0)
    {G : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hG : IsUnit (subGram G).det) :
    quotGram (c • G) = c • quotGram G := by
  have h₁ : IsUnit G.toBlocks₁₁.det := hG
  have e₁ : (c • G).toBlocks₁₁ = c • G.toBlocks₁₁ := rfl
  have e₂ : (c • G).toBlocks₁₂ = c • G.toBlocks₁₂ := rfl
  have e₃ : (c • G).toBlocks₂₁ = c • G.toBlocks₂₁ := rfl
  have e₄ : (c • G).toBlocks₂₂ = c • G.toBlocks₂₂ := rfl
  have e₅ : (c • G.toBlocks₁₁)⁻¹ = c⁻¹ • G.toBlocks₁₁⁻¹ :=
    Matrix.inv_eq_left_inv (by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
        Matrix.nonsing_inv_mul _ h₁])
  rw [quotGram, quotGram, e₁, e₂, e₃, e₄, e₅, smul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 2
  field_simp

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem gram_expMul {E : X.Modules} {r : ℕ} (h : Met p σ E r) (u : CxPts p σ → ℝ) {U : X.Opens}
    {ι : Type} (t : ι → Γ(E, U)) (y : CxPts p σ) :
    (h.expMul u).gram t y = (Real.exp (u y) : ℂ) • h.gram t y := by
  ext a b
  exact h.form_expMul u _ _ y

theorem restrict_expMul {E F : X.Modules} {r s : ℕ} (h : Met p σ E r) (u : CxPts p σ → ℝ)
    {i : F ⟶ E} (hi : VB.IsSubbundle i) (hF : VB.IsVB F s) :
    (h.expMul u).restrict hi hF = (h.restrict hi hF).expMul u :=
  Met.ext (funext₂ fun _ y => gram_expMul h u _ y)

theorem quot_expMul {S : ShortComplex X.Modules} {r s : ℕ} (h : Met p σ S.X₂ (r + s))
    (u : CxPts p σ → ℝ) (hS : S.ShortExact) (h₁ : VB.IsVB S.X₁ r) (h₃ : VB.IsVB S.X₃ s) :
    (h.expMul u).quot hS h₁ h₃ = (h.quot hS h₁ h₃).expMul u :=
  Met.ext_of_exists fun y => by
    obtain ⟨a, hy⟩ := Met.exists_adapted hS h₁ h₃ y
    refine ⟨a.quot, hy, ?_⟩
    rw [Met.quot_G _ hS h₁ h₃ a hy, gram_expMul, quotGram_smul (by exact_mod_cast (Real.exp_pos _).ne')
      (posDef_subGram (h.posDef_gram_frame hS a hy)).det_pos.ne'.isUnit, ← h.quot_G hS h₁ h₃ a hy]
    rfl

theorem grMet_scale {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r) (i : Fin r)
    (s : ℝ) : (h.scale s).grMet fl i = (h.grMet fl i).scale s :=
  VMetric.ext (funext fun σ =>
    (congrArg (fun m : Met p σ (VMetric.stepSeq fl i).X₂ (i + 1) =>
      m.quot (VMetric.stepSeq_shortExact fl i) (fl.isVB i.castSucc) (fl.isVB_gr i))
      (restrict_expMul (h.met σ) (fun _ => s) (fl.isSubbundle i.succ) (fl.isVB i.succ))).trans
      (quot_expMul _ _ _ _ _))

theorem grLB_scale_isometric : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (i : Fin r) (s : ℝ), (VMetric.grLB fl i (H.scale s)).Isometric ((VMetric.grLB fl i H).shift (fun _ => -s / 2) fun _ => rfl) := by
  intro k _ X p E r h H fl i s
  refine HermLB.isometric_of_eqOn fun σ c y hy => ?_
  change -Real.log (((h.grMet fl i).met σ).G c y).det.re + 2 * (-s / 2) =
    -Real.log ((((h.scale s).grMet fl i).met σ).G c y).det.re
  rw [grMet_scale]
  change _ = -Real.log ((Real.exp s : ℂ) • ((h.grMet fl i).met σ).G c y).det.re
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (by positivity) (det_re_pos (((h.grMet fl i).met σ).posDef c y hy)).ne', Real.log_pow,
    Real.log_exp]
  push_cast
  ring

end GlobalTheory.GradedScale
