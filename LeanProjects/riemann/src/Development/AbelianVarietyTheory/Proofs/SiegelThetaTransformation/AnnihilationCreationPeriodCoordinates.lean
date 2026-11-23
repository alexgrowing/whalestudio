import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPeriodMapHomeomorphRiemannFormDensity
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticCharacterRealFinitePointsMatchStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [hx, Matrix.mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [hx, Matrix.mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem hx_smul_right (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x z (c • w) = conj c * hx X bas idx x z w := by
  simp only [hx, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_eq_mul, Complex.star_def]

theorem hx_rsmul_left (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x (t • z) w = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_left]

theorem hx_rsmul_right (t : ℝ) (z w : Fin g → ℂ) :
    hx X bas idx x z (t • w) = t * hx X bas idx x z w := by
  rw [← Complex.coe_smul, hx_smul_right, Complex.conj_ofReal]

theorem hasDerivAt_translate (hs : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (Φ : (Fin n → Fin g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ) (ζ u : Fin n → Fin g → ℂ) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ)) *
      (gaussR X bas idx x (ζ + t • u) * Φ (ζ + t • u)))
      (gaussR X bas idx x ζ * (-(π * ∑ k, hx X bas idx x (u k) (ζ k)) * Φ ζ + fderiv ℝ Φ ζ u)) 0 := by
  have hab : ∑ k, hx X bas idx x (ζ k) (u k) = conj (∑ k, hx X bas idx x (u k) (ζ k)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hs (u k) (ζ k)
  have hph : ∀ t : ℝ, (((∑ k, hx X bas idx x (ζ k) ((t • u) k)).im : ℝ) : ℂ) =
      (t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) := by
    intro t
    have h : ∑ k, hx X bas idx x (ζ k) ((t • u) k) = (t : ℂ) * ∑ k, hx X bas idx x (ζ k) (u k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, hx_rsmul_right]
    rw [h, Complex.im_ofReal_mul, Complex.ofReal_mul]
  have hq : ∀ t : ℝ, ∑ k, hx X bas idx x ((ζ + t • u) k) ((ζ + t • u) k) =
      ∑ k, hx X bas idx x (ζ k) (ζ k) +
        (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
        (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k) := by
    intro t
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, hx_add_left, hx_add_right, hx_rsmul_left, hx_rsmul_right]
    ring
  have hT : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hE : HasDerivAt (fun t : ℝ => (Real.pi : ℂ) * I * ((t : ℂ) * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (ζ k) +
          (t : ℂ) * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) +
          (t : ℂ) ^ 2 * ∑ k, hx X bas idx x (u k) (u k)))
      ((Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))) 0 := by
    have h := ((hT.mul_const (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ)).const_mul ((Real.pi : ℂ) * I)).sub
      ((((hT.mul_const (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k))).const_add
        (∑ k, hx X bas idx x (ζ k) (ζ k))).add ((hT.pow 2).mul_const (∑ k, hx X bas idx x (u k) (u k)))).const_mul
          ((Real.pi : ℂ) / 2))
    exact h.congr_deriv (by simp)
  have hL : HasDerivAt (fun t : ℝ => ζ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add ζ
  have hΦt : HasDerivAt (fun t : ℝ => Φ (ζ + t • u)) (fderiv ℝ Φ ζ u) 0 :=
    (hΦ ζ).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hL (by simp)
  have hF := hE.cexp.mul hΦt
  refine (hF.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · have key : (Real.pi : ℂ) * I * (((∑ k, hx X bas idx x (ζ k) (u k)).im : ℝ) : ℂ) -
        (Real.pi : ℂ) / 2 * (∑ k, hx X bas idx x (ζ k) (u k) + ∑ k, hx X bas idx x (u k) (ζ k)) =
        -((Real.pi : ℂ) * ∑ k, hx X bas idx x (u k) (ζ k)) := by
      rw [hab]
      generalize ∑ k, hx X bas idx x (u k) (ζ k) = b
      have e1 : conj b = (b.re : ℂ) - (b.im : ℂ) * I := by apply Complex.ext <;> simp
      have e2 : b = (b.re : ℂ) + (b.im : ℂ) * I := (Complex.re_add_im b).symm
      rw [Complex.conj_im, e1]
      push_cast
      linear_combination ((Real.pi : ℂ) / 2) * e2
    rw [key]
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, add_zero, zero_smul, zero_sub,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    unfold GlobalTheory.Ker.gaussR
    ring
  · beta_reduce
    rw [hph t]
    unfold GlobalTheory.Ker.gaussR
    rw [hq t, ← mul_assoc, ← Complex.exp_add]
    congr 2

end Classical

variable {D : D7} {S T : HSp D}

theorem dRho_eq (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (G : WO S T → ℂ)
    (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ) (hΦ : Differentiable ℝ Φ)
    (hG : ∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ)
    (hu : u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))
    (w : WO S T) (hw : IsRealPt w) :
    Formalism.IndefR.Datum.dRho (heisO C.ψ S T) C.θ τ z G w =
      gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) *
        (-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w) +
          fderiv ℝ Φ (C.zOf (C.xB B) w) u) := by
  obtain ⟨R, -, -, -, hR1, hR2, -, -, hline, -⟩ := GlobalTheory.T.realPoints_classicalModel_realVectorSpace D S T C
  have hdom : C.xB B ∈ C.X.dom := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hs := (GlobalTheory.Dict.hx_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).1
  have hE := (zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (C.xB B) hdom).2.1
  have hψ := (GlobalTheory.T.symplecticCharacter_real_finite_points_match D S T C).2.1
  have hlin : ∀ (a : WR C.X S.rank) (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (a + t • b) = zR C.X C.idx (C.xB B) a + t • zR C.X C.idx (C.xB B) b := by
    intro a t b
    have h := (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_add a (t • b)
    rw [map_smul] at h
    exact h
  have hsm : ∀ (t : ℝ) (b : WR C.X S.rank),
      zR C.X C.idx (C.xB B) (t • b) = t • zR C.X C.idx (C.xB B) b := fun t b =>
    (zRLin C.X C.idx (C.xB B) (n := S.rank)).map_smul t b
  have hT := hasDerivAt_translate C.X C.bas C.idx (C.xB B) hs Φ hΦ (C.zOf (C.xB B) w) u
  unfold Formalism.IndefR.Datum.dRho heisO
  refine (hT.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).deriv
  beta_reduce
  have hw' : w + lineAt C.θ τ z t =
      R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank)) := by
    rw [hline, map_add, hR2 w hw]
  have hz : C.zOf (C.xB B)
      (R (C.realPt w + t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) =
      C.zOf (C.xB B) w + t • u := by
    unfold Ctx.zOf
    rw [(hR1 _).2, hlin, hu]
  rw [hw', hG _ (hR1 _).1, hz, hline, hψ w _ hw (hR1 _).1, (hR1 _).2, ← hE, hsm, ← hu]
  rfl

end GlobalTheory.Ker.HeisDeriv

theorem GlobalTheory.Ker.annih_crea_coord : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (Φ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℝ Φ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * Φ (C.zOf (C.xB B) w)) → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Fin S.rank → Fin C.g → ℂ), u = zR C.X C.idx (C.xB B) (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) → ∀ w, IsRealPt w → annih (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u + I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)) ∧ crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (2 * ((-(π * ∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k))) * Φ (C.zOf (C.xB B) w) + (1 / 2 : ℂ) * (fderiv ℝ Φ (C.zOf (C.xB B) w) u - I * fderiv ℝ Φ (C.zOf (C.xB B) w) (I • u)))) := by
  intro D S T C B hB G Φ hΦ hG τ z u hu w hw
  have h1 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ z u hu w hw
  have hJ : I • u = zR C.X C.idx (C.xB B)
      (Pi.single (C.m.e τ) (fun k a => conj ((cplxO 1 (C.sB B τ) z) a k)) : WR C.X S.rank) := by
    rw [hu]
    exact (((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.1 τ z).symm
  have h2 := GlobalTheory.Ker.HeisDeriv.dRho_eq C B hB G Φ hΦ hG τ (cplxO 1 (C.sB B τ) z) (I • u) hJ w hw
  simp only [Pi.smul_apply, GlobalTheory.Ker.HeisDeriv.hx_smul_left, ← Finset.mul_sum] at h2
  unfold Formalism.IndefR.Datum.annih Formalism.IndefR.Datum.crea
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  constructor
  · linear_combination (-(gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w))) * I_sq
  · linear_combination (gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * (Real.pi : ℂ) *
      (∑ k, hx C.X C.bas C.idx (C.xB B) (u k) (C.zOf (C.xB B) w k)) * Φ (C.zOf (C.xB B) w)) * I_sq
