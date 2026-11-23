import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.HeisRead

variable {D : D7}

open GlobalTheory.FockCompare in

theorem realPt_eq_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (Z : RW T S) :
    realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => Z τ i j) = iotaW σ T S Z := by
  have hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of fun i j => Z τ i j :=
    ⟨iotaW σ T S Z, hσ.real_iota T S Z, fun τ => congrFun (hσ.pi_iota T S Z) τ⟩
  have hs := Classical.epsilon_spec hex
  exact hσ.real_ext hs.1 (hσ.real_iota T S Z) (funext fun τ => (hs.2 τ).trans (congrFun (hσ.pi_iota T S Z) τ).symm)

theorem embH_toHom_apply (S T : HSp D) (δ : ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau)
    (i : Fin T.rank) (j : Fin S.rank) :
    embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) := by
  simp [embH, toHom, Matrix.toLin'_apply]

end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead

theorem term_eq (k sc : ℝ) (δ w g : ℂ) (hδ : δ ≠ 0) (hsc : sc * ‖δ‖ ^ 2 = 2 * k) :
    2 * (Complex.I * (k : ℂ) * ((starRingEnd ℂ) g * -(δ⁻¹ * w))).re = ((sc : ℂ) * (w * (starRingEnd ℂ) (δ * g))).im := by
  have hn : Complex.normSq δ ≠ 0 := Complex.normSq_pos.2 hδ |>.ne'
  have hsc' : sc = 2 * k / Complex.normSq δ := by
    rw [Complex.normSq_eq_norm_sq, eq_div_iff (by rwa [← Complex.normSq_eq_norm_sq]), hsc]
  subst hsc'
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  rw [Complex.normSq_apply] at hn ⊢
  field_simp
  ring
end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead
variable {D : D7}

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = starRingEnd ℂ (HV sc z w) := by
  simp only [HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

open GlobalTheory.OrientedHeis in

theorem omO_eq_im (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hP : StdPair θ S T δ sc ψ)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : VCx D.what₂.Tau S.rank T.rank) :
    omO S T (fun τ i j => -(δ⁻¹ * z τ i j)) (fun τ i j => tauE D τ (γ i j)) =
      (HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im := by
  simp only [omO, LinearMap.mk₂_apply, HV, LinearMap.mk₂'ₛₗ_apply, embH_toHom_apply, formAt, hP.gS, hP.gT, inv_one,
    Matrix.one_apply, apply_ite (tauE D _), map_one, map_zero, hP.xi]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hin : ∀ τ (x1 : Fin S.rank), (∑ x2 : Fin S.rank, ∑ x3 : Fin T.rank, if x1 = x2 then (starRingEnd ℂ) ((tauE D τ) (γ x3 x2)) * -(δ⁻¹ * z τ x3 x1) else 0) =
      ∑ x3 : Fin T.rank, (starRingEnd ℂ) ((tauE D τ) (γ x3 x1)) * -(δ⁻¹ * z τ x3 x1) := fun τ x1 => by
    rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hin]
  rw [Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term_eq _ sc δ _ _ hP.ne hP.scale
end GlobalTheory.AdForm.HeisRead
namespace GlobalTheory.AdForm.HeisRead

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis in

theorem xiN_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  intro D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  funext z
  let G : RW T S := fun τ i j => tauE D τ (γ i j)
  let Z : RW T S := fun τ i j => -(δ⁻¹ * z τ i j)
  have hrat : ratW T S γ = v + iotaW σ T S G := by
    have h1 : ratW T S γ - v = iotaW σ T S G := by
      refine hσ.real_ext (x := ratW T S γ - v) ?_ (hσ.real_iota _ _ _) ?_
      · show (ratW T S γ - v).map (finPart D) = 0
        rw [Matrix.map_sub _ (finPart D).map_sub, hv.2, sub_self]
      · rw [hσ.pi_iota, map_sub]
        funext τ i j
        have h0 : piW θ T S v τ i j = 0 := by
          show θ τ (infPart D (v i j)) = 0
          rw [show infPart D (v i j) = 0 from congrFun (congrFun hv.1 i) j, map_zero]
        show θ τ (infPart D (incA D (γ i j))) - piW θ T S v τ i j = _
        rw [h0, sub_zero, comp_incA hP.inf]
    rw [← h1]; abel
  have hX : ∀ τ i j, embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) :=
    GlobalTheory.AdForm.HeisRead.embH_toHom_apply S T δ γ
  have hp : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S Z := by
    simpa using GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T Z
  have hp' : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * (z + embH (tauE D) δ (toHom S T rfl rfl γ)) τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S (Z - G) := by
    rw [← GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T (Z - G)]
    congr 1
    funext τ i j
    simp only [Fin.cast_eq_self, Pi.add_apply, hX, Matrix.of_apply, Pi.sub_apply, Z, G]
    field_simp [hP.ne]
    ring
  unfold xiN Formalism.L2.Th1.H.opU heisO
  beta_reduce
  rw [hp, hp']
  have e0 : symplOH S T (iotaW σ T S Z) v = 0 := GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _)
  have e1 : iotaW σ T S Z + v = ratW T S γ + iotaW σ T S (Z - G) := by rw [hrat, map_sub]; abel
  have e2 : f (ratW T S γ + iotaW σ T S (Z - G)) = ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) * f (iotaW σ T S (Z - G)) := by
    rw [hf.quasi, ← GlobalTheory.FinTranslate.symplOH_skew, hrat, symplOH_add_right,
      GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _), zero_add]
  have e3 : ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) =
      Complex.exp (-(Real.pi * Complex.I) * ((HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im : ℂ)) := by
    rw [psi_symplOH hσ hP.std, hσ.pi_iota, LinearMap.map_sub₂, omO_self hσ, sub_zero]
    exact congrArg (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (t : ℂ)))
      (GlobalTheory.AdForm.HeisRead.omO_eq_im θ ψ S T δ sc hP γ z)
  rw [e0, AddChar.map_zero_eq_one, one_mul, e1, e2, e3]
  set X := embH (tauE D) δ (toHom S T rfl rfl γ)
  have hadd : HV sc (z + X) (z + X) = HV sc z z + HV sc z X + HV sc X z + HV sc X X := by
    simp only [map_add, LinearMap.add_apply]; ring
  have hc : HV sc X z = starRingEnd ℂ (HV sc z X) := GlobalTheory.AdForm.HeisRead.HV_conj sc z X
  have hcj : starRingEnd ℂ (HV sc z X) = HV sc z X - 2 * Complex.I * ((HV sc z X).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [← mul_assoc, ← Complex.exp_add, mul_right_comm, ← Complex.exp_add]
  congr 2
  rw [hadd, hc, hcj]
  ring

end GlobalTheory.AdForm.HeisRead
