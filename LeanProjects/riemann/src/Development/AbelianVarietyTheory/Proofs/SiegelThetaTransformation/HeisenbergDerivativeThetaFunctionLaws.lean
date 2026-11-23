import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.HeisDeriv

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D}

theorem EFR_conj (C : Ctx S T) (x y : RW T S) :
    EFR C.X (fun σ k a => conj (x (C.m.e.symm σ) a k) : WR C.X S.rank) (fun σ k a => conj (y (C.m.e.symm σ) a k)) =
      -omO S T x y := by
  simp only [EFR, hermC, omO, LinearMap.mk₂_apply, formAt]
  rw [← C.m.e.sum_comp, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Equiv.symm_apply_apply, C.m.e_emb, C.m.ka, C.m.gT, C.m.gS, inv_one,
    ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply, RCLike.conj_conj]
  have hx : (-(2 * D.host.xi0 / 2)) = -D.host.xi0 := by ring
  have hone : ∀ F : Fin S.rank → Fin S.rank → ℂ,
      ∑ a, ∑ b, tauE D τ ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) a b) * F a b = ∑ a, F a a := by
    intro F; simp [Matrix.one_apply]
  rw [hx]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [hone, ← Complex.re_sum, ← Finset.mul_sum]
  have hc : conj (tauE D τ (-D.host.xi0)) *
      ∑ k, ∑ a, conj (x τ a k) * ∑ b, conj (tauE D τ (T.gram b a)) * y τ b k =
      conj (-(tauE D τ D.host.xi0 *
        ∑ k, ∑ b, conj (y τ b k) * ∑ a, tauE D τ (T.gram b a) * x τ a k)) := by
    simp only [map_neg, map_mul, map_sum, RCLike.conj_conj, neg_mul]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hc, Complex.conj_re, Complex.neg_re]
  ring

theorem pi_lineAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  obtain ⟨-, -, h⟩ := isLineAt_lineAt hθ τ z
  funext τ' i j
  have h1 := congrFun (congrFun (h 1 τ') i) j
  rw [Pi.single_apply]
  split_ifs at h1 ⊢ with hτ
  · rw [Complex.ofReal_one, one_smul] at h1
    exact h1
  · exact h1

theorem single_conj (C : Ctx S T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) =
      fun σ k a => conj (piW C.θ T S (lineAt C.θ τ z 1) (C.m.e.symm σ) a k) := by
  rw [pi_lineAt C.inf]
  funext σ k a
  simp only [Pi.single_apply, Equiv.symm_apply_eq]
  split_ifs <;> simp

theorem dRho_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ f, C.IsTh f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), C.IsTh (dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ w, HasDerivAt (fun t : ℝ => C.rho (lineAt C.θ τ z t) f w) (dRho (heisO C.ψ S T) C.θ τ z f w) 0) ∧ (∀ f', C.IsTh f' → dRho (heisO C.ψ S T) C.θ τ z (f + f') = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z f') ∧ (∀ a : ℂ, dRho (heisO C.ψ S T) C.θ τ z (a • f) = a • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ z', dRho (heisO C.ψ S T) C.θ τ (z + z') f = dRho (heisO C.ψ S T) C.θ τ z f + dRho (heisO C.ψ S T) C.θ τ z' f) ∧ (∀ t : ℝ, dRho (heisO C.ψ S T) C.θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO C.ψ S T) C.θ τ z f) ∧ (∀ u, IsFinPt u → dRho (heisO C.ψ S T) C.θ τ z (C.rho u f) = C.rho u (dRho (heisO C.ψ S T) C.θ τ z f)) ∧ ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dRho (heisO C.ψ S T) C.θ τ z (dRho (heisO C.ψ S T) C.θ τ' z' f) - dRho (heisO C.ψ S T) C.θ τ' z' (dRho (heisO C.ψ S T) C.θ τ z f) = (2 * π * I * (EFR C.X (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank) (Pi.single (C.m.e τ') (fun k a => conj (z' a k)) : WR C.X S.rank) : ℝ)) • f := by
  intro D S T C f hf τ z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  have hθ := C.inf
  have hψ := C.std
  have hD' : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ),
      dRho (heisO C.ψ S T) C.θ τ z g =
        hD (iotaW σ T S) (piW C.θ T S) (omO S T) (piW C.θ T S (lineAt C.θ τ z 1)) g := by
    intro τ z g
    rw [dRho_eq_dLine, dLine_eq_hD hσ hψ (isRealDir_lineAt hθ τ z)]
  have hsm : ∀ g, C.IsTh g → Sm (iotaW σ T S) g := fun g hg => theta_sm hσ hg
  have hform : ∀ g, C.IsTh g → ∀ (u : RW T S) (w : WO S T),
      hD (iotaW σ T S) (piW C.θ T S) (omO S T) u g w =
        -(Real.pi * Complex.I) * (omO S T (piW C.θ T S w) u : ℝ) * g w +
          fderiv ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 u :=
    fun g hg u w => hD_eq_fderiv _ _ _ g (hsm g hg) u w
  have hdiff : ∀ g, C.IsTh g → ∀ w : WO S T,
      DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun g hg w => ((hsm g hg w).differentiable (by simp)) 0
  refine ⟨theta_dRho hθ hψ τ z hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0
    rw [map_zero, heisO_zero, ← dRho_eq_dLine] at h
    exact h
  · intro f' hf'
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f' hf', hform (f + f') (theta_add hf hf')]
    rw [show (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        (fun x => f (w + iotaW σ T S x)) + (fun x => f' (w + iotaW σ T S x)) from rfl,
      fderiv_add (hdiff f hf w) (hdiff f' hf' w)]
    simp only [Pi.add_apply, _root_.add_apply]
    ring
  · intro a
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform (a • f) (theta_smul a hf)]
    rw [show (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        (fun x => a * f (w + iotaW σ T S x)) from rfl, fderiv_const_mul (hdiff f hf w)]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.smul_apply]
    ring
  · intro z'
    have hadd : piW C.θ T S (lineAt C.θ τ (z + z') 1) =
        piW C.θ T S (lineAt C.θ τ z 1) + piW C.θ T S (lineAt C.θ τ z' 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, e, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp
    funext w
    rw [hD', hD', hD', Pi.add_apply, hform f hf, hform f hf, hform f hf, hadd, map_add,
      ContinuousLinearMap.map_add]
    push_cast
    ring
  · intro t
    have hs : piW C.θ T S (lineAt C.θ τ ((t : ℂ) • z) 1) = t • piW C.θ T S (lineAt C.θ τ z 1) := by
      funext τ' i j
      have e := fun y : Matrix (Fin T.rank) (Fin S.rank) ℂ =>
        congrFun (congrFun (congrFun (pi_lineAt hθ τ y) τ') i) j
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, e, e]
      simp only [Pi.single_apply]
      split_ifs <;> simp [Complex.real_smul]
    funext w
    rw [hD', hD', Pi.smul_apply, hform f hf, hform f hf, hs, map_smul, ContinuousLinearMap.map_smul]
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · intro u hu
    exact GlobalTheory.FinTranslate.dRho_heisO hθ hu τ z f
  · intro τ' z'
    have hskew : ∀ u v : RW T S, omO S T v u = -omO S T u v := by
      intro u v
      have h := omO_self hσ (u + v)
      simp only [map_add, LinearMap.add_apply, omO_self hσ, zero_add, add_zero] at h
      linarith
    simp only [hD']
    rw [heisenberg_derivative_commutator (WO S T) (RW T S) (iotaW σ T S) (piW C.θ T S) (omO S T)
      (hσ.pi_iota T S) (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) hskew f (hsm f hf),
      single_conj C τ z, single_conj C τ' z', EFR_conj]
    congr 1
    push_cast
    ring

end GlobalTheory.Ker.HeisDeriv
