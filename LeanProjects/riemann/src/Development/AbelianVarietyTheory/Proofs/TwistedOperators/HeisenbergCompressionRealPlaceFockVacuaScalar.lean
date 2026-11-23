import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkewStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCompress

open GlobalTheory.WeilVacMove

theorem gauss_ode (c : ℝ → ℂ) (a : ℂ) (h : ∀ s : ℝ, HasDerivAt c ((s : ℂ) * a * c s) s) :
    c 1 = Complex.exp (a / 2) * c 0 := by
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(a * ((t : ℂ) * (t : ℂ)) / 2)) * c t) 0 s := by
    intro s
    have e1 : HasDerivAt (fun x : ℂ => -(a * (x * x) / 2)) (-(a * (1 * (s : ℂ) + (s : ℂ) * 1) / 2)) (s : ℂ) :=
      ((((hasDerivAt_id (s : ℂ)).mul (hasDerivAt_id (s : ℂ))).const_mul a).div_const 2).neg
    have e3 := (e1.cexp.comp_ofReal).mul (h s)
    exact e3.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun s => (key s).differentiableAt) (fun s => (key s).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, zero_div, neg_zero,
    Complex.exp_zero, one_mul] at hc
  rw [← hc, ← mul_assoc, ← Complex.exp_add]
  simp

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem wAt_eq_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (w : Mx D m n) :
    wAt (.inr τ) w = lineAt θ τ (compAt θ τ w) 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  obtain ⟨-, -, -, -, hfi, -, hth⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  ext i j
  rw [← sub_eq_zero]
  apply hσ.ext
  · have h1 : finPart D (lineAt θ τ (compAt θ τ w) 1 i j) = 0 := by
      have := congrFun (congrFun (hfin 1) i) j
      simpa [Matrix.map_apply] using this
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, hfi τ, h1]
  · intro τ'
    have h2 := congrFun (congrFun (hcomp 1 τ') i) j
    by_cases hτ : τ' = τ
    · subst hτ
      rw [if_pos rfl, Complex.ofReal_one, one_smul] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ' (compAt θ τ' w) 1 i j)) = θ τ' (infPart D (w i j)) := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, (hth θ hθ τ').1, one_mul, h2']
      exact sub_self _
    · have h3 := (hth θ hθ τ').2 τ (Ne.symm hτ)
      rw [if_neg hτ] at h2
      have h2' : θ τ' (infPart D (lineAt θ τ (compAt θ τ w) 1 i j)) = 0 := h2
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.wAt, map_sub, map_mul, h3, zero_mul, zero_sub, neg_eq_zero, h2']

theorem dLine_heisO (hψ : IsStdChar D ψ (-1)) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (v : WO S T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    dLine ψ S T L (heisO ψ S T v f) x =
      -2 * phase lam S T (L 1) v * heisO ψ S T v f x + ψ (symplOH S T x v) * dLine ψ S T L f (x + v) := by
  have hG : (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) =
      fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        heisO ψ S T (L t) f (x + v) := by
    funext t
    have e1 := GlobalTheory.WeilVacMove.psi_sympl_line hl hlam hL hL0 v t
    have hX : Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) =
        (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ * (Complex.exp ((t : ℂ) * phase lam S T (L 1) v))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      ring
    have hE := Complex.exp_ne_zero ((t : ℂ) * phase lam S T (L 1) v)
    show ψ (symplOH S T x (L t)) * (ψ (symplOH S T (x + L t) v) * f (x + L t + v)) =
      ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
        (ψ (symplOH S T (x + v) (L t)) * f (x + v + L t))
    rw [GlobalTheory.WeilVacMove.symplOH_add_left, GlobalTheory.WeilVacMove.symplOH_add_left,
      GlobalTheory.WeilVacMove.symplOH_skew S T v (L t), AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_neg_eq_inv, e1, add_right_comm x (L t) v, hX]
    field_simp
  have hH := (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (x + v)
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)))
      (Complex.exp (((0 : ℝ) : ℂ) * (-2 * phase lam S T (L 1) v)) * (1 * (-2 * phase lam S T (L 1) v))) 0 :=
    (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const _).cexp).comp_ofReal
  have hD := (hexp.const_mul (ψ (symplOH S T x v))).mul hH
  show deriv (fun t : ℝ => heisO ψ S T (L t) (heisO ψ S T v f) x) 0 = _
  have hD' : HasDerivAt (fun t : ℝ => ψ (symplOH S T x v) * Complex.exp ((t : ℂ) * (-2 * phase lam S T (L 1) v)) *
      heisO ψ S T (L t) f (x + v)) _ 0 := hD
  rw [hG, hD'.deriv]
  have hv : heisO ψ S T v f x = ψ (symplOH S T x v) * f (x + v) := rfl
  rw [hv, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

private theorem flow_lemma {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (τ : D.what₂.Tau)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) (hvf : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f)
    (hvg : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g) :
    ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z 1) f) g =
      Complex.exp (-(phase lam S T (lineAt θ τ z 1) (lineAt θ τ z 1) +
        Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * z * sS)) 1) (lineAt θ τ z 1)) / 2) *
        ipO μ 𝓕 f g := by
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  set J := Complex.I • (sT * z * sS) with hJ
  obtain ⟨hLc, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨hLc', hL0', -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ J
  set L := lineAt θ τ z with hLeq
  set L' := lineAt θ τ J with hLJeq
  set Dz := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z with hDz
  set DJ := Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ J with hDJ
  have vf : Dz f + Complex.I • DJ f = 0 := hvf z
  have vg : Dz g + Complex.I • DJ g = 0 := hvg z
  have hp : ∀ (u : WO S T) (s : ℝ), phase lam S T u (L s) = (s : ℂ) * phase lam S T u (L 1) := by
    intro u s
    have hc : Continuous ((phase lam S T u).comp L) :=
      hl.comp (GlobalTheory.WeilVacMove.continuous_symplOH S T hLc continuous_const)
    exact GlobalTheory.WeilVacMove.additive_real _ hc s
  have key : ∀ s : ℝ, HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L t) f) g)
      ((s : ℂ) * -(phase lam S T (L 1) (L 1) + Complex.I * phase lam S T (L' 1) (L 1)) *
        ipO μ 𝓕 (heisO ψ S T (L s) f) g) s := by
    intro s
    set h := heisO ψ S T (L s) f with hheq
    have hh : IsThetaFunO ψ S T h := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 s) hf
    obtain ⟨hder, hXs⟩ := GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ z
    have hYs := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ h g hh hg τ J).2
    have h0 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g) (ipO μ 𝓕 (Dz h) g) (s - s) := by
      rw [sub_self]
      refine hder.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      show ipO μ 𝓕 (heisO ψ S T (L (t + s)) f) g = ipO μ 𝓕 (heisO ψ S T (L t) h) g
      rw [hheq, GlobalTheory.WeilVacMove.heisO_line_add hψ hLc hL0 t s f]
    have hd := (h0.comp_sub_const s s)
    simp only [sub_add_cancel] at hd
    refine hd.congr_deriv ?_
    have hDzh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hh
    have hDJh := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hh
    have hDJg := GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ J hg
    have cA : Dz h + Complex.I • DJ h =
        (-2 * (phase lam S T (L 1) (L s) + Complex.I * phase lam S T (L' 1) (L s))) • h := by
      funext x
      have c1 : Dz h x = -2 * phase lam S T (L 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * Dz f (x + L s) := dLine_heisO hψ hl hlam hLc hL0 (L s) hf x
      have c2 : DJ h x = -2 * phase lam S T (L' 1) (L s) * h x +
          ψ (symplOH S T x (L s)) * DJ f (x + L s) := dLine_heisO hψ hl hlam hLc' hL0' (L s) hf x
      have c3 := congrFun vf (x + L s)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at c3 ⊢
      rw [c1, c2]
      linear_combination ψ (symplOH S T x (L s)) * c3
    have e3 : ipO μ 𝓕 h (Dz g) = Complex.I * ipO μ 𝓕 h (DJ g) := by
      have hz : Dz g = (-Complex.I) • DJ g := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left vg
      rw [hz, ((U h (DJ g) hh hDJg).2.2.1 (-Complex.I)).2]
      simp [Complex.conj_I]
    have e4 : ipO μ 𝓕 (Dz h + Complex.I • DJ h) g = ipO μ 𝓕 (Dz h) g + Complex.I * ipO μ 𝓕 (DJ h) g := by
      rw [((U (Dz h) g hDzh hg).2.2.2.1 _ (GlobalTheory.WeilVacMove.isTheta_smul Complex.I hDJh)).1,
        ((U (DJ h) g hDJh hg).2.2.1 Complex.I).1]
    rw [cA, ((U h g hh hg).2.2.1 _).1, hp (L 1) s, hp (L' 1) s] at e4
    linear_combination (-1 / 2 : ℂ) * e4 + (1 / 2 : ℂ) * hXs - (Complex.I / 2) * hYs - (1 / 2 : ℂ) * e3
  have hfin := gauss_ode _ _ key
  simp only [map_zero, GlobalTheory.WeilVacMove.heisO_zero] at hfin
  exact hfin

theorem compress : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  intro D ψ θ S T μ 𝓕 hψ hθ hμ τ sS sT _ _ w
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
  refine ⟨starRingEnd ℂ (Complex.exp (-(phase lam S T (lineAt θ τ (compAt θ τ w) 1) (lineAt θ τ (compAt θ τ w) 1) +
      Complex.I * phase lam S T (lineAt θ τ (Complex.I • (sT * compAt θ τ w * sS)) 1)
        (lineAt θ τ (compAt θ τ w) 1)) / 2)), ?_⟩
  intro f g hf hg hvf hvg
  have U := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  obtain ⟨-, hL0, -⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (compAt θ τ w)
  have h1 := GlobalTheory.WeilVacMove.isTheta_heisO_real hψ (hL0 1) hf
  rw [wAt_eq_lineAt hθ τ w, (U _ g h1 hg).2.1, (U f g hf hg).2.1,
    flow_lemma hψ hθ hμ hl hlam τ sS sT (compAt θ τ w) hf hg hvf hvg, map_mul]

end GlobalTheory.VacCompress

end
