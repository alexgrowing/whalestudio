import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.FockKill

open GlobalTheory.FockIndep GlobalTheory.OrientedHeis
open scoped Real Classical

section Generic

variable {ι X : Type} [Fintype ι] {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem quad_pure {B : ι → (X → ℂ) → (X → ℂ)} {G : Module.End ℂ (X → ℂ)} {μ : ι → ι → ℂ}
    (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f))
    (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (Badd : ∀ i f f', P f → P f' → B i (f + f') = B i f + B i f')
    (Bsm : ∀ i (a : ℂ) f, P f → B i (a • f) = a • B i f)
    (hBA : ∀ i j f, P f → B i (A j f) = A j (B i f) + (μ i j + μ j i) • f)
    (hGA : ∀ i f, P f → G (A i f) = A i (G f) + B i f)
    {f : X → ℂ} (hf : P f) (hv : ∀ i, B i f = 0) (hGf : G f = 0) (Q : MvPolynomial ι ℂ) :
    G (pureTensorL A f Q) =
      pureTensorL A f (∑ i, ∑ j, μ i j • MvPolynomial.pderiv i (MvPolynomial.pderiv j Q)) := by
  have hC : ∀ a, pureTensorL A f (MvPolynomial.C a) = a • f := fun a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, pure_one]
  have hm := pure_mem hadd hsm hA hf
  have hX := pure_X_mul hadd hsm hA hc Aadd Asm hf
  have hd : ∀ (i j : ι) (Q : MvPolynomial ι ℂ), MvPolynomial.pderiv i (MvPolynomial.X j * Q) =
      MvPolynomial.X j * MvPolynomial.pderiv i Q + (if i = j then Q else 0) := fun i j Q => by
    rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, add_comm]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  have key : ∀ i Q, B i (pureTensorL A f Q) =
      pureTensorL A f (∑ j, (μ i j + μ j i) • MvPolynomial.pderiv j Q) := by
    intro i Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp [hC, Bsm _ _ _ hf, hv]
    | add p q hp hq =>
      rw [map_add, Badd _ _ _ (hm _) (hm _), hp, hq, ← map_add, ← Finset.sum_add_distrib]
      simp only [map_add, smul_add]
    | mul_X p j hp =>
      rw [mul_comm, hX, hBA _ _ _ (hm _), hp, ← hX, ← map_smul, ← map_add]
      congr 1
      simp only [hd, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm, smul_ite, smul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  induction Q using MvPolynomial.induction_on with
  | C a => simp [hC, hGf]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, ← map_add, ← Finset.sum_add_distrib]
    simp only [map_add, smul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [mul_comm, hX, hGA _ _ (hm _), hp, key, ← hX, ← map_add]
    congr 1
    simp only [hd, map_add, apply_ite (MvPolynomial.pderiv _), map_zero, smul_add, add_smul, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, add_assoc]
    congr 2
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Generic

section Mat

variable {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {H s B' W : Matrix (Fin m) (Fin m) ℂ} {δ : Fin m → ℂ}

theorem trace_unitMap (hB : Bᴴ * G * B = 1) (H W B' : Matrix (Fin m) (Fin m) ℂ) (a c : Fin m) (b d : Fin n) :
    (G⁻¹ * (unitMap B B' c d)ᴴ * H * (W * unitMap B B' a b)).trace =
      if b = d then (B'ᴴ * H * W * B') c a else 0 := by
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hG : G⁻¹ = B * Bᴴ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc]
    exact mul_eq_one_comm.1 (by rw [← Matrix.mul_assoc, hB])
  have h1 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, Matrix.nonsing_inv_mul _ hu, conjTranspose_one]
  have e : G⁻¹ * (unitMap B B' c d)ᴴ * H * (W * unitMap B B' a b) =
      B * ((Bᴴ * (B⁻¹)ᴴ) * (Matrix.single c d (1 : ℂ))ᴴ * (B'ᴴ * H * W * B') * Matrix.single a b (1 : ℂ) * B⁻¹) := by
    simp only [hG, unitMap, conjTranspose_mul, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.nonsing_inv_mul_cancel_right _ _ hu, h1, Matrix.one_mul,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single]
  by_cases h' : b = d
  · subst h'; simp
  · simp [Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm h'), h']

theorem skew_entry (hH : Hᴴ = H) (hW : Wᴴ * H + H * W = 0) {ξ : ℂ} (hξ : ξ.re = 0) (a b : Fin m) :
    (ξ * (B'ᴴ * H * W * B') a b).re = (ξ * (B'ᴴ * H * W * B') b a).re := by
  have e : (B'ᴴ * H * W * B')ᴴ = -(B'ᴴ * H * W * B') := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
      ← Matrix.mul_assoc Wᴴ, eq_neg_of_add_eq_zero_left hW]
    simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  have e' := congrArg Complex.im (congrFun (congrFun e a) b)
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.neg_im, Complex.star_def, Complex.conj_im, neg_inj] at e'
  rw [Complex.mul_re, Complex.mul_re, hξ, e', zero_mul, zero_mul]

theorem herm_cartan (hs : IsCartanInv H s) : sᴴ * H = H * s := by
  calc sᴴ * H = sᴴ * H * s * s := by rw [Matrix.mul_assoc _ s, hs.1, Matrix.mul_one]
    _ = _ := by rw [hs.2.1]

theorem zero_entry (hs : IsCartanInv H s) (hB : s * B' = B' * diagonal δ) (hW : s * W = -(W * s)) {a b : Fin m}
    (ha : star (δ a) + δ b ≠ 0) : (B'ᴴ * H * W * B') a b = 0 := by
  have e : (diagonal δ)ᴴ * (B'ᴴ * H * W * B') = -(B'ᴴ * H * W * B' * diagonal δ) := by
    calc _ = (B' * diagonal δ)ᴴ * H * W * B' := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * H * (s * W) * B' := by
        rw [← hB, conjTranspose_mul, Matrix.mul_assoc _ _ H, herm_cartan hs]; simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hW, Matrix.mul_assoc _ B', ← hB]; simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
  have e' := congrFun (congrFun e a) b
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal, Pi.star_apply] at e'
  refine (mul_eq_zero.1 ?_).resolve_left ha
  linear_combination e'

theorem conj_exp (hs : s * s = 1) (hW : s * W = -(W * s)) (t : ℝ) :
    s * NormedSpace.exp (t • W) = NormedSpace.exp ((-t) • W) * s := by
  have hi : s⁻¹ = s := Matrix.inv_eq_left_inv hs
  have e : (-t) • W = s * (t • W) * s⁻¹ := by
    rw [hi, Matrix.mul_smul, Matrix.smul_mul, hW, Matrix.neg_mul, Matrix.mul_assoc, hs, Matrix.mul_one, smul_neg,
      neg_smul]
  rw [e, Matrix.exp_conj _ _ (IsUnit.of_mul_eq_one _ hs), hi, Matrix.mul_assoc _ s, hs, Matrix.mul_one]

theorem parts (hH : IsUnit H.det) (hs : IsCartanInv H s) {Z : Matrix (Fin m) (Fin m) ℂ} (h1 : s * Z = -Z)
    (h2 : Z * s = Z) :
    s * ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H))) = -((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H)) * s) ∧
    (1 / (2 * Complex.I)) • (Z - -(H⁻¹ * Zᴴ * H)) =
      Complex.I • (s * ((1 / 2 : ℂ) • (Z + -(H⁻¹ * Zᴴ * H)))) := by
  have e := herm_cartan hs
  have e' : s * H⁻¹ = H⁻¹ * sᴴ := by
    calc s * H⁻¹ = H⁻¹ * (H * s) * H⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hH]
      _ = _ := by rw [← e, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hH]
  have a1 : s * (H⁻¹ * Zᴴ * H) = H⁻¹ * Zᴴ * H := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e', Matrix.mul_assoc _ sᴴ, ← conjTranspose_mul, h2]
  have a2 : H⁻¹ * Zᴴ * H * s = -(H⁻¹ * Zᴴ * H) := by
    rw [Matrix.mul_assoc _ H, ← e, ← Matrix.mul_assoc, Matrix.mul_assoc _ Zᴴ, ← conjTranspose_mul, h1,
      conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]
  generalize H⁻¹ * Zᴴ * H = Y at a1 a2
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
    a1, a2, h1, h2]
  refine ⟨by module, ?_⟩
  have : (1 / (2 * Complex.I) : ℂ) = -(Complex.I / 2) := by field_simp; simp
  rw [this]
  module

theorem isCartanInv_one (h : Bᴴ * G * B = 1) : IsCartanInv G 1 := by
  have hB : B * (Bᴴ * G) = 1 := mul_eq_one_comm.1 h
  have hi : B⁻¹ = Bᴴ * G := Matrix.inv_eq_right_inv hB
  have hu : IsUnit B := IsUnit.of_mul_eq_one _ hB
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    have h1 : (B⁻¹)ᴴ * Bᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hi, hB, Matrix.conjTranspose_one]
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G := by rw [h1, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, ← hi]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  refine Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit ?_)
  exact (Matrix.isUnit_nonsing_inv_iff).2 hu

end Mat

section Weil

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}

def IsGen (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D)
    (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin T.rank) ℂ) (Gn : Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧
    (∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ u f) - Datum.dRho (heisO ψ S T) θ τ u (Gn f) =
      Datum.dRho (heisO ψ S T) θ τ (X * u) f) ∧
    (∀ τ', τ' ≠ τ → ∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ' u f) = Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧
    ∀ (p : GA D S × GA D T) (w : WO S T),
      HasDerivAt (fun t : ℝ => om (p * (1, oneP θ T τ X t)) f w) (om p (Gn f) w) 0

variable {s X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}

theorem gen_anti (hθ : IsInfFam θ) (hs : IsCartanInv (gramAt D T τ) s) (hX : X ∈ lieAt T τ) (ha : s * X = -(X * s))
    (hG : IsGen ψ om θ τ X GX) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {c : ℂ}
    (hc : om (1, atTau θ T τ s) f = c • f) : om (1, atTau θ T τ s) (GX f) = -(c • GX f) := by
  funext w
  have d1 := (hG f hf).2.2.2 (1, atTau θ T τ s) w
  have d0 := (hG f hf).2.2.2 1 w
  have d2 := (HasDerivAt.comp_const_sub (0 : ℝ) 0 (by rw [sub_self]; exact d0)).const_mul c
  have hm := GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) hX
  have e : (fun t : ℝ => om ((1, atTau θ T τ s) * (1, oneP θ T τ X t)) f w) =
      fun t : ℝ => c * om (1 * (1, oneP θ T τ X (0 - t))) f w := by
    funext t
    have : (((1 : GA D S), atTau θ T τ s) * (1, oneP θ T τ X t)) =
        (1, oneP θ T τ X (0 - t)) * (1, atTau θ T τ s) := by
      rw [Prod.mk_mul_mk, Prod.mk_mul_mk, oneP, oneP, ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hs.2.1 (hm _),
        ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ (hm _) hs.2.1, conj_exp hs.1 ha, zero_sub]
    rw [this, map_mul, Module.End.mul_apply, hc, map_smul, one_mul, Pi.smul_apply, smul_eq_mul]
  rw [e] at d1
  rw [d1.unique d2, map_one]
  simp

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hX : IsGen ψ om θ τ X GX)
  (hY : IsGen ψ om θ τ (Complex.I • (s * X)) GY)
include hψ hθ hX hY

omit hψ hθ in
theorem gen_theta {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T ((GX + Complex.I • GY) g) :=
  theta_add (hX g hg).1 (theta_smul _ (hY g hg).1)

theorem gen_dRho (τ' : D.what₂.Tau) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) :
    (GX + Complex.I • GY) (Datum.dRho (heisO ψ S T) θ τ' u g) =
      Datum.dRho (heisO ψ S T) θ τ' u ((GX + Complex.I • GY) g) +
        (if τ' = τ then (1 : ℂ) else 0) • annih (heisO ψ S T) θ τ (cplxO 1 s) (X * u) g := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [dRho_add hψ hθ _ _ (hX g hg).1 (theta_smul _ (hY g hg).1), dRho_smul hψ hθ _ _ _ (hY g hg).1]
  split_ifs with h
  · subst h
    have e : cplxO 1 s (X * u) = Complex.I • (s * X) * u := by
      rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
    rw [annih, e, ← (hX g hg).2.1, ← (hY g hg).2.1]
    module
  · rw [(hX g hg).2.2.1 _ h, (hY g hg).2.2.1 _ h, zero_smul, add_zero]

theorem gen_aPlus (τ' : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    (GX + Complex.I • GY) (aPlus (heisO ψ S T) θ τ' J u g) =
      aPlus (heisO ψ S T) θ τ' J u ((GX + Complex.I • GY) g) +
        ((fockScale D τ' : ℂ)⁻¹ * (if τ' = τ then (1 : ℂ) else 0)) • (annih (heisO ψ S T) θ τ (cplxO 1 s) (X * u) g +
          (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 s) (X * J u) g) := by
  rw [aPlus_eq, aPlus_eq, map_smul, map_add, map_smul, gen_dRho hψ hθ hX hY _ _ hg, gen_dRho hψ hθ hX hY _ _ hg]
  module

theorem gen_vac (τ' : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 s) f)
    (hv' : IsFockVacAt (heisO ψ S T) θ τ' J f) : IsFockVacAt (heisO ψ S T) θ τ' J ((GX + Complex.I • GY) f) := by
  intro u
  have e := congrArg (GX + Complex.I • GY) (hv' u)
  rw [annih, map_add, map_smul, gen_dRho hψ hθ hX hY _ _ hf, gen_dRho hψ hθ hX hY _ _ hf, hv, hv, smul_zero,
    add_zero, add_zero, map_zero] at e
  exact e

end Weil

section Kill

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}

theorem anti_I {m : ℕ} {s X : Matrix (Fin m) (Fin m) ℂ} (ha : s * X = -(X * s)) :
    s * (Complex.I • (s * X)) = -(Complex.I • (s * X) * s) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, ← smul_neg, ← Matrix.mul_neg, ← ha]

theorem gen_kill_vac (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (kS : S.SigOK) (kT : T.SigOK)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (sT τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (sT τ * X) ∈ lieAt T τ) (ha : sT τ * X = -(X * sT τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) :
    (GX + Complex.I • GY) f = 0 := by
  obtain ⟨x₁, x₂, y₁, y₂, h⟩ := GlobalTheory.T.maximalCompact_acts_on_realVacua_by_detPowers D ψ θ S T χS χT om hom hθ kS kT (fun _ => 1) sT hS hT
  have sp := GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ (g := sT τ) (hT τ).2.1
  have hk : ∀ ρ, sT ρ * compAt θ ρ (Formalism.L2.Theta.mt T (atTau θ T τ (sT τ))) =
      compAt θ ρ (Formalism.L2.Theta.mt T (atTau θ T τ (sT τ))) * sT ρ := fun ρ => by
    by_cases e : ρ = τ
    · subst e
      have e1 : compAt θ ρ (Formalism.L2.Theta.mt T (atTau θ T ρ (sT ρ))) = sT ρ := sp.2.1
      rw [e1]
    · have e1 : compAt θ ρ (Formalism.L2.Theta.mt T (atTau θ T τ (sT τ))) = 1 := sp.2.2 ρ e
      rw [e1, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) →
      om (1, atTau θ T τ (sT τ)) f = c • f :=
    ⟨_, fun f hf hv => h f hf hv 1 (one_mem _) _ sp.1 (fun _ => by rw [Matrix.one_mul, Matrix.mul_one]) hk⟩
  have h1 := hc _ (gen_theta hX hY hf) fun ρ => gen_vac hom.std hθ hX hY ρ _ hf (hv τ) (hv ρ)
  have h2 : om (1, atTau θ T τ (sT τ)) ((GX + Complex.I • GY) f) = -(c • (GX + Complex.I • GY) f) := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply]
    rw [map_add, map_smul, gen_anti hθ (hT τ) lX ha hX hf (hc f hf hv),
      gen_anti hθ (hT τ) lY (anti_I ha) hY hf (hc f hf hv)]
    module
  rw [← h1, eq_neg_iff_add_eq_zero, ← two_smul ℂ, smul_eq_zero_iff_right two_ne_zero] at h2
  have e' := congrArg (om (1, atTau θ T τ (sT τ))⁻¹) h2
  rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e'

end Kill

section Model

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau}
  {Sp : D.what₂.Tau → SPar} {M : DSModel T Sp}

theorem pMinus_laws {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    cart M τ * Z = -Z ∧ Z * cart M τ = Z := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have eZ : Z = (M.fr τ)⁻¹ * (M.fr τ * Z * (M.fr τ)⁻¹) * M.fr τ := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  have z1 : Formalism.REAL.Jm (M.ε τ) * (M.fr τ * Z * (M.fr τ)⁻¹) = -(M.fr τ * Z * (M.fr τ)⁻¹) := by
    ext a b
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.neg_apply]
    cases e : M.ε τ a
    · simp
    · rw [hZ a b (by simp [e]), mul_zero, neg_zero]
  have z2 : (M.fr τ * Z * (M.fr τ)⁻¹) * Formalism.REAL.Jm (M.ε τ) = M.fr τ * Z * (M.fr τ)⁻¹ := by
    ext a b
    rw [Formalism.REAL.Jm, Matrix.mul_diagonal]
    cases e : M.ε τ b
    · rw [hZ a b (by simp [e]), zero_mul]
    · simp
  have h1 : cart M τ * Z = -Z := by
    generalize M.fr τ * Z * (M.fr τ)⁻¹ = ζ at eZ z1
    rw [eZ, cart, Matrix.mul_assoc _ ζ, Matrix.mul_assoc _ (M.fr τ), Matrix.mul_nonsing_inv_cancel_left _ _ hu,
      Matrix.mul_assoc, ← Matrix.mul_assoc _ ζ, z1, Matrix.neg_mul, Matrix.mul_neg]
  have h2 : Z * cart M τ = Z := by
    generalize M.fr τ * Z * (M.fr τ)⁻¹ = ζ at eZ z2
    rw [eZ, cart, Matrix.mul_assoc _ (M.fr τ), Matrix.mul_assoc (M.fr τ)⁻¹ (Formalism.REAL.Jm _),
      Matrix.mul_nonsing_inv_cancel_left _ _ hu, ← Matrix.mul_assoc, Matrix.mul_assoc _ ζ, z2]
  exact ⟨h1, h2⟩

theorem exists_coef {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} (hp : ∀ a, M.ε τ a = decide ((a : ℕ) < p))
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ)) :
    ∃ ν : Fin T.rank → Fin T.rank → ℂ, (∀ a b : Fin T.rank, ¬ (p ≤ (a : ℕ) ∧ (b : ℕ) < p) → ν a b = 0) ∧
      ∀ a c b d, ∀ u, u = unitMap (BS τ) (onb M τ) a c → ∀ u', u' = unitMap (BS τ) (onb M τ) b d →
        ((omDir S T τ (X * u) τ u' : ℝ) + Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * u)) τ u' : ℝ)) +
          (-Complex.I) * ((omDir S T τ (X * cplxO 1 (cart M τ) u) τ u' : ℝ) +
            Complex.I * (omDir S T τ (cplxO 1 (cart M τ) (X * cplxO 1 (cart M τ) u)) τ u' : ℝ)) =
        (if c = d then ν a b else 0) + (if d = c then ν b a else 0) := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have ht : cart M τ * onb M τ = onb M τ * diagonal fun a => if M.ε τ a then (1 : ℂ) else -1 := by
    rw [cart, onb, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
    rfl
  let o : Matrix (Fin T.rank) (Fin T.rank) ℂ → Fin T.rank → Fin T.rank → ℝ := fun W a b =>
    2 * (tauE D τ D.host.xi0 * ((onb M τ)ᴴ * gramAt D T τ * W * onb M τ) a b).re
  have hre := GlobalTheory.RealSymplForm.realPlace_imaginaryGenerator_re_eq_zero D τ
  have osym : ∀ W ∈ lieAt T τ, ∀ a b, o W a b = o W b a := fun W hW a b =>
    congrArg (2 * ·) (skew_entry (GlobalTheory.SmoothAutCheck.gramAt_herm T τ) hW hre a b)
  have ozero : ∀ W, cart M τ * W = -(W * cart M τ) → ∀ a b : Fin T.rank, ((a : ℕ) < p ↔ (b : ℕ) < p) →
      o W a b = 0 := fun W hW a b hab => by
    simp only [o]
    rw [zero_entry (hT τ) ht hW, mul_zero, Complex.zero_re, mul_zero]
    simp only [hp, decide_eq_true_eq, hab]
    split_ifs <;> norm_num
  have hom1 : ∀ W a c b d, omDir S T τ (W * unitMap (BS τ) (onb M τ) a c) τ (unitMap (BS τ) (onb M τ) b d) =
      if c = d then o W b a else 0 := fun W a c b d => by
    rw [omDir, if_pos rfl, trace_unitMap (hB τ)]
    split_ifs <;> simp [o]
  have hJ : ∀ (W : Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      cplxO 1 (cart M τ) (W * u) = Complex.I • (cart M τ * W) * u := fun W u => by
    rw [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]
  have hJ' : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      X * cplxO 1 (cart M τ) u = (-(Complex.I • (cart M τ * X))) * u := fun u => by
    rw [cplxO, Matrix.mul_one, ha, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  have hJ'' : Complex.I • (cart M τ * -(Complex.I • (cart M τ * X))) = X := by
    rw [Matrix.mul_neg, Matrix.mul_smul, ← Matrix.mul_assoc, (hT τ).1, Matrix.one_mul, smul_neg, smul_smul,
      Complex.I_mul_I, neg_smul, neg_neg, one_smul]
  have oneg : ∀ W a b, o (-W) a b = -o W a b := fun W a b => by
    simp only [o, Matrix.neg_mul, Matrix.neg_apply, mul_neg, Complex.neg_re]
  clear_value o
  refine ⟨fun a b => if p ≤ (a : ℕ) ∧ (b : ℕ) < p then
    2 * (o X a b + Complex.I * o (Complex.I • (cart M τ * X)) a b) else 0, fun a b h => if_neg h, ?_⟩
  rintro a c b d _ rfl _ rfl
  rw [hJ', hJ, hJ, hJ'', hom1, hom1, hom1, oneg]
  by_cases e3 : c = d
  swap
  · simp [e3, Ne.symm e3]
  subst e3
  simp only [if_true]
  have z1 := ozero _ ha
  have z2 := ozero _ (anti_I ha)
  have s1 := osym _ lX a b
  have s2 := osym _ lY a b
  generalize Complex.I • (cart M τ * X) = Y at z2 s2
  rw [s1, s2]
  have e : (o X b a : ℂ) + Complex.I * o Y b a + -Complex.I * ((-o Y b a : ℝ) + Complex.I * o X b a) =
      2 * (o X b a + Complex.I * o Y b a) := by
    push_cast
    linear_combination (-o X b a : ℂ) * Complex.I_mul_I
  rw [e]
  by_cases ha' : (a : ℕ) < p <;> by_cases hb' : (b : ℕ) < p
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]
  · rw [if_neg (by omega), if_pos (by omega), zero_add]
  · rw [if_pos (by omega), if_neg (by omega), add_zero]
  · simp [z1 b a (by simp [ha', hb']), z2 b a (by simp [ha', hb'])]

theorem gen_kill (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    (hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) {p : ℕ} (hp : ∀ a, M.ε τ a = decide ((a : ℕ) < p))
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} {GX GY : Module.End ℂ (WO S T → ℂ)}
    (hX : IsGen ψ om θ τ X GX) (hY : IsGen ψ om θ τ (Complex.I • (cart M τ * X)) GY)
    (lX : X ∈ lieAt T τ) (lY : Complex.I • (cart M τ * X) ∈ lieAt T τ) (ha : cart M τ * X = -(X * cart M τ))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f)
    (h0 : (GX + Complex.I • GY) f = 0) {P : MvPolynomial (FVar D T.rank S.rank) ℂ}
    (hP : ∀ a b : Fin T.rank, p ≤ (a : ℕ) → (b : ℕ) < p →
      ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) :
    (GX + Complex.I • GY) (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) = 0 := by
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨ν, n0, hν⟩ := exists_coef hB hp lX lY ha
  unfold pureTensorO aPlusAll
  refine (quad_pure (P := IsThetaFunO ψ S T) (G := GX + Complex.I • GY)
    (B := fun k g => ((fockScale D k.1 : ℂ)⁻¹ * (if k.1 = τ then (1 : ℂ) else 0)) •
      (annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) (X * unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2) g +
        (-Complex.I) • annih (heisO ψ S T) θ τ (cplxO 1 (cart M τ))
          (X * cplxO 1 (cart M k.1) (unitMap (BS k.1) (onb M k.1) k.2.1 k.2.2)) g))
    (μ := fun i j => if i.1 = τ then if j.1 = τ then if i.2.2 = j.2.2 then
      ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * ν i.2.1 j.2.1 else 0 else 0 else 0)
    (fun _ _ => theta_add) (fun a _ => theta_smul a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf ?_ h0 P).trans ?_
  · exact fun _ _ h => aPlus_theta hψ hθ _ _ _ h
  · exact fun i j _ h => aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
  · exact fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  · exact fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  · intro i g g' hg hg'
    rw [annih_add hψ hθ _ _ _ hg hg', annih_add hψ hθ _ _ _ hg hg']
    simp only [smul_add]
    abel
  · intro i a g hg
    rw [annih_smul hψ hθ _ _ _ _ hg, annih_smul hψ hθ _ _ _ _ hg, smul_comm _ a, ← smul_add, smul_comm _ a]
  · rintro ⟨τ₁, a, c⟩ ⟨τ₂, b, d⟩ g hg
    have ta := fun z => annih_theta hψ hθ τ (cplxO 1 (cart M τ)) z hg
    have aa := fun z => annih_aPlus (sS := fun _ => 1) hψ hθ τ z hS hT τ₂ (unitMap (BS τ₂) (onb M τ₂) b d) hg
    dsimp only at aa ⊢
    rw [aa, aa, aPlus_smul hψ hθ _ _ _ _ (theta_add (ta _) (theta_smul _ (ta _))),
      aPlus_add hψ hθ _ _ _ (ta _) (theta_smul _ (ta _)), aPlus_smul hψ hθ _ _ _ _ (ta _), smul_add (-Complex.I),
      add_add_add_comm, smul_add, smul_smul, ← add_smul, smul_smul]
    refine congrArg₂ (· + ·) rfl (congrArg (· • g) ?_)
    by_cases e1 : τ₁ = τ
    swap
    · simp only [if_neg e1, ite_self, mul_zero, zero_mul, add_zero]
    by_cases e2 : τ₂ = τ
    swap
    · simp [e2, omDir, Ne.symm e2]
    subst e1
    subst e2
    have := hν a c b d _ rfl _ rfl
    simp only [if_true]
    by_cases e3 : c = d
    · simp only [if_pos e3, if_pos e3.symm] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
    · simp only [if_neg e3, if_neg (Ne.symm e3)] at this ⊢
      linear_combination ((fockScale D τ₂ : ℂ)⁻¹ * (fockScale D τ₂ : ℂ)⁻¹ * (-(4 * π * Complex.I))) * this
  · exact fun i _ h => gen_aPlus hψ hθ hX hY _ _ _ h
  · intro i
    rw [hv, hv, smul_zero, add_zero, smul_zero]
  · refine (congrArg _ ?_).trans (map_zero _)
    simp only [Fintype.sum_prod_type, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [← Finset.smul_sum]
    by_cases hab : p ≤ (a : ℕ) ∧ (b : ℕ) < p
    · rw [hP a b hab.1 hab.2, smul_zero]
    · rw [n0 a b hab, mul_zero, zero_smul]

end Model

theorem rderC_theta_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → S.SigOK → T.SigOK → ∀ (BS : D.what₂.Tau → Mt S.rank), (∀ τ, IsONBasis (gramAt D S τ) 1 (BS τ) S.rank) → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (p : D.what₂.Tau → ℕ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < p τ)) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (cart M τ)) f) → ∀ (P : PolF D T.rank S.rank) τ, (∀ a b : Fin T.rank, p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin S.rank, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) P) = 0) → ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P)) = 0 := by
  intro D ψ S T χS χT om hom θ hθ kS kT BS hBS Sp M p hp f hf hv P τ hP Z hZ h
  have hψ := hom.std
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hB : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 := fun τ => by
    obtain ⟨ε, h1, h2, -⟩ := hBS τ
    rw [h2, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases h1 a with h | h
    · rw [h.1, Complex.ofReal_one]
    · exact absurd a.2 (not_lt.2 h.2)
  have hS := fun τ => isCartanInv_one (hB τ)
  obtain ⟨h1, h2⟩ := pMinus_laws hZ
  obtain ⟨ha, eY⟩ := parts (GlobalTheory.SmoothAutCheck.gramAt_unit T τ) (hT τ) h1 h2
  obtain ⟨lX, lY⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  unfold RderC
  unfold conjAt at lX lY ⊢
  rw [eY] at lY ⊢
  generalize (1 / 2 : ℂ) • (Z + -((gramAt D T τ)⁻¹ * Zᴴ * gramAt D T τ)) = X at ha lX lY
  obtain ⟨GX, hX⟩ : ∃ G, IsGen ψ om θ τ X G := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lX
  obtain ⟨GY, hY⟩ : ∃ G, IsGen ψ om θ τ (Complex.I • (cart M τ * X)) G :=
    GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ _ lY
  have hφ : IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P) :=
    pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
      (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
  have key := gen_kill hψ hθ hB (hp τ) hX hY lX lY ha hf (hv τ)
    (gen_kill_vac hom hθ kS kT hS hT hX hY lX lY ha hf hv) hP
  generalize pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f P = φ at key hφ
  funext g
  have a1 := ((hX φ hφ).2.2.2 (h, g) 0).deriv
  have a2 := ((hY φ hφ).2.2.2 (h, g) 0).deriv
  simp only [Prod.mk_mul_mk, mul_one] at a1 a2
  have a3 := congrFun (congrArg (om (h, g)) key) 0
  rw [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, map_zero] at a3
  simp only [Pi.add_apply, Pi.smul_apply, Rder, thetaKO]
  rw [a1, a2]
  exact a3

end GlobalTheory.FockKill
