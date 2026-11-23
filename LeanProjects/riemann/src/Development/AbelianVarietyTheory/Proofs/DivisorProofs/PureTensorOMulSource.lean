import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergDerivativeThetaFunctionLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.SourceBasis

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

local notation "dR" => Formalism.IndefR.Datum.dRho (heisO ψ S T) θ

theorem dRho_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (∀ f', IsThetaFunO ψ S T f' → dR τ z (f + f') = dR τ z f + dR τ z f') ∧
    (∀ a : ℂ, dR τ z (a • f) = a • dR τ z f) ∧
    (∀ z', dR τ (z + z') f = dR τ z f + dR τ z' f) ∧
    (∀ t : ℝ, dR τ ((t : ℂ) • z) f = (t : ℂ) • dR τ z f) ∧
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ), dR τ z (dR τ' z' f) - dR τ' z' (dR τ z f) =
      (-(2 * Real.pi * I) * (omO S T (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
        (Pi.single τ' z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ)) • f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have pl := @GlobalTheory.Ker.HeisDeriv.pi_lineAt D S T θ hθ
  have hE : ∀ τ z g, dR τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun τ z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  refine ⟨fun f' hf' => ?_, fun a => ?_, fun z' => ?_, fun t => ?_, fun τ' z' => ?_⟩
  · funext w
    rw [Pi.add_apply, hE, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_add hf hf')), hD_eq_fderiv _ _ _ _ hs,
      hD_eq_fderiv _ _ _ _ (theta_sm h hf')]
    have e : (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        fun x : RW T S => f (w + iotaW σ T S x) + f' (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_add (hd hf w) (hd hf' w), ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  · funext w
    rw [Pi.smul_apply, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_smul a hf)), hD_eq_fderiv _ _ _ _ hs]
    have e : (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        fun x : RW T S => a • f (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_const_smul (hd hf w), ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  · have e : piW θ T S (lineAt θ τ (z + z') 1) =
        piW θ T S (lineAt θ τ z 1) + piW θ T S (lineAt θ τ z' 1) := by
      rw [pl, pl, pl, Pi.single_add]
      rfl
    funext w
    rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_add, ContinuousLinearMap.map_add]
    push_cast
    ring
  · have e : piW θ T S (lineAt θ τ ((t : ℂ) • z) 1) = t • piW θ T S (lineAt θ τ z 1) := by
      rw [pl, pl, Pi.single_smul]
      rfl
    funext w
    rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
      LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
      have h1 := omO_self h (S := S) (T := T) (u + v)
      simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
      linarith
    rw [hE, hE, hE, hE, heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota T S)
      (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) sk f hs, pl, pl]
    all_goals (congr 1; push_cast; ring)

theorem onb_selfadjoint {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) (hB : B.det ≠ 0) :
    sᴴ * G = G * s ∧ s * s = 1 := by
  obtain ⟨ε, h0, h1, h2⟩ := h
  have hu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).2 hB.isUnit
  have hu' : IsUnit Bᴴ := hu.star
  constructor
  · refine hu.mul_right_cancel (hu'.mul_left_cancel ?_)
    calc Bᴴ * (sᴴ * G * B) = (s * B)ᴴ * G * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Matrix.diagonal fun a => (ε a : ℂ)) * (Bᴴ * G * B) := by
        rw [h2, conjTranspose_mul, diagonal_conjTranspose]
        simp only [Matrix.mul_assoc]
        congr 2
        funext a
        simp
      _ = (Bᴴ * G * B) * (Matrix.diagonal fun a => (ε a : ℂ)) := by rw [h1]
      _ = _ := by simp only [Matrix.mul_assoc, h2]
  · refine hu.mul_right_cancel ?_
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h2, Matrix.mul_assoc, diagonal_mul_diagonal, Matrix.one_mul]
    conv_rhs => rw [← Matrix.mul_one B, ← Matrix.diagonal_one]
    congr 2
    funext a
    rcases h0 a with h | h <;> simp [h.1]

theorem formAt_trace (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ x y =
      2 * (tauE D τ D.host.xi0 * Matrix.trace ((S.gram⁻¹).map (tauE D τ) * yᴴ * gramAt D T τ * x)).re := by
  unfold formAt
  congr 3
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, gramAt, Matrix.map_apply,
    conjTranspose_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  symm
  rw [Finset.sum_comm]
  conv_lhs => enter [2, e]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem formAt_cplx (τ : D.what₂.Tau) {s : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hs : sᴴ * gramAt D T τ = gramAt D T τ * s) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    formAt S T τ (cplxO 1 s x) y = -formAt S T τ x (cplxO 1 s y) := by
  rw [formAt_trace, formAt_trace]
  unfold cplxO
  simp only [Matrix.mul_one, conjTranspose_smul, conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, trace_smul,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc sᴴ, hs, Matrix.mul_assoc]
  simp
  ring

theorem omO_cplx {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hs : ∀ τ, (s τ)ᴴ * gramAt D T τ = gramAt D T τ * s τ) (τ τ' : D.what₂.Tau)
    (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (Pi.single τ (cplxO 1 (s τ) x) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
        (Pi.single τ' y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) =
      -omO S T (Pi.single τ x : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
        (Pi.single τ' (cplxO 1 (s τ') y) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  have e : ∀ (τ τ'' : D.what₂.Tau) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      (Pi.single τ (cplxO 1 (s τ) x) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) τ'' =
        cplxO 1 (s τ'') ((Pi.single τ x : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) τ'') := by
    intro τ τ'' x
    by_cases h : τ'' = τ
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
      simp [cplxO]
  show ∑ τ'', formAt S T τ'' _ _ = -∑ τ'', formAt S T τ'' _ _
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ'' _ => ?_
  rw [e, e]
  exact formAt_cplx τ'' (hs τ'') _ _

theorem cplxO_cplxO {m n : ℕ} {s : Matrix (Fin m) (Fin m) ℂ} (hs : s * s = 1) (x : Matrix (Fin m) (Fin n) ℂ) :
    cplxO 1 s (cplxO 1 s x) = -x := by
  unfold cplxO
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hs, Matrix.one_mul, I_mul_I,
    neg_one_smul]

section Ops

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)

theorem aPlus_eq (f : WO S T → ℂ) : aPlus (heisO ψ S T) θ τ J z f =
    ((fockScale D τ : ℂ)⁻¹) • (dR τ z f + (-I) • dR τ (J z) f) := by
  rw [aPlus, crea, neg_smul, sub_eq_add_neg]

include hψ hθ

theorem aPlus_th {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (aPlus (heisO ψ S T) θ τ J z f) := by
  rw [aPlus_eq]
  exact theta_smul _ (theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf)))

theorem aPlus_add {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    aPlus (heisO ψ S T) θ τ J z (f + f') = aPlus (heisO ψ S T) θ τ J z f + aPlus (heisO ψ S T) θ τ J z f' := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).1 f' hf']
  module

theorem aPlus_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (a • f) = a • aPlus (heisO ψ S T) θ τ J z f := by
  simp only [aPlus_eq, fun z => (dRho_laws hψ hθ hf τ z).2.1 a]
  module

theorem aPlus_comm {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hs : ∀ τ, (s τ)ᴴ * gramAt D T τ = gramAt D T τ * s τ) (hs2 : ∀ τ, s τ * s τ = 1)
    (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 (s τ)) z (aPlus (heisO ψ S T) θ τ' (cplxO 1 (s τ')) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO 1 (s τ')) z' (aPlus (heisO ψ S T) θ τ (cplxO 1 (s τ)) z f) := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => eq_add_of_sub_eq ((dRho_laws hψ hθ hf τ z).2.2.2.2 τ' z')
  have h2 := omO_cplx hs τ τ' z z'
  have h1 := omO_cplx hs τ τ' z (cplxO 1 (s τ') z')
  rw [cplxO_cplxO (hs2 τ'), Pi.single_neg] at h1
  erw [LinearMap.map_neg] at h1
  rw [neg_neg] at h1
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO 1 (s τ') z'), hc τ (cplxO 1 (s τ) z) τ' z',
    hc τ (cplxO 1 (s τ) z) τ' (cplxO 1 (s τ') z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

theorem crea_smul {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) (p : Prop) [Decidable p]
    (hz : s * z = (if p then (1 : ℂ) else -1) • z) (a : ℂ) :
    crea (heisO ψ S T) θ τ (cplxO 1 s) (a • z) f =
      (if p then a else conj a) • crea (heisO ψ S T) θ τ (cplxO 1 s) z f := by
  have h := fun a z => GlobalTheory.Ker.ColChange.real_smul_split (fun z => dR τ z f)
    (fun x y => (dRho_laws hψ hθ hf τ x).2.2.1 y)
    (fun t x => (dRho_laws hψ hθ hf τ x).2.2.2.1 t) a z
  unfold crea cplxO
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_smul, hz, smul_smul, smul_smul, smul_smul, h a, h (I * a * _),
    h (I * ite _ _ _)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, a = x + y * I := ⟨_, _, (Complex.re_add_im a).symm⟩
  funext w
  split_ifs
  · simp
    linear_combination (y * dR τ (I • z) f w) * Complex.I_sq
  · simp
    linear_combination (y * dR τ (I • z) f w) * Complex.I_sq

theorem crea_sum {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (t : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    crea (heisO ψ S T) θ τ (cplxO 1 s) (∑ l ∈ t, z l) f = ∑ l ∈ t, crea (heisO ψ S T) θ τ (cplxO 1 s) (z l) f := by
  let F : Matrix (Fin T.rank) (Fin S.rank) ℂ →+ (WO S T → ℂ) :=
    AddMonoidHom.mk' (fun z => crea (heisO ψ S T) θ τ (cplxO 1 s) z f) fun x y => by
      have h := fun x y => (dRho_laws hψ hθ hf τ x).2.2.1 y
      unfold crea cplxO
      rw [Matrix.mul_add, Matrix.add_mul, smul_add, h, h, smul_add]
      abel
  exact map_sum F z t

end Ops

theorem unitMap_mul {m n : ℕ} (H U : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (j : Fin n) :
    unitMap (H * U) B i j = ∑ l, U⁻¹ j l • unitMap H B i l := by
  have h := congrArg (· * H⁻¹) (GlobalTheory.Ker.ColChange.unitMap_expand U B i j)
  simp only [unitMap, inv_one, Matrix.mul_one, Matrix.sum_mul, Matrix.smul_mul] at h ⊢
  rw [← h, Matrix.mul_inv_rev, ← Matrix.mul_assoc]

theorem onb_unitMap {k n : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p)
    (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin k) (l : Fin n) :
    s * unitMap H B i l = (if (i : ℕ) < p then (1 : ℂ) else -1) • unitMap H B i l := by
  obtain ⟨ε, h0, -, h2⟩ := h
  unfold unitMap
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.mul_assoc B]
  congr 2
  ext a b
  rw [Matrix.diagonal_mul]
  by_cases h : i = a
  · subst h
    rcases h0 i with h | h
    · simp [h.1, h.2]
    · simp [h.1, not_lt.2 h.2]
  · simp [h]

theorem pureTensorO_mul_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BV U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pW : D.what₂.Tau → ℕ), (∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) → (∀ τ, (BW τ).det ≠ 0) → (∀ τ, (BV τ).det ≠ 0) → (∀ τ, (U τ).det ≠ 0) → ∀ f, IsThetaFunO ψ V W f → ∀ P : MvPolynomial (FVar D W.rank V.rank) ℂ, pureTensorO ψ θ V W (fun _ => 1) s (fun τ => BV τ * U τ) BW f P = pureTensorO ψ θ V W (fun _ => 1) s BV BW f (MvPolynomial.aeval (fun k : FVar D W.rank V.rank => ∑ b, MvPolynomial.C (if (k.2.1 : ℕ) < pW k.1 then (U k.1)⁻¹ k.2.2 b else conj ((U k.1)⁻¹ k.2.2 b)) * MvPolynomial.X (k.1, k.2.1, b)) P) := by
  intro D ψ θ V W hψ hθ BV U s BW pW hon hBW _ _ f hf P
  have hs := fun τ => onb_selfadjoint (hon τ) (hBW τ)
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') := fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun τ => cplxO 1 (s τ)) BS BW i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have hm : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) Q,
      IsThetaFunO ψ V W (pureTensorO ψ θ V W (fun _ => 1) s BS BW f Q) := fun BS Q =>
    GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) hadd hsm (hA BS) hf Q
  have hX : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) Q v,
      pureTensorO ψ θ V W (fun _ => 1) s BS BW f (MvPolynomial.X v * Q) =
        aPlusAll (heisO ψ V W) θ (fun τ => cplxO 1 (s τ)) BS BW v (pureTensorO ψ θ V W (fun _ => 1) s BS BW f Q) :=
    fun BS Q v => GlobalTheory.Ker.FockAlg.pure_X_mul (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO 1 (s τ)) BS BW)
      (P := IsThetaFunO ψ V W) hadd hsm (hA BS)
      (fun i j _ h => aPlus_comm hψ hθ i.1 _ (fun τ => (hs τ).1) (fun τ => (hs τ).2) j.1 _ h)
      (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h) hf Q v
  have h1 : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      pureTensorO ψ θ V W (fun _ => 1) s BS BW f 1 = f := fun BS => GlobalTheory.Ker.FockAlg.pure_one f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul,
      map_smul, map_smul, h1, h1]
  | add P Q hP hQ => rw [map_add, map_add, map_add, hP, hQ]
  | mul_X P v hP =>
    obtain ⟨τ, i, j⟩ := v
    rw [mul_comm, hX, hP, map_mul, MvPolynomial.aeval_X]
    clear hP
    generalize (MvPolynomial.aeval _ P : MvPolynomial (FVar D W.rank V.rank) ℂ) = Q
    simp only [← MvPolynomial.smul_eq_C_mul, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hX]
    simp only [aPlusAll, aPlus]
    rw [unitMap_mul, crea_sum hψ hθ _ (hm _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [crea_smul hψ hθ τ _ (hm _ _) _ _ (onb_unitMap (hon τ) _ i l), smul_comm]

end GlobalTheory.AdTh.SourceBasis

end
