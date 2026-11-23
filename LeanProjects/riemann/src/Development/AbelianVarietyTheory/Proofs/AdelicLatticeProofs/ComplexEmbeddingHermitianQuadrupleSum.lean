import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RealAdeleExtAndStandardCharacterFormula
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.FockCompare
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplOH_add_left (x x' y : WO S T) : symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOH_add_right (x y y' : WO S T) : symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem gramInv_star (V : HSp D) (i j) : star (V.gram⁻¹ i j) = V.gram⁻¹ j i := by
  have h : V.gram.IsHermitian := by
    funext i j
    exact GlobalTheory.DualPairCheck.gram_star V j i
  exact congrFun (congrFun h.inv j) i

theorem herm_sum {A : Type} [CommRing A] {m n : ℕ} (c : A →+* A) (hc : ∀ a, c (c a) = a) (P : Fin n → Fin n → A)
    (Q : Fin m → Fin m → A) (hP : ∀ i k, c (P i k) = P k i) (hQ : ∀ i k, c (Q i k) = Q k i)
    (x y : Matrix (Fin m) (Fin n) A) :
    c (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a) =
      ∑ a, ∑ b, ∑ e, ∑ d, P a b * c (x e b) * Q e d * y d a := by
  simp only [map_sum, map_mul, hc, hP, hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hO_herm (x y : WO S T) : cA D (hO S T x y) = hO S T y x :=
  herm_sum (cA D) GlobalTheory.DualPairCheck.cA_cA (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k))
    (fun i k => by rw [GlobalTheory.DualPairCheck.cA_incA, gramInv_star])
    (fun i k => by rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]) x y

theorem symplO_skew (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, hO_herm, map_neg,
    neg_mul, map_neg]

theorem map_hO_zero {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (q : A →+* B) (c : A →+* A)
    (hc : ∀ z, q z = 0 → q (c z) = 0) (P : Fin n → Fin n → A) (Q : Fin m → Fin m → A)
    (x y : Matrix (Fin m) (Fin n) A) (h : x.map q = 0 ∨ y.map q = 0) :
    q (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a) = 0 := by
  have hk : ∀ i j k l (a b : A), q (a * c (y i j) * b * x k l) = 0 := by
    intro i j k l a b
    rw [map_mul, map_mul, map_mul]
    rcases h with h | h
    · have h1 : q (x k l) = 0 := congrFun (congrFun h k) l
      rw [h1, mul_zero]
    · have h1 : q (y i j) = 0 := congrFun (congrFun h i) j
      rw [hc _ h1, mul_zero, zero_mul, zero_mul]
  simp only [map_sum, hk, Finset.sum_const_zero]

theorem map_trace_hO_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (p : A →ₐ[F] B) (s : E →ₐ[F] E) {m n : ℕ}
    (c : A ⊗[F] E) (P : Fin n → Fin n → A ⊗[F] E) (Q : Fin m → Fin m → A ⊗[F] E)
    (x y : Matrix (Fin m) (Fin n) (A ⊗[F] E))
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom = 0) :
    p (Algebra.trace A (A ⊗[F] E) (c * ∑ a, ∑ b, ∑ e, ∑ d, P a b * sigR A s (y e b) * Q e d * x d a)) = 0 := by
  have hc : ∀ z : A ⊗[F] E, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s z) =
      sigR B s ((Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [RingHom.map_zero]
    | add a b ha hb => simp only [RingHom.map_add, ha, hb]
    | tmul a e => rfl
  have hh := map_hO_zero (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom (sigR A s)
    (fun z hz => by rw [hc, hz, map_zero]) P Q x y h
  rw [map_trace_tensor, map_mul]
  erw [hh]
  rw [mul_zero, map_zero]

theorem map_symplO_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (x y : WO S T)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (symplO S T x y) = 0 := by
  unfold symplO hO
  exact map_trace_hO_zero p D.sp.cm.sig _ (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k)) x y h

theorem snd_symplO {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplO S T x y) = 0 := map_symplO_eq_zero (sndA D.host.F) x y h

theorem fst_symplO {x y : WO S T} (h : x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) :
    fstA D.host.F (symplO S T x y) = 0 := map_symplO_eq_zero (fstA D.host.F) x y h

theorem symplOH_fin_real {u x : WO S T} (hu : u.map (infPart D) = 0) (hx : x.map (finPart D) = 0) :
    symplOH S T u x = 0 ∧ symplOH S T x u = 0 := by
  have h1 : symplO S T u x = 0 := Prod.ext (fst_symplO (Or.inl hu)) (snd_symplO (Or.inr hx))
  have h2 : symplO S T x u = 0 := Prod.ext (fst_symplO (Or.inr hu)) (snd_symplO (Or.inl hx))
  unfold symplOH
  rw [h1, h2, mul_zero]
  exact ⟨rfl, rfl⟩

theorem continuous_symplOH {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOH S T (x t) (y t) := by
  have hy' : ∀ i j, Continuous fun t => cA D (y t i j) := fun i j =>
    ThetaCont.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hO S T (x t) (y t) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF D.host.F) (Formalism.L2.Theta.AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

def formAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Fin T.rank → Fin S.rank → ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * ∑ a, ∑ b, ∑ e, ∑ d,
    tauE D τ (S.gram⁻¹ a b) * starRingEnd ℂ (y e b) * tauE D τ (T.gram e d) * x d a).re

theorem formAt_smul_left (τ : D.what₂.Tau) (c : ℝ) (x y : Fin T.rank → Fin S.rank → ℂ) :
    formAt S T τ (c • x) y = c * formAt S T τ x y := by
  unfold formAt
  rw [mul_left_comm c, ← Complex.re_ofReal_mul c, mul_left_comm (c : ℂ)]
  congr 3
  simp only [Finset.mul_sum, Pi.smul_apply, Complex.real_smul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

theorem formAt_smul_right (τ : D.what₂.Tau) (c : ℝ) (x y : Fin T.rank → Fin S.rank → ℂ) :
    formAt S T τ x (c • y) = c * formAt S T τ x y := by
  unfold formAt
  rw [mul_left_comm c, ← Complex.re_ofReal_mul c, mul_left_comm (c : ℂ)]
  congr 3
  simp only [Finset.mul_sum, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, formAt S T τ (x τ) (y τ))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [formAt, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re])
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => formAt_smul_left τ c _ _)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [formAt, Pi.add_apply, mul_add, add_mul, map_add, Finset.sum_add_distrib, Complex.add_re])
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => formAt_smul_right τ c _ _)

theorem complexEmbedding_hermitianQuadrupleSum {A : Type} [CommRing A] (φ : A →+* ℂ) (c : A →+* A) (hc : ∀ a, φ (c a) = starRingEnd ℂ (φ a))
    {m n : ℕ} (x y : Fin m → Fin n → A) (P : Fin n → Fin n → A) (Q : Fin m → Fin m → A) :
    φ (∑ a, ∑ b, ∑ e, ∑ d, P a b * c (y e b) * Q e d * x d a) =
      ∑ a, ∑ b, ∑ e, ∑ d, φ (P a b) * starRingEnd ℂ (φ (y e b)) * φ (Q e d) * φ (x d a) := by
  simp only [map_sum, map_mul, hc]

theorem valTau_symplO (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x y : WO S T) :
    valTau θ τ (symplO S T x y) = formAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  have h := complexEmbedding_hermitianQuadrupleSum ((θ τ).comp (infPart D)) (cA D) (comp_cA hθ τ) x y
    (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k))
  simp only [hi] at h
  unfold valTau symplO formAt
  rw [SymplVal.trace_AE, RingHom.map_add, RingHom.map_add, comp_cA hθ, RingHom.map_mul, RingHom.map_mul, comp_incA hθ,
    Complex.add_re, Complex.conj_re, two_mul]
  erw [h]
  rfl

theorem psi_symplOH (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (w : WO S T) (x : RW T S) :
    ψ (symplOH S T w (iotaW σ T S x)) =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S w) x : ℝ)) := by
  unfold symplOH
  rw [(real_adele_ext_and_char D θ σ h _ (snd_symplO (Or.inr (h.real_iota T S x)))).2 ψ hψ]
  congr 3
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [valTau_symplO h.inf, h.pi_iota]

theorem symplOH_self (x : WO S T) : symplOH S T x x = 0 := by
  have h := symplO_skew x x
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
  have h3 : 2 * symplO S T x x = 0 := by rw [two_mul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  have h4 : symplO S T x x = 0 := by
    rw [← one_mul (symplO S T x x), ← h2, mul_assoc, h3, mul_zero]
  unfold symplOH
  rw [h4, mul_zero]

theorem omO_self (h : Chart θ σ) (x : RW T S) : omO S T x x = 0 := by
  have h1 : symplO S T (iotaW σ T S x) (iotaW σ T S x) = -symplO S T (iotaW σ T S x) (iotaW σ T S x) := symplO_skew _ _
  refine Finset.sum_eq_zero fun τ _ => ?_
  have h2 := valTau_symplO h.inf τ (S := S) (T := T) (iotaW σ T S x) (iotaW σ T S x)
  have h3 : valTau θ τ (-symplO S T (iotaW σ T S x) (iotaW σ T S x)) =
      -valTau θ τ (symplO S T (iotaW σ T S x) (iotaW σ T S x)) := by
    unfold valTau
    rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_neg, Complex.neg_re]
  rw [← h1, h2, h.pi_iota] at h3
  linarith

theorem theta_zero : IsThetaFunO ψ S T 0 where
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
  cont := continuous_const
  smooth k L _ _ w := contDiff_const

theorem theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f + g) where
  quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    obtain ⟨U', hU', h2⟩ := hg.level
    refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (h1 u hu.1 h0) w
    have e2 := congrFun (h2 u hu.2 h0) w
    unfold heisO at e1 e2 ⊢
    rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
  cont := hf.cont.add hg.cont
  smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

theorem theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) where
  quasi γ w := by
    rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
  level := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (h1 u hu h0) w
    unfold heisO at e1 ⊢
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
  cont := hf.cont.const_smul c
  smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)

theorem theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  have := theta_add hf (theta_smul (-1) hg)
  rwa [neg_one_smul, ← sub_eq_add_neg] at this

theorem heisO_heisO (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisO_quasi (w₀ : WO S T) (f : WO S T → ℂ)
    (hf : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (γ w) :
    heisO ψ S T w₀ f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * heisO ψ S T w₀ f w := by
  simp only [heisO]
  rw [add_assoc, hf, symplOH_add_left, symplOH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem heisO_comm_fin_real {u x : WO S T} (hu : u.map (infPart D) = 0) (hx : x.map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : heisO ψ S T u f = f) : heisO ψ S T u (heisO ψ S T x f) = heisO ψ S T x f := by
  conv_rhs => rw [← hf]
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real hu hx).1, (symplOH_fin_real hu hx).2, add_comm]

theorem continuous_of_level (h : Chart θ σ) (hψ : Continuous ψ) (f : WO S T → ℂ)
    (hU : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f)
    (hs : Sm (iotaW σ T S) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WO S T → RW T S := fun w' => piW θ T S (w' - w)
  let a : WO S T → WO S T := fun w' => w + iotaW σ T S (x w')
  let u : WO S T → WO S T := fun w' => w' - a w'
  have hx : Continuous x := (continuous_pi' h.inf T S).comp (continuous_id.sub continuous_const)
  have ha : Continuous a := continuous_const.add ((h.continuous_iota T S).comp hx)
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + iotaW σ T S (piW θ T S (w - w))) = 0
    rw [sub_self, AddMonoidHom.map_zero, AddMonoidHom.map_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPart D) = 0 := by
    intro w'
    have hp : piW θ T S (u w') = 0 := by
      show piW θ T S (w' - (w + iotaW σ T S (piW θ T S (w' - w)))) = 0
      rw [← sub_sub, AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  have hg : Continuous fun w' => ψ (-symplOH S T (a w') (u w')) * f (a w') :=
    (hψ.comp (continuous_symplOH ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplOH S T (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplOH S T (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

theorem theta_sm (h : Chart θ σ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : Sm (iotaW σ T S) f :=
  ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth

theorem heisO_iota (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (x : RW T S) (f : WO S T → ℂ) (w : WO S T) :
    heisO ψ S T (iotaW σ T S x) f w =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S w) x : ℝ)) * f (w + iotaW σ T S x) := by
  unfold heisO
  rw [psi_symplOH h hψ]

theorem theta_heisO_real (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {x : WO S T} (hx : x.map (finPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T x f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T x f) = heisO ψ S T x f := by
    obtain ⟨U, hU, hl⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => heisO_comm_fin_real h0 hx (hl u hu h0)⟩
  have hsm : Sm (iotaW σ T S) (heisO ψ S T x f) := by
    intro w
    rw [← h.iota_pi (V := T) (W := S) hx]
    generalize piW θ T S x = z
    have e : (fun y => heisO ψ S T (iotaW σ T S z) f (w + iotaW σ T S y)) = fun y =>
        Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM ((omO S T).flip z (piW θ T S w + y)))) *
          f ((w + iotaW σ T S z) + iotaW σ T S y) := by
      funext y
      rw [heisO_iota h hψ, AddMonoidHom.map_add, h.pi_iota, add_right_comm]
      rfl
    rw [e]
    refine ContDiff.mul (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_)))
      (theta_sm h hf _)
    exact (LinearMap.toContinuousLinearMap ((omO S T).flip z)).contDiff.comp (contDiff_const.add contDiff_id)
  exact ⟨heisO_quasi x f hf.quasi, hlev, continuous_of_level h hψ.1.1 _ hlev hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T S).1 _).2 hsm⟩

def dLine (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ →+ WO S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => deriv (fun t : ℝ => heisO ψ S T (L t) f w) 0

theorem dRho_eq_dLine (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f = dLine ψ S T (lineAt θ τ z) f := rfl

theorem dLine_eq_hD (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    (f : WO S T → ℂ) : dLine ψ S T L f = hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (L 1)) f := by
  funext w
  unfold dLine hD
  congr 1
  funext t
  rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L hL t, heisO_iota h hψ]

theorem theta_dLine (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (dLine ψ S T L f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hsm := (hD_formula_smooth _ _ (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S) f (theta_sm h hf)
    (piW θ T S (L 1))).2
  rw [← dLine_eq_hD h hψ hL] at hsm
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (dLine ψ S T L f) = dLine ψ S T L f := by
    obtain ⟨U, hU, hl⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have : (fun t => heisO ψ S T (L t) f w) = fun t => heisO ψ S T u (heisO ψ S T (L t) f) w := by
      funext t; rw [heisO_comm_fin_real h0 (hL.2 t) (hl u hu h0)]
    conv_rhs => unfold dLine; rw [this]
    unfold dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  refine ⟨fun γ w => ?_, hlev, continuous_of_level h hψ.1.1 _ hlev hsm,
    ((smooth_iff_sm_and_real_lines D θ σ h T S).1 _).2 hsm⟩
  unfold dLine
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  exact heisO_quasi (L t) f hf.quasi γ w

theorem heisO_line_add (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    (f : WO S T → ℂ) (s t : ℝ) : heisO ψ S T (L (s + t)) f = heisO ψ S T (L s) (heisO ψ S T (L t) f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L hL
  have h1 : ψ (symplOH S T (L s) (L t)) = 1 := by
    rw [e s, e t, psi_symplOH h hψ, h.pi_iota, LinearMap.map_smul₂, map_smul, omO_self h]
    simp
  rw [heisO_heisO, h1, one_smul, L.map_add]

theorem hasDerivAt_heisO (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : IsRealDir T S L)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) (s : ℝ) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (heisO ψ S T (L s) (dLine ψ S T L f) w) s := by
  have h0 : ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (dLine ψ S T L f w) 0 := by
    intro w
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    refine DifferentiableAt.hasDerivAt ?_
    have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ =>
        Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (t * omO S T (piW θ T S w) (piW θ T S (L 1))))) *
          f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
      funext t
      rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L hL t, heisO_iota h hψ, map_smul]
      rfl
    rw [e]
    have h1 : ContDiff ℝ ∞ fun t : ℝ => f (w + iotaW σ T S (t • piW θ T S (L 1))) :=
      (theta_sm h hf w).comp (contDiff_id.smul contDiff_const)
    have h2 : ContDiff ℝ ∞ fun t : ℝ =>
        Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (t * omO S T (piW θ T S w) (piW θ T S (L 1))))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul contDiff_const)))
    exact (h2.mul h1).differentiable (by simp) 0
  have h1 := (h0 (w + L s)).const_mul (ψ (symplOH S T w (L s)))
  have h2 : HasDerivAt (fun t : ℝ => heisO ψ S T (L (s + t)) f w) (heisO ψ S T (L s) (dLine ψ S T L f) w) (s - s) := by
    rw [sub_self]
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show heisO ψ S T (L (s + t)) f w = _
    rw [heisO_line_add hθ hψ hL]
    rfl
  have h3 := h2.comp_sub_const s s
  simpa only [add_sub_cancel] using h3

end GlobalTheory.OrientedHeis

end
