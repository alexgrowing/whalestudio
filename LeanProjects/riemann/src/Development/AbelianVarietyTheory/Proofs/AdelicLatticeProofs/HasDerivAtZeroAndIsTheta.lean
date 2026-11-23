import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticRealPartVanish
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOfHeisenbergLevelAndSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FockCompare

section Abstract

variable {G R : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]

theorem hasDerivAt_exp_mul (ι : R →+ G) (c : ℂ) (f : G → ℂ) (hf : Sm ι f) (u : R) (w : G) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * c) * f (w + ι (t • u)))
      (c * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
  have hd : DifferentiableAt ℝ (fun x : R => f (w + ι x)) ((0 : ℝ) • u) :=
    ((hf w).differentiable (by simp)).differentiableAt
  have hl : HasDerivAt (fun t : ℝ => t • u) u 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u
  have h2 : HasDerivAt (fun t : ℝ => f (w + ι (t • u)))
      (fderiv ℝ (fun x : R => f (w + ι x)) 0 u) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [zero_smul] at this
    exact this
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c 0 := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const c
  have h3 := h0.cexp.mul h2
  refine HasDerivAt.congr_deriv h3 ?_
  simp

theorem contDiff_additive [FiniteDimensional ℝ R] (φ : R →+ ℂ) (h : Continuous φ) : ContDiff ℝ ∞ φ :=
  (φ.toRealLinearMap h).contDiff

theorem sm_deriv (ι : R →+ G) (φ : G →+ ℂ) (hφ : ContDiff ℝ ∞ fun x => φ (ι x)) (f : G → ℂ) (hf : Sm ι f) (u : R) :
    Sm ι fun w => φ w * f w + fderiv ℝ (fun x : R => f (w + ι x)) 0 u := by
  intro w
  have e : (fun x : R => φ (w + ι x) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 u) = fun x : R =>
      (φ w + φ (ι x)) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι y)) x u := by
    funext x
    rw [map_add φ]
    congr 2
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => f (w + ι y)) (x := 0) x
    rw [add_zero] at this
    rw [← this]
    congr 1
    funext y
    rw [map_add, add_assoc]
  show ContDiff ℝ ∞ fun x : R => φ (w + ι x) * f (w + ι x) + fderiv ℝ (fun y : R => f (w + ι x + ι y)) 0 u
  rw [e]
  refine ContDiff.add (ContDiff.mul (contDiff_const.add hφ) (hf w)) ?_
  exact ((hf w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem sm_translate (ι : R →+ G) (φ : G →+ ℂ) (hφ : ContDiff ℝ ∞ fun x => φ (ι x)) (f : G → ℂ) (hf : Sm ι f) (v : G) :
    Sm ι fun w => Complex.exp (φ w) * f (w + v) := by
  intro w
  have e : (fun x : R => Complex.exp (φ (w + ι x)) * f (w + ι x + v)) = fun x : R =>
      Complex.exp (φ w + φ (ι x)) * f (w + v + ι x) := by
    funext x
    rw [map_add φ, add_right_comm]
  show ContDiff ℝ ∞ fun x : R => Complex.exp (φ (w + ι x)) * f (w + ι x + v)
  rw [e]
  exact (contDiff_const.add hφ).cexp.mul (hf _)

end Abstract

variable {D : D7}

theorem symplOH_add_left (S T : HSp D) (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOH_add_right (S T : HSp D) (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH symplO hO
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem symplOH_zero_left (S T : HSp D) (y : WO S T) : symplOH S T 0 y = 0 := by
  have := symplOH_add_left S T 0 0 y
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem symplOH_zero_right (S T : HSp D) (y : WO S T) : symplOH S T y 0 = 0 := by
  have := symplOH_add_right S T y 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem gram_inv_star (V : HSp D) (i j) : star (V.gram⁻¹ i j) = V.gram⁻¹ j i := by
  have h : V.gram.IsHermitian :=
    Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i
  exact congrFun (congrFun h.inv j) i

theorem herm_sum {A : Type} [CommRing A] {m n : ℕ} (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (hP : ∀ i k, σ (P i k) = P k i) (hQ : ∀ i k, σ (Q i k) = Q k i)
    (x y : Matrix (Fin n) (Fin m) A) :
    σ (∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (x c b) * Q c d * y d a := by
  simp only [map_sum, map_mul, hσ, hP, hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x :=
  herm_sum (cA D) GlobalTheory.DualPairCheck.cA_cA (fun i k => incA D (S.gram⁻¹ i k)) (fun i k => incA D (T.gram i k))
    (fun i k => by rw [GlobalTheory.DualPairCheck.cA_incA, gram_inv_star])
    (fun i k => by rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]) x y

theorem symplO_skew (S T : HSp D) (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, hO_herm, map_neg,
    neg_mul, map_neg]

theorem symplOH_skew (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_skew, mul_neg]

theorem continuous_symplOH (S T : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO S T} (hx : Continuous x)
    (hy : Continuous y) : Continuous fun t => symplOH S T (x t) (y t) := by
  have hy' : ∀ i j, Continuous fun t => cA D (y t i j) := fun i j =>
    ThetaCont.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hO S T (x t) (y t) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

theorem sum_reorder {A : Type} [CommRing A] {m n : ℕ} (σ : A → A) (P : Fin m → Fin m → A)
    (Q : Fin n → Fin n → A) (x y : Matrix (Fin n) (Fin m) A) :
    ∑ a, ∑ b, ∑ c, ∑ d, P a b * σ (y c b) * Q c d * x d a =
      ∑ i, ∑ j, ∑ k, ∑ l, σ (yᵀ i j) * P k i * Q j l * xᵀ k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
    simp only [Matrix.transpose_apply]; ring

theorem map_symplOH_eq_zero {B : Type} [CommRing B] [Algebra D.host.F B] (p : AF D.host.F →ₐ[D.host.F] B)
    (S T : HSp D) (x y : WO S T)
    (h : x.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0 ∨
      y.map (Algebra.TensorProduct.map p (AlgHom.id D.host.F D.host.E)).toRingHom = 0) :
    p (symplOH S T x y) = 0 := by
  have h1 : p (symplO S T x y) = 0 := by
    unfold symplO hO
    rw [sum_reorder (cA D) (fun k i => incA D (S.gram⁻¹ k i)) (fun j l => incA D (T.gram j l)) x y]
    refine map_trace_sesq_eq_zero p D.sp.cm.sig _ (fun k i => incA D (S.gram⁻¹ k i))
      (fun j l => incA D (T.gram j l)) xᵀ yᵀ (h.imp (fun h => ?_) fun h => ?_) <;>
    · ext i j
      exact congrFun (congrFun h j) i
  unfold symplOH
  rw [map_mul, h1, mul_zero]

theorem snd_symplOH (S T : HSp D) (x y : WO S T) (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplOH S T x y) = 0 := map_symplOH_eq_zero (sndA D.host.F) S T x y h

theorem fst_symplOH (S T : HSp D) (x y : WO S T) (h : x.map (infPart D) = 0 ∨ y.map (infPart D) = 0) :
    fstA D.host.F (symplOH S T x y) = 0 := map_symplOH_eq_zero (fstA D.host.F) S T x y h

theorem symplOH_fin_real (S T : HSp D) (u v : WO S T) (hu : u.map (infPart D) = 0) (hv : v.map (finPart D) = 0) :
    symplOH S T u v = 0 ∧ symplOH S T v u = 0 :=
  ⟨Prod.ext (fst_symplOH S T u v (Or.inl hu)) (snd_symplOH S T u v (Or.inr hv)),
    Prod.ext (fst_symplOH S T v u (Or.inr hu)) (snd_symplOH S T v u (Or.inl hv))⟩

theorem exists_log {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ lam : AF D.host.F →+ ℂ, Continuous lam ∧ ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  let lam : AF D.host.F →+ ℂ :=
    { toFun := fun a => 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
        ∑ ρ, θ ρ (fstA D.host.F a ⊗ₜ[D.host.F] (1 : D.host.E))
      map_zero' := by simp only [map_zero, TensorProduct.zero_tmul, Finset.sum_const_zero, mul_zero]
      map_add' := fun a b => by
        simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  refine ⟨lam, ?_, fun a ha => ?_⟩
  · exact continuous_const.mul (continuous_finset_sum _ fun ρ _ => (hθ ρ).2.comp continuous_fst)
  · have hc := hψ.2.2 θ hθ (fstA D.host.F a)
    have e : pairA D.host.F (fstA D.host.F a) 0 = a := Prod.ext rfl ha.symm
    rw [psiInf, e] at hc
    exact hc

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisO_heisO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w w' : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T w (heisO ψ S T w' f) = ψ (symplOH S T w w') • heisO ψ S T (w + w') f := by
  funext u
  simp only [heisO, Pi.smul_apply, smul_eq_mul, symplOH_add_left, symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  rw [heisO, symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem heisO_quasi (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ)
    (hf : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w) (γ w) :
    heisO ψ S T w₀ f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * heisO ψ S T w₀ f w := by
  simp only [heisO]
  rw [add_assoc, hf, symplOH_add_left, symplOH_add_right, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

theorem heisO_fix_of_real (u v : WO S T) (hu : u.map (infPart D) = 0) (hv : v.map (finPart D) = 0)
    (f : WO S T → ℂ) (hf : heisO ψ S T u f = f) : heisO ψ S T u (heisO ψ S T v f) = heisO ψ S T v f := by
  conv_rhs => rw [← hf]
  rw [heisO_heisO, heisO_heisO, (symplOH_fin_real S T u v hu hv).1, (symplOH_fin_real S T u v hu hv).2, add_comm]

theorem isTheta_zero : IsThetaFunO ψ S T 0 where
  quasi γ w := by simp only [Pi.zero_apply, mul_zero]
  level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
  cont := continuous_const
  smooth k L _ _ w := contDiff_const

theorem isTheta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
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

theorem isTheta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (c • f) where
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

theorem isTheta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  have := isTheta_add hf (isTheta_smul (-1) hg)
  rwa [neg_one_smul, ← sub_eq_add_neg] at this

variable {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem continuous_of_level (h : Chart θ σ) (hψ : Continuous ψ) (f : WO S T → ℂ)
    (hU : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f)
    (hs : Sm (iotaW σ T S) f) : Continuous f := by
  obtain ⟨U, hUo, hU⟩ := hU
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA T S) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WA T S) := IsTopologicalAddGroup.to_continuousSub
  refine continuous_iff_continuousAt.2 fun w => ?_
  let x : WA T S → RW T S := fun w' => piW θ T S (w' - w)
  let a : WA T S → WA T S := fun w' => w + iotaW σ T S (x w')
  let u : WA T S → WA T S := fun w' => w' - a w'
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
    (hψ.comp (continuous_symplOH S T ha hu).neg).mul ((hs w).continuous.comp hx)
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hU _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show ψ (-symplOH S T (a w') (u w')) * f (a w') = f w'
  rw [← e]
  show _ * (ψ (symplOH S T (a w') (u w')) * f (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

def phase (lam : AF D.host.F →+ ℂ) (S T : HSp D) (v : WO S T) : WO S T →+ ℂ where
  toFun w := lam (symplOH S T w v)
  map_zero' := by rw [symplOH_zero_left, map_zero]
  map_add' x y := by rw [symplOH_add_left, map_add]

theorem contDiff_phase (h : Chart θ σ) {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (v : WO S T) :
    ContDiff ℝ ∞ fun x => phase lam S T v (iotaW σ T S x) :=
  contDiff_additive ((phase lam S T v).comp (iotaW σ T S))
    (hl.comp (continuous_symplOH S T (h.continuous_iota T S) continuous_const))

theorem isTheta_heisO_real (hψ : IsStdChar D ψ (-1)) {v : WO S T} (hv : v.map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (heisO ψ S T v f) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hsm := (smooth_iff_sm_and_real_lines D θ σ h T S).1
  have hs : Sm (iotaW σ T S) (heisO ψ S T v f) := by
    have e : heisO ψ S T v f = fun w => Complex.exp (phase lam S T v w) * f (w + v) := by
      funext w
      rw [heisO, hlam _ (snd_symplOH S T w v (Or.inr hv))]
      rfl
    rw [e]
    exact sm_translate _ _ (contDiff_phase h hl v) f ((hsm f).1 hf.smooth) v
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (heisO ψ S T v f) = heisO ψ S T v f := by
    obtain ⟨U, hU, h1⟩ := hf.level
    exact ⟨U, hU, fun u hu h0 => heisO_fix_of_real u v h0 hv f (h1 u hu h0)⟩
  exact ⟨heisO_quasi ψ S T v f hf.quasi, hlev, continuous_of_level h hψ.1.1 _ hlev hs, (hsm _).2 hs⟩

def dLine (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (L : ℝ →+ WO S T) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun x => deriv (fun t : ℝ => heisO ψ S T (L t) f x) 0

theorem additive_real (φ : ℝ →+ ℂ) (h : Continuous φ) (t : ℝ) : φ t = t * φ 1 := by
  have := (φ.toRealLinearMap h).map_smul t 1
  rw [smul_eq_mul, mul_one] at this
  exact this

theorem psi_sympl_line {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (w : WO S T) (t : ℝ) :
    ψ (symplOH S T w (L t)) = Complex.exp (t * phase lam S T (L 1) w) := by
  rw [hlam _ (snd_symplOH S T w _ (Or.inr (hL0 t)))]
  congr 1
  let φ : ℝ →+ ℂ :=
    { toFun := fun t => lam (symplOH S T w (L t))
      map_zero' := by rw [map_zero L, symplOH_zero_right, map_zero]
      map_add' := fun x y => by rw [map_add L, symplOH_add_right, map_add] }
  exact additive_real φ (hl.comp (continuous_symplOH S T continuous_const hL)) t

theorem hasDerivAt_zero_and_isTheta (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    (∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (dLine ψ S T L f w) 0) ∧
      IsThetaFunO ψ S T (dLine ψ S T L f) := by
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hsm := (smooth_iff_sm_and_real_lines D θ σ h T S).1
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := (hsm f).1 hf.smooth
  have hd : ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1))) 0 := by
    intro w
    have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
        f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
      funext t
      rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
    rw [e]
    exact hasDerivAt_exp_mul _ _ f hfs _ w
  have hs : Sm (iotaW σ T S) (dLine ψ S T L f) := by
    have e : dLine ψ S T L f = fun w => phase lam S T (L 1) w * f w +
        fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := funext fun w => (hd w).deriv
    rw [e]
    exact sm_deriv _ _ (contDiff_phase h hl _) f hfs _
  have hlev : ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧
      ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (dLine ψ S T L f) = dLine ψ S T L f := by
    obtain ⟨U, hU, h1⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have : (fun t => heisO ψ S T (L t) f w) = fun t => heisO ψ S T u (heisO ψ S T (L t) f) w := by
      funext t; rw [heisO_fix_of_real u _ h0 (hL0 t) f (h1 u hu h0)]
    conv_rhs => unfold dLine; rw [this]
    unfold dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  refine ⟨fun w => (hd w).differentiableAt.hasDerivAt, fun γ w => ?_, hlev,
    continuous_of_level h hψ.1.1 _ hlev hs, (hsm _).2 hs⟩
  unfold dLine
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  exact heisO_quasi ψ S T (L t) f hf.quasi γ w

theorem heisO_line_add (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (s t : ℝ) (f : WO S T → ℂ) :
    heisO ψ S T (L s) (heisO ψ S T (L t) f) = heisO ψ S T (L (s + t)) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have h1 : phase lam S T (L 1) (L 1) = 0 := by
    have : phase lam S T (L 1) (L 1) = -phase lam S T (L 1) (L 1) :=
      (congrArg lam (symplOH_skew S T (L 1) (L 1))).trans (map_neg lam _)
    exact self_eq_neg.1 this
  have h2 : phase lam S T (L 1) (L s) = 0 := by
    have := additive_real ((phase lam S T (L 1)).comp L)
      (hl.comp (continuous_symplOH S T hL continuous_const)) s
    exact this.trans (mul_eq_zero_of_right _ h1)
  rw [heisO_heisO, psi_sympl_line hl hlam hL hL0, h2, mul_zero, Complex.exp_zero, one_smul, map_add]

theorem hasDerivAt_line (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) (s : ℝ) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (L t) f w) (heisO ψ S T (L s) (dLine ψ S T L f) w) s := by
  have h1 := ((hasDerivAt_zero_and_isTheta hψ hL hL0 hf).1 (w + L s)).const_mul (ψ (symplOH S T w (L s)))
  have h2 : HasDerivAt (fun t : ℝ => heisO ψ S T (L (s + t)) f w) (heisO ψ S T (L s) (dLine ψ S T L f) w) 0 := by
    refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
    exact (congrFun (heisO_line_add hψ hL hL0 s t f) w).symm
  have h3 := HasDerivAt.comp_sub_const s s (by rwa [sub_self] :
    HasDerivAt (fun t : ℝ => heisO ψ S T (L (s + t)) f w) (heisO ψ S T (L s) (dLine ψ S T L f) w) (s - s))
  simpa only [add_sub_cancel] using h3

theorem isLineAt_lineAt (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    IsLineAt θ τ z (lineAt θ τ z) :=
  Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)

theorem isTheta_dRho (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) :=
  (hasDerivAt_zero_and_isTheta hψ (isLineAt_lineAt hθ τ z).1 (isLineAt_lineAt hθ τ z).2.1 hf).2

end GlobalTheory.WeilVacMove

end
