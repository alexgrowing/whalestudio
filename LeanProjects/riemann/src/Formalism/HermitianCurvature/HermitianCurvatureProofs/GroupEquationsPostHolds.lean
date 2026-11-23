import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliCoordinates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section post

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def gpMulR (X : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def gpMulL (X : B.Mat k r) : B.Mat k r →L[ℝ] B.Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

theorem gpMulR_apply (X Y : B.Mat k r) : gpMulR X Y = Y * X := by
  simp [gpMulR]

theorem gpMulL_apply (X Y : B.Mat k r) : gpMulL X Y = X * Y := by
  simp [gpMulL]

theorem gp_rdV (X g : B.Mat k r) (f : B.Mat k r → E) (hf : DifferentiableAt ℝ f g) :
    Formalism.REAL.RdV X f g = fderiv ℝ f g (g * X) := by
  have hγ := B5.curve_hasDerivAt g X 0
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  rw [h0] at hγ
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm).deriv

theorem gp_ldV (X g : B.Mat k r) (f : B.Mat k r → E) (hf : DifferentiableAt ℝ f g) :
    Q.LdV X f g = fderiv ℝ f g (X * g) := by
  have hγ : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) (X * g) 0 := by
    have h1 := (gpMulR g).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (B5.curve_hasDerivAt (1 : B.Mat k r) X 0)
    have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) * g) =
        (⇑(gpMulR g) ∘ fun t : ℝ => (1 : B.Mat k r) * NormedSpace.exp ((t : ℂ) • X)) := by
      funext t; simp [gpMulR_apply]
    have e2 : gpMulR g (1 * NormedSpace.exp (((0 : ℝ) : ℂ) • X) * X) = X * g := by
      simp [gpMulR_apply]
    rw [e, ← e2]
    exact h1
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g = g := by simp
  exact (hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ h0.symm).deriv

theorem gp_fderiv_post (ℓ : E →L[ℂ] ℂ) (f : B.Mat k r → E) (g : B.Mat k r) (hf : DifferentiableAt ℝ f g)
    (v : B.Mat k r) : fderiv ℝ (fun x => ℓ (f x)) g v = ℓ (fderiv ℝ f g v) := by
  have h : HasFDerivAt (fun x => ℓ (f x)) ((ℓ.restrictScalars ℝ).comp (fderiv ℝ f g)) g :=
    (ℓ.restrictScalars ℝ).hasFDerivAt.comp g hf.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem gp_cd (A : B.Mat k r →L[ℝ] B.Mat k r) (m : ℕ) (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun g => fderiv ℝ f g (A g)) :=
  (hf.fderiv_right (by norm_cast)).clm_apply A.contDiff

theorem gp_RZ (ℓ : E →L[ℂ] ℂ) (H Z : B.Mat k r) (m : ℕ) (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (m : WithTop ℕ∞) (Q.RZ H Z f) ∧ (fun g => ℓ (Q.RZ H Z f g)) = Q.RZ H Z (fun g => ℓ (f g)) := by
  have hd : ∀ g, DifferentiableAt ℝ f g := fun g => hf.differentiable (by simp) g
  have hdl : ∀ g, DifferentiableAt ℝ (fun x => ℓ (f x)) g :=
    fun g => (ℓ.restrictScalars ℝ).differentiableAt.comp g (hd g)
  have e : Q.RZ H Z f = fun g => fderiv ℝ f g (gpMulR (hpart1 H Z) g) +
      Complex.I • fderiv ℝ f g (gpMulR (hpart2 H Z) g) := by
    funext g
    simp only [Q.RZ, gpMulR_apply]
    rw [gp_rdV _ _ f (hd g), gp_rdV _ _ f (hd g)]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (gp_cd _ m f hf).add ((gp_cd _ m f hf).const_smul Complex.I)
  · funext g
    simp only [Q.RZ]
    rw [gp_rdV _ _ _ (hdl g), gp_rdV _ _ _ (hdl g), gp_rdV _ _ f (hd g), gp_rdV _ _ f (hd g),
      gp_fderiv_post ℓ f g (hd g), gp_fderiv_post ℓ f g (hd g), map_add, map_smul]

theorem gp_LZ (ℓ : E →L[ℂ] ℂ) (H Z : B.Mat k r) (m : ℕ) (f : B.Mat k r → E)
    (hf : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (m : WithTop ℕ∞) (Q.LZ H Z f) ∧ (fun g => ℓ (Q.LZ H Z f g)) = Q.LZ H Z (fun g => ℓ (f g)) := by
  have hd : ∀ g, DifferentiableAt ℝ f g := fun g => hf.differentiable (by simp) g
  have hdl : ∀ g, DifferentiableAt ℝ (fun x => ℓ (f x)) g :=
    fun g => (ℓ.restrictScalars ℝ).differentiableAt.comp g (hd g)
  have e : Q.LZ H Z f = fun g => fderiv ℝ f g (gpMulL (hpart1 H Z) g) +
      Complex.I • fderiv ℝ f g (gpMulL (hpart2 H Z) g) := by
    funext g
    simp only [Q.LZ, gpMulL_apply]
    rw [gp_ldV _ _ f (hd g), gp_ldV _ _ f (hd g)]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (gp_cd _ m f hf).add ((gp_cd _ m f hf).const_smul Complex.I)
  · funext g
    simp only [Q.LZ]
    rw [gp_ldV _ _ _ (hdl g), gp_ldV _ _ _ (hdl g), gp_ldV _ _ f (hd g), gp_ldV _ _ f (hd g),
      gp_fderiv_post ℓ f g (hd g), gp_fderiv_post ℓ f g (hd g), map_add, map_smul]

def gpLtr {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {m : ℕ}
    (Eop : Fin m → Fin m → (B.Mat k r → E') → B.Mat k r → E') (q : ℂ × Fin m × Fin m)
    (y : B.Mat k r → E') : B.Mat k r → E' :=
  q.1 • y + Eop q.2.1 q.2.2 y

theorem gp_ofFn {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {m t : ℕ}
    (Eop : Fin m → Fin m → (B.Mat k r → E') → B.Mat k r → E') (a b : Fin t → Fin m) (u : ℂ)
    (σ : Equiv.Perm (Fin t)) :
    (List.ofFn fun j : Fin t => fun y : B.Mat k r → E' =>
      (if a (σ j) = b j then (u - ((j : ℕ) : ℂ)) • y else 0) + Eop (a (σ j)) (b j) y) =
    (List.ofFn fun j : Fin t => ((if a (σ j) = b j then u - ((j : ℕ) : ℂ) else 0), a (σ j), b j)).map
      (gpLtr Eop) := by
  rw [List.map_ofFn]
  congr 1
  funext j y
  simp only [Function.comp, gpLtr]
  split_ifs <;> simp

variable {m : ℕ}

theorem gp_foldr (ℓ : E →L[ℂ] ℂ) (EopE : Fin m → Fin m → (B.Mat k r → E) → B.Mat k r → E)
    (EopC : Fin m → Fin m → (B.Mat k r → ℂ) → B.Mat k r → ℂ)
    (h : ∀ a b (j : ℕ) (f : B.Mat k r → E), ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) (EopE a b f) ∧
        (fun g => ℓ (EopE a b f g)) = EopC a b (fun g => ℓ (f g))) :
    ∀ (qs : List (ℂ × Fin m × Fin m)) (j : ℕ) (f : B.Mat k r → E),
      ContDiff ℝ ((j + qs.length : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) ((qs.map (gpLtr EopE)).foldr (fun T h => T h) f) ∧
      (fun g => ℓ ((qs.map (gpLtr EopE)).foldr (fun T h => T h) f g)) =
        (qs.map (gpLtr EopC)).foldr (fun T h => T h) (fun g => ℓ (f g))
  | [], j, f, hf => ⟨by simpa using hf, rfl⟩
  | q :: qs, j, f, hf => by
    have hf' : ContDiff ℝ ((j + 1 + qs.length : ℕ) : WithTop ℕ∞) f := by
      have e : j + 1 + qs.length = j + (q :: qs).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    obtain ⟨h1, h2⟩ := gp_foldr ℓ EopE EopC h qs (j + 1) f hf'
    simp only [List.map_cons, List.foldr_cons]
    set F := (qs.map (gpLtr EopE)).foldr (fun T h => T h) f
    obtain ⟨h3, h4⟩ := h q.2.1 q.2.2 j F h1
    refine ⟨?_, ?_⟩
    · exact ((h1.of_le (by norm_cast; omega)).const_smul q.1).add h3
    · rw [← h2]
      funext g
      have h5 : ℓ (EopE q.2.1 q.2.2 F g) = EopC q.2.1 q.2.2 (fun g => ℓ (F g)) g := congrFun h4 g
      simp only [gpLtr, Pi.add_apply, Pi.smul_apply, map_add, map_smul]
      rw [h5]

theorem gp_foldl (ℓ : E →L[ℂ] ℂ) (EopE : Fin m → Fin m → (B.Mat k r → E) → B.Mat k r → E)
    (EopC : Fin m → Fin m → (B.Mat k r → ℂ) → B.Mat k r → ℂ)
    (h : ∀ a b (j : ℕ) (f : B.Mat k r → E), ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) (EopE a b f) ∧
        (fun g => ℓ (EopE a b f g)) = EopC a b (fun g => ℓ (f g))) :
    ∀ (qs : List (ℂ × Fin m × Fin m)) (j : ℕ) (f : B.Mat k r → E),
      ContDiff ℝ ((j + qs.length : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) ((qs.map (gpLtr EopE)).foldl (fun h T => T h) f) ∧
      (fun g => ℓ ((qs.map (gpLtr EopE)).foldl (fun h T => T h) f g)) =
        (qs.map (gpLtr EopC)).foldl (fun h T => T h) (fun g => ℓ (f g))
  | [], j, f, hf => ⟨by simpa using hf, rfl⟩
  | q :: qs, j, f, hf => by
    have hf' : ContDiff ℝ ((j + qs.length + 1 : ℕ) : WithTop ℕ∞) f := by
      have e : j + qs.length + 1 = j + (q :: qs).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    obtain ⟨h3, h4⟩ := h q.2.1 q.2.2 (j + qs.length) f hf'
    have h1 : ContDiff ℝ ((j + qs.length : ℕ) : WithTop ℕ∞) (gpLtr EopE q f) :=
      ((hf'.of_le (by norm_cast; omega)).const_smul q.1).add h3
    have hq : (fun g => ℓ (gpLtr EopE q f g)) = gpLtr EopC q (fun g => ℓ (f g)) := by
      funext g
      have h5 : ℓ (EopE q.2.1 q.2.2 f g) = EopC q.2.1 q.2.2 (fun g => ℓ (f g)) g := congrFun h4 g
      simp only [gpLtr, Pi.add_apply, Pi.smul_apply, map_add, map_smul]
      rw [h5]
    obtain ⟨h6, h7⟩ := gp_foldl ℓ EopE EopC h qs j _ h1
    simp only [List.map_cons, List.foldl_cons]
    refine ⟨h6, ?_⟩
    rw [h7, hq]

theorem gp_qmF (ℓ : E →L[ℂ] ℂ) (EopE : Fin m → Fin m → (B.Mat k r → E) → B.Mat k r → E)
    (EopC : Fin m → Fin m → (B.Mat k r → ℂ) → B.Mat k r → ℂ)
    (h : ∀ a b (j : ℕ) (f : B.Mat k r → E), ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) (EopE a b f) ∧
        (fun g => ℓ (EopE a b f g)) = EopC a b (fun g => ℓ (f g)))
    {t : ℕ} (a b : Fin t → Fin m) (u : ℂ) (f : B.Mat k r → E) (hf : ContDiff ℝ (t : WithTop ℕ∞) f) :
    (fun g => ℓ (Q.qmF EopE a b u f g)) = Q.qmF EopC a b u (fun g => ℓ (f g)) := by
  funext g
  simp only [Q.qmF, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [gp_ofFn EopE a b u σ, gp_ofFn EopC a b u σ]
  exact congrFun (gp_foldr ℓ EopE EopC h _ 0 f (by simpa using hf)).2 g

theorem gp_qmFrev (ℓ : E →L[ℂ] ℂ) (EopE : Fin m → Fin m → (B.Mat k r → E) → B.Mat k r → E)
    (EopC : Fin m → Fin m → (B.Mat k r → ℂ) → B.Mat k r → ℂ)
    (h : ∀ a b (j : ℕ) (f : B.Mat k r → E), ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (j : WithTop ℕ∞) (EopE a b f) ∧
        (fun g => ℓ (EopE a b f g)) = EopC a b (fun g => ℓ (f g)))
    {t : ℕ} (a b : Fin t → Fin m) (u : ℂ) (f : B.Mat k r → E) (hf : ContDiff ℝ (t : WithTop ℕ∞) f) :
    (fun g => ℓ (Q.qmFrev EopE a b u f g)) = Q.qmFrev EopC a b u (fun g => ℓ (f g)) := by
  funext g
  simp only [Q.qmFrev, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [gp_ofFn EopE a b u σ, gp_ofFn EopC a b u σ]
  exact congrFun (gp_foldl ℓ EopE EopC h _ 0 f (by simpa using hf)).2 g

theorem gp_capR_post (ℓ : E →L[ℂ] ℂ) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (f : B.Mat k r → E)
    (hf : ContDiff ℝ (m : WithTop ℕ∞) f) :
    (fun g => ℓ (Q.capR k r Bs w f g)) = Q.capR k r Bs w (fun g => ℓ (f g)) := by
  unfold Q.capR
  exact gp_qmF ℓ (fun a b => Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs a b))
    (fun a b => Q.RZ (Hpk k r) (Q.unitB (Hpk k r) Bs a b))
    (fun a b j f hf => gp_RZ ℓ (Hpk k r) (Q.unitB (Hpk k r) Bs a b) j f hf) id id w f hf

theorem gp_capLft_post (ℓ : E →L[ℂ] ℂ) (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (f : B.Mat k r → E)
    (hf : ContDiff ℝ (m : WithTop ℕ∞) f) :
    (fun g => ℓ (Q.capLft k r Bs w f g)) = Q.capLft k r Bs w (fun g => ℓ (f g)) := by
  unfold Q.capLft
  exact gp_qmFrev ℓ (fun a b => Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs a b))
    (fun a b => Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs a b))
    (fun a b j f hf => gp_LZ ℓ (Hpk k r) (Q.unitB (Hpk k r) Bs a b) j f hf) id id w f hf

end post

section loc

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem gp_glev0 {x : B.Mat k r} (hx : x ∈ B.GV k r) : x ∈ Q.Glev k r 0 :=
  ⟨hx, fun _ ha => absurd ha (Nat.not_lt_zero _)⟩

theorem gp_gv_mul {g h : B.Mat k r} (hg : g ∈ B.GV k r) (hh : h ∈ B.GV k r) : g * h ∈ B.GV k r :=
  (Qx8.glev_mul (gp_glev0 hg) (gp_glev0 hh)).1

theorem gp_rd_loc {f f₂ : B.Mat k r → E} {V : Set (B.Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ B.GV k r → f x = f₂ x) {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r))
    {g : B.Mat k r} (hg : g ∈ B.GV k r) (hgV : g ∈ V) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f₂ g := by
  unfold Formalism.REAL.RdV
  apply Filter.EventuallyEq.deriv_eq
  have hc : ContinuousAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 :=
    (B5.curve_hasDerivAt g X 0).continuousAt
  have h0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  filter_upwards [hc.preimage_mem_nhds (by rw [h0]; exact hV.mem_nhds hgV)] with t ht
  exact h _ ht (gp_gv_mul hg (hX t).1)

theorem gp_ld_loc {f f₂ : B.Mat k r → E} {V : Set (B.Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ B.GV k r → f x = f₂ x) {X : B.Mat k r} (hX : X ∈ JfS.lieOf (Nset k r))
    {g : B.Mat k r} (hg : g ∈ B.GV k r) (hgV : g ∈ V) : Q.LdV X f g = Q.LdV X f₂ g := by
  unfold Q.LdV
  apply Filter.EventuallyEq.deriv_eq
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) * g = g := by simp
  filter_upwards [(Qx8.lcurve_cont X g).continuousAt.preimage_mem_nhds (by rw [h0]; exact hV.mem_nhds hgV)]
    with t ht
  exact h _ ht (gp_gv_mul (hX t).1 hg)

theorem gp_glob {n : ℕ} {J : B.Mat k r → E} {U : Set (B.Mat k r)} {F : B.Mat k r → E} {g : B.Mat k r}
    (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ (n : WithTop ℕ∞) F U)
    (hJF : ∀ x ∈ U, x ∈ Q.Glev k r 0 → J x = F x) :
    ∃ (V : Set (B.Mat k r)) (J' : B.Mat k r → E), IsOpen V ∧ g ∈ V ∧ ContDiff ℝ (n : WithTop ℕ∞) J' ∧
      ∀ x ∈ V, x ∈ Q.Glev k r 0 → J x = J' x := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU g hgU
  let b : ContDiffBump g := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  refine ⟨Metric.ball g (ρ / 4), fun x => (b x : ℝ) • F x, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_, fun x hx hxG => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall g (ρ / 2)
    · have hxU : x ∈ U := hball (Metric.closedBall_subset_ball (by linarith) hx)
      exact b.contDiff.contDiffAt.smul (hF.contDiffAt (hU.mem_nhds hxU))
    · have : (fun x => (b x : ℝ) • F x) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        have : b y = 0 := by
          rw [← Function.notMem_support, b.support_eq]
          exact fun h => hy (Metric.ball_subset_closedBall h)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq this
  · have h1 : b x = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
    have h2 : x ∈ U := hball (Metric.ball_subset_ball (by linarith) hx)
    simp [h1, hJF x h2 hxG]

end loc

theorem group_equations_post_holds : GEqsPost := by
  intro k r z z' E _ _ J ℓ hG
  obtain ⟨hC, hR1, hL1, hCl, hCr, hCV⟩ := hG
  have loc : ∀ g ∈ JF.Om k r z z', ∃ (V : Set (B.Mat k r)) (J' : B.Mat k r → E), IsOpen V ∧ g ∈ V ∧
      ContDiff ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) J' ∧ ∀ x ∈ V, x ∈ Q.Glev k r 0 → J x = J' x := by
    intro g hg
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hC g ⟨gp_glev0 hg.1, hg.2⟩
    exact gp_glob hU hgU hF hJF
  have hd : ∀ (J' : B.Mat k r → E), ContDiff ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) J' → ∀ g,
      DifferentiableAt ℝ J' g := fun J' h g => h.differentiable (by simp) g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hC g₀ hg₀
    exact ⟨U, fun x => ℓ (F x), hU, hgU, (ℓ.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
      fun x hx hxG => by simp [hJF x hx hxG]⟩
  · intro X hX
    obtain ⟨c, hc⟩ := hR1 X hX
    refine ⟨c, fun g hg => ?_⟩
    obtain ⟨V, J', hV, hgV, hJ', hJJ'⟩ := loc g hg
    have hdl : DifferentiableAt ℝ (fun x => ℓ (J' x)) g :=
      (ℓ.restrictScalars ℝ).differentiableAt.comp g (hd J' hJ' g)
    rw [gp_rd_loc (f₂ := fun x => ℓ (J' x)) hV (fun x hx hxG => by simp [hJJ' x hx (gp_glev0 hxG)]) hX hg.1 hgV,
      gp_rdV X g _ hdl, gp_fderiv_post ℓ J' g (hd J' hJ' g), ← gp_rdV X g J' (hd J' hJ' g),
      ← gp_rd_loc hV (fun x hx hxG => hJJ' x hx (gp_glev0 hxG)) hX hg.1 hgV, hc g hg, map_smul]
  · intro X hX
    obtain ⟨c, hc⟩ := hL1 X hX
    refine ⟨c, fun g hg => ?_⟩
    obtain ⟨V, J', hV, hgV, hJ', hJJ'⟩ := loc g hg
    have hdl : DifferentiableAt ℝ (fun x => ℓ (J' x)) g :=
      (ℓ.restrictScalars ℝ).differentiableAt.comp g (hd J' hJ' g)
    rw [gp_ld_loc (f₂ := fun x => ℓ (J' x)) hV (fun x hx hxG => by simp [hJJ' x hx (gp_glev0 hxG)]) hX hg.1 hgV,
      gp_ldV X g _ hdl, gp_fderiv_post ℓ J' g (hd J' hJ' g), ← gp_ldV X g J' (hd J' hJ' g),
      ← gp_ld_loc hV (fun x hx hxG => hJJ' x hx (gp_glev0 hxG)) hX hg.1 hgV, hc g hg, map_smul]
  · intro Bs hBs w
    obtain ⟨c, hc⟩ := hCl Bs hBs w
    refine ⟨c, fun g hg => ?_⟩
    obtain ⟨V, J', hV, hgV, hJ', hJJ'⟩ := loc g hg
    have hgx : g ∈ Q.Glev k r 0 ∩ V := ⟨gp_glev0 hg.1, hgV⟩
    have l1 := Qx8.loc_capLft (E := ℂ) (i := 0) hV Bs hBs.1 w (fun x => ℓ (J x)) (fun x => ℓ (J' x))
      (fun x hx => by simp [hJJ' x hx.2 hx.1]) g hgx
    have l2 := Qx8.loc_capLft (E := E) (i := 0) hV Bs hBs.1 w J J' (fun x hx => hJJ' x hx.2 hx.1) g hgx
    have hp := congrFun (gp_capLft_post ℓ Bs w J' (hJ'.of_le (by norm_cast; omega))) g
    rw [l1, ← hp, ← l2, hc g hg, map_smul]
  · intro Bs hBs w
    obtain ⟨c, hc⟩ := hCr Bs hBs w
    refine ⟨c, fun g hg => ?_⟩
    obtain ⟨V, J', hV, hgV, hJ', hJJ'⟩ := loc g hg
    have hgx : g ∈ Q.Glev k r 0 ∩ V := ⟨gp_glev0 hg.1, hgV⟩
    have l1 := (CapelliCoordinates.good_capR (E := ℂ) (i := 0) hV Bs hBs.1 w).loc (fun x => ℓ (J x)) (fun x => ℓ (J' x))
      (fun x hx => by simp [hJJ' x hx.2 hx.1]) g hgx
    have l2 := (CapelliCoordinates.good_capR (E := E) (i := 0) hV Bs hBs.1 w).loc J J' (fun x hx => hJJ' x hx.2 hx.1) g hgx
    have hp := congrFun (gp_capR_post ℓ Bs w J' (hJ'.of_le (by norm_cast; omega))) g
    rw [l1, ← hp, ← l2, hc g hg, map_smul]
  · intro Y
    obtain ⟨c, hc⟩ := hCV Y
    refine ⟨c, fun g hg => ?_⟩
    obtain ⟨V, J', hV, hgV, hJ', hJJ'⟩ := loc g hg
    have hgx : g ∈ Q.Glev k r 0 ∩ V := ⟨gp_glev0 hg.1, hgV⟩
    have l1 : Q.CV k r (Y : ℂ) (fun x => ℓ (J x)) g = Q.CV k r (Y : ℂ) (fun x => ℓ (J' x)) g :=
      (Qx2.good_qminor (E := ℂ) (i := 0) hV id id (Q.uC k r 0 (Y : ℂ))).loc (fun x => ℓ (J x))
        (fun x => ℓ (J' x)) (fun x hx => by simp [hJJ' x hx.2 hx.1]) g hgx
    have l2 : Q.CV k r (Y : ℂ) J g = Q.CV k r (Y : ℂ) J' g :=
      (Qx2.good_qminor (E := E) (i := 0) hV id id (Q.uC k r 0 (Y : ℂ))).loc J J'
        (fun x hx => hJJ' x hx.2 hx.1) g hgx
    have hck : B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) J' :=
      fun _ _ => ⟨Set.univ, J', isOpen_univ, trivial, by exact_mod_cast hJ'.contDiffOn, fun _ _ _ => rfl⟩
    rw [l1, JFxB.cvPost k r E ℂ (Y : ℂ) ℓ J' hck g hg.1, ← l2, hc g hg, map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
