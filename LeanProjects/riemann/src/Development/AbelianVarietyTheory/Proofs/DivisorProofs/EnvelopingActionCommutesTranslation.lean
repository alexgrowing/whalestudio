import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnvRepAllEnvIncl
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RightDerivativeAlongLieSmoothAndLinear

noncomputable section

open scoped ContDiff Topology TensorProduct

namespace GlobalTheory.EnvCommLie

open GlobalTheory.SmoothForms

section Abstract

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

def JointSm (σ : 𝔸 →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (Ψ : ℝ → G → ℂ) : Prop :=
  ∀ (g : G) (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (c : P → 𝔸), ContDiff ℝ ∞ c →
    (∀ p, σ (c p) * c p = 1) → ContDiff ℝ ∞ fun q : ℝ × P => Ψ q.1 (g * s (c q.2))

theorem unit_mul (H : IsLieData σ j s) {a b : 𝔸} (ha : σ a * a = 1) (hb : σ b * b = 1) : σ (a * b) * (a * b) = 1 := by
  rw [H.anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]

theorem s_one (H : IsLieData σ j s) : s 1 = 1 := by
  have h := H.mul 1 1 (by rw [H.one, one_mul]) (by rw [H.one, one_mul])
  rw [one_mul] at h
  exact (mul_eq_left.1 h.symm)

theorem expMap_zero (H : IsLieData σ j s) : expMap j s 0 = 1 := by
  simp only [expMap, map_zero, NormedSpace.exp_zero, s_one H]

theorem expMap_add_smul (H : IsLieData σ j s) (X : L) (t h : ℝ) :
    expMap j s ((t + h) • X) = expMap j s (t • X) * expMap j s (h • X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hb : ∀ x : 𝔸, x ∈ Metric.eball (0 : 𝔸) (NormedSpace.expSeries ℝ 𝔸).radius := fun x =>
    (NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _
  simp only [expMap]
  rw [← H.mul _ _ (DerLinear.exp_unitary H _) (DerLinear.exp_unitary H _), add_smul, map_add,
    NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) ?_ (hb _) (hb _)]
  rw [map_smul, map_smul]
  exact ((Commute.refl (j X)).smul_left t).smul_right h

theorem sm_transl (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) {b : 𝔸}
    (hb : σ b * b = 1) : Sm (expMap j s) (fun x => φ (x * s b)) := by
  intro g
  have hc : ContDiff ℝ ∞ fun Z : L => NormedSpace.exp (j Z) * b := (DerLinear.contDiff_exp H).mul contDiff_const
  have := contDiff_family H hl (fun g => (hφ g).contDiffAt) hc (fun Z => unit_mul H (DerLinear.exp_unitary H Z) hb) g
  convert this using 2 with Z
  simp only [expMap]
  rw [H.mul _ _ (DerLinear.exp_unitary H Z) hb, mul_assoc]

theorem jointSm_transl (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    JointSm σ s (fun t x => φ (x * expMap j s (t • X))) := by
  intro g P _ _ c hc hu
  have hc' : ContDiff ℝ ∞ fun q : ℝ × P => c q.2 * NormedSpace.exp (j (q.1 • X)) :=
    (hc.comp contDiff_snd).mul ((DerLinear.contDiff_exp H).comp (contDiff_fst.smul contDiff_const))
  have := contDiff_family H hl (fun g => (hφ g).contDiffAt) hc'
    (fun q => unit_mul H (hu q.2) (DerLinear.exp_unitary H _)) g
  convert this using 2 with q
  simp only [expMap]
  rw [mul_assoc, ← H.mul _ _ (hu q.2) (DerLinear.exp_unitary H _)]

theorem hasDerivAt_transl (H : IsLieData σ j s) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) (t : ℝ) (x : G) :
    HasDerivAt (fun t => φ (x * expMap j s (t • X))) (Der (expMap j s) X φ (x * expMap j s (t • X))) t := by
  have h1 : HasDerivAt (fun h : ℝ => φ (x * expMap j s (t • X) * expMap j s (h • X)))
      (Der (expMap j s) X φ (x * expMap j s (t • X))) (t - t) := by
    rw [sub_self]
    exact (Sm.differentiableAt hφ _ X).hasDerivAt
  have h2 := h1.comp_sub_const t t
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  change φ (x * expMap j s (u • X)) = φ (x * expMap j s (t • X) * expMap j s ((u - t) • X))
  rw [mul_assoc, ← expMap_add_smul H, add_sub_cancel]

omit [FiniteDimensional ℝ 𝔸] in

theorem contDiff_deriv_param {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : E × ℝ → ℂ}
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ fun q => deriv (fun r => K (q, r)) 0 := by
  have e : ∀ q, deriv (fun r => K (q, r)) 0 = fderiv ℝ K (q, 0) ((0 : E), (1 : ℝ)) := fun q =>
    ((hK.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((hasDerivAt_const (0 : ℝ) q).prodMk (hasDerivAt_id' (0 : ℝ)))).deriv
  simp_rw [e]
  exact ((hK.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

theorem jointSm_der (H : IsLieData σ j s) (Y : L) {Ψ : ℝ → G → ℂ} (hΨ : JointSm σ s Ψ) :
    JointSm σ s (fun t => Der (expMap j s) Y (Ψ t)) := by
  intro g P _ _ c hc hu
  have hc' : ContDiff ℝ ∞ fun p : P × ℝ => c p.1 * NormedSpace.exp (j (p.2 • Y)) :=
    (hc.comp contDiff_fst).mul ((DerLinear.contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hF := hΨ g (P × ℝ) _ hc' (fun p => unit_mul H (hu p.1) (DerLinear.exp_unitary H _))
  have hK : ContDiff ℝ ∞ fun q : (ℝ × P) × ℝ =>
      Ψ q.1.1 (g * s (c q.1.2 * NormedSpace.exp (j (q.2 • Y)))) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  convert contDiff_deriv_param hK using 1
  funext q
  simp only [Der, expMap]
  congr 1
  funext r
  rw [mul_assoc, H.mul _ _ (hu _) (DerLinear.exp_unitary H _)]

theorem hasDerivAt_der (H : IsLieData σ j s) (Y : L) {Ψ Ψ' : ℝ → G → ℂ} (hΨ : JointSm σ s Ψ)
    (hd : ∀ t x, HasDerivAt (fun t => Ψ t x) (Ψ' t x) t) (t : ℝ) (x : G) :
    HasDerivAt (fun t => Der (expMap j s) Y (Ψ t) x) (Der (expMap j s) Y (Ψ' t) x) t := by
  have hc : ContDiff ℝ ∞ fun r : ℝ => NormedSpace.exp (j (r • Y)) :=
    (DerLinear.contDiff_exp H).comp (contDiff_id.smul contDiff_const)
  set F : ℝ × ℝ → ℂ := fun q => Ψ q.1 (x * s (NormedSpace.exp (j (q.2 • Y)))) with hFdef
  have hF : ContDiff ℝ ∞ F := hΨ x ℝ _ hc (fun r => DerLinear.exp_unitary H _)
  have hdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hdd : Differentiable ℝ (fderiv ℝ F) := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have e1 : ∀ t', Der (expMap j s) Y (Ψ t') x = fderiv ℝ F (t', 0) ((0 : ℝ), (1 : ℝ)) := fun t' =>
    ((hdiff _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) t').prodMk (hasDerivAt_id' (0 : ℝ)))).deriv
  have e2 : ∀ t' r, Ψ' t' (x * expMap j s (r • Y)) = fderiv ℝ F (t', r) ((1 : ℝ), (0 : ℝ)) := fun t' r =>
    (hd t' _).unique ((hdiff _).hasFDerivAt.comp_hasDerivAt t' ((hasDerivAt_id' t').prodMk (hasDerivAt_const t' r)))
  have e3 : Der (expMap j s) Y (Ψ' t) x = fderiv ℝ (fderiv ℝ F) (t, 0) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := by
    have : (fun r => Ψ' t (x * expMap j s (r • Y))) = fun r => fderiv ℝ F (t, r) ((1 : ℝ), (0 : ℝ)) := funext (e2 t)
    change deriv (fun r => Ψ' t (x * expMap j s (r • Y))) 0 = _
    rw [this]
    have h := (hdd _).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id' (0 : ℝ)))
    have h2 := h.clm_apply (hasDerivAt_const (0 : ℝ) ((1 : ℝ), (0 : ℝ)))
    simpa using h2.deriv
  have hL : HasDerivAt (fun t' => fderiv ℝ F (t', 0) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ F) (t, 0) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
    have h := (hdd _).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t (0 : ℝ)))
    simpa using h.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ)))
  have hsym := (hF.contDiffAt (x := (t, (0 : ℝ)))).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2:ℕ∞) ≤ ⊤))
  rw [e3, ← hsym ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))]
  exact hL.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t' => e1 t')

def GoodOp (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G) (A : Module.End ℂ (smSub (expMap j s))) : Prop :=
  ∀ Ψ Ψ' : ℝ → smSub (expMap j s), JointSm σ s (fun t => (Ψ t).1) → JointSm σ s (fun t => (Ψ' t).1) →
    (∀ t x, HasDerivAt (fun t => (Ψ t).1 x) ((Ψ' t).1 x) t) →
    JointSm σ s (fun t => (A (Ψ t)).1) ∧ JointSm σ s (fun t => (A (Ψ' t)).1) ∧
      ∀ t x, HasDerivAt (fun t => (A (Ψ t)).1 x) ((A (Ψ' t)).1 x) t

theorem goodOp_derOp (H : IsLieData σ j s) (hl : HasLog σ j) (Y : L) : GoodOp σ j s (derOp H hl Y) :=
  fun _ _ h1 h2 h3 => ⟨jointSm_der H Y h1, jointSm_der H Y h2, hasDerivAt_der H Y h1 h3⟩

theorem goodOp_algebraMap (c : ℂ) : GoodOp σ j s (algebraMap ℂ (Module.End ℂ (smSub (expMap j s))) c) := by
  intro Ψ Ψ' h1 h2 h3
  simp only [Module.algebraMap_end_apply, Submodule.coe_smul]
  exact ⟨fun g P _ _ c' hc hu => (h1 g P c' hc hu).const_smul c, fun g P _ _ c' hc hu => (h2 g P c' hc hu).const_smul c,
    fun t x => (h3 t x).const_smul c⟩

theorem goodOp_add {A B : Module.End ℂ (smSub (expMap j s))} (hA : GoodOp σ j s A) (hB : GoodOp σ j s B) :
    GoodOp σ j s (A + B) := by
  intro Ψ Ψ' h1 h2 h3
  obtain ⟨a1, a2, a3⟩ := hA Ψ Ψ' h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := hB Ψ Ψ' h1 h2 h3
  simp only [LinearMap.add_apply, Submodule.coe_add]
  exact ⟨fun g P _ _ c hc hu => (a1 g P c hc hu).add (b1 g P c hc hu),
    fun g P _ _ c hc hu => (a2 g P c hc hu).add (b2 g P c hc hu), fun t x => (a3 t x).add (b3 t x)⟩

theorem goodOp_mul {A B : Module.End ℂ (smSub (expMap j s))} (hA : GoodOp σ j s A) (hB : GoodOp σ j s B) :
    GoodOp σ j s (A * B) := by
  intro Ψ Ψ' h1 h2 h3
  obtain ⟨b1, b2, b3⟩ := hB Ψ Ψ' h1 h2 h3
  exact hA (fun t => B (Ψ t)) (fun t => B (Ψ' t)) b1 b2 b3

theorem goodOp_of_mem (H : IsLieData σ j s) (hl : HasLog σ j) {A : Module.End ℂ (smSub (expMap j s))}
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (derOp H hl))) : GoodOp σ j s A := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨Y, rfl⟩ := hx; exact goodOp_derOp H hl Y
  | algebraMap c => exact goodOp_algebraMap c
  | add x y _ _ hx hy => exact goodOp_add hx hy
  | mul x y _ _ hx hy => exact goodOp_mul hx hy

theorem comm_of_transl (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) {A : Module.End ℂ (smSub (expMap j s))}
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (derOp H hl)))
    (htr : ∀ (t : ℝ) (φ : smSub (expMap j s)) (h : (fun x => φ.1 (x * expMap j s (t • X))) ∈ smSub (expMap j s)),
      (A ⟨_, h⟩).1 = fun x => (A φ).1 (x * expMap j s (t • X))) :
    derOp H hl X * A = A * derOp H hl X := by
  have hG : GoodOp σ j s A := goodOp_of_mem H hl hA
  refine LinearMap.ext fun φ => Subtype.ext (funext fun g => ?_)
  have mem : ∀ (ψ : smSub (expMap j s)) (t : ℝ), (fun x => ψ.1 (x * expMap j s (t • X))) ∈ smSub (expMap j s) :=
    fun ψ t => sm_transl H hl ψ.2 (DerLinear.exp_unitary H (t • X))
  let Ψ : ℝ → smSub (expMap j s) := fun t => ⟨_, mem φ t⟩
  let Ψ' : ℝ → smSub (expMap j s) := fun t => ⟨_, mem (derOp H hl X φ) t⟩
  have hd : ∀ t x, HasDerivAt (fun t => (Ψ t).1 x) ((Ψ' t).1 x) t := fun t x => hasDerivAt_transl H φ.2 X t x
  obtain ⟨-, -, h3⟩ := hG Ψ Ψ' (jointSm_transl H hl φ.2 X) (jointSm_transl H hl (derOp H hl X φ).2 X) hd
  have h4 := h3 0 g
  have e0 : Ψ' 0 = derOp H hl X φ := Subtype.ext (funext fun x => by
    change (derOp H hl X φ).1 (x * expMap j s ((0 : ℝ) • X)) = _
    rw [zero_smul, expMap_zero H, mul_one])
  rw [e0] at h4
  have h5 : (fun t => (A (Ψ t)).1 g) = fun t => (A φ).1 (g * expMap j s (t • X)) :=
    funext fun t => congrFun (htr t φ (mem φ t)) g
  rw [h5] at h4
  have h6 : HasDerivAt (fun t : ℝ => (A φ).1 (g * expMap j s (t • X))) ((derOp H hl X (A φ)).1 g) 0 :=
    (Sm.differentiableAt (A φ).2 g X).hasDerivAt
  exact h6.unique h4

end Abstract

section Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

open Classical in

theorem envRepAll_ι_of_tmul (R : RealPoints θ V) (τ : D.what₂.Tau) (c : ℂ) (X : LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ (c ⊗ₜ X))) =
      c • opInf R (atPlace V τ X) := by
  rw [← envIncl_ι, envRepAll_envIncl]
  have : c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul, map_smul, envRep_ι]

open Classical in
theorem envRepAll_ι_mem (R : RealPoints θ V) (x : GlobalTheory.AutFinLit.LieC V) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) ∈ Algebra.adjoin ℂ (Set.range (opInf R)) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | of τ y =>
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
    | tmul c X => rw [envRepAll_ι_of_tmul]; exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self _)) c
    | add a b ha hb => rw [map_add, map_add, map_add]; exact add_mem ha hb
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

theorem envRepAll_mem (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) :
    envRepAll R u ∈ Algebra.adjoin ℂ (Set.range (opInf R)) := by
  have hs : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (GlobalTheory.AutFinLit.LieC V)) :=
    by unfold UniversalEnvelopingAlgebra.mkAlgHom; exact RingCon.mkₐ_surjective _
  obtain ⟨w, rfl⟩ := hs u
  induction w using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
  | ι x => rw [← UniversalEnvelopingAlgebra.ι_apply]; exact envRepAll_ι_mem R x
  | mul a b ha hb => rw [map_mul, map_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb

end Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
attribute [local instance 100] LieRing.ofAssociativeRing in

theorem envRepAll_comm_lie : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V), (∀ a ∈ GinfC V, ∀ (f : SmF θ V)
      (hfa : (fun x => f.1 (x * a)) ∈ SmF θ V), (envRepAll R u ⟨_, hfa⟩).1 = fun x => (envRepAll R u f).1 (x * a)) →
    ∀ x : GlobalTheory.AutFinLit.LieC V, envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) * envRepAll R u =
      envRepAll R u * envRepAll R (UniversalEnvelopingAlgebra.ι ℂ x) := by
  intro D θ _ V R u hu x
  have hcomm : ∀ τ (X : LieAt V τ),
      opInf R (atPlace V τ X) * envRepAll R u = envRepAll R u * opInf R (atPlace V τ X) := fun τ X =>
    comm_of_transl (isLieData R) (hasLog R) (atPlace V τ X) (envRepAll_mem R u) fun t φ h =>
      hu _ (isExpFam_expInf R (t • atPlace V τ X)).1 φ h
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of τ y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c X => rw [envRepAll_ι_of_tmul, smul_mul_assoc, mul_smul_comm, hcomm]
    | add a b ha hb => rw [map_add, map_add, map_add, add_mul, mul_add, ha, hb]
  | add a b ha hb => rw [map_add, map_add, add_mul, mul_add, ha, hb]

end GlobalTheory.EnvCommLie
