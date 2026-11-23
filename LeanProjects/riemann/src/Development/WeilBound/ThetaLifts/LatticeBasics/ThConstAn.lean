import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n' d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

local instance borelU {J : Matrix (Fin n) (Fin n) E} : BorelSpace (UA σ J) := ⟨rfl⟩

local instance topU {J : Matrix (Fin n) (Fin n) E} : IsTopologicalGroup (UA σ J) :=
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  Subgroup.instIsTopologicalGroupSubtypeMem _

def Ker (θ : UA σ X.J → UA σ W.J → ℂ) : Prop :=
  Continuous (fun x : UA σ X.J × UA σ W.J => θ x.1 x.2) ∧
    (∀ γ ∈ ratU σ X.J, ∀ γ' ∈ ratU σ W.J, ∀ g h, θ (γ * g) (γ' * h) = θ g h) ∧
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖θ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k

variable {θ : UA σ X.J → UA σ W.J → ℂ} {φ : UA σ W.J → ℂ} {μ : Measure (UA σ W.J)} {D : Set (UA σ W.J)}

theorem Ker.bd (hθ : Ker θ) (hφ : IsRapid φ) : ∃ (K : ℝ) (k : ℕ), 0 ≤ K ∧ ∀ g h, ‖φ h * star (θ g h)‖ ≤ K * (ht g : ℝ) ^ k := by
  obtain ⟨-, hi, C, k, hC⟩ := hθ
  obtain ⟨C', hC'⟩ := hφ.2.2 k
  have h0 : 0 ≤ C' := le_trans (by positivity) (hC' 1)
  refine ⟨|C| * C', k, by positivity, fun g h => ?_⟩
  have h1 : ‖θ g h‖ ≤ |C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k := by
    have := Monotone.map_ciInf_of_continuousAt (f := fun x : ℝ≥0 => |C| * (ht g : ℝ) ^ k * (x : ℝ) ^ k)
      (g := fun γ : ratU σ W.J => ht (γ.1 * h)) (by fun_prop) (fun x y hxy => by
        have : (x : ℝ) ≤ y := hxy
        dsimp only; gcongr) (OrderBot.bddBelow _)
    refine le_of_le_of_eq (le_ciInf fun γ => ?_) this.symm
    rw [← hi 1 (one_mem _) γ.1 γ.2, one_mul, mul_assoc, ← mul_pow]
    exact (hC _ _).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [norm_mul, norm_star]
  calc _ ≤ ‖φ h‖ * (|C| * (ht g : ℝ) ^ k * (qht h : ℝ) ^ k) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = |C| * (ht g : ℝ) ^ k * (‖φ h‖ * (qht h : ℝ) ^ k) := by ring
    _ ≤ |C| * (ht g : ℝ) ^ k * C' := mul_le_mul_of_nonneg_left (hC' h) (by positivity)
    _ = _ := by ring

theorem Ker.meas (hθ : Ker θ) (hφ : IsRapid φ) (g) : AEStronglyMeasurable (fun h => φ h * star (θ g h)) (μ.restrict D) :=
  (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable

theorem Ker.int (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) (g) : IntegrableOn (fun h => φ h * star (θ g h)) D μ := by
  obtain ⟨K, k, -, hK⟩ := hθ.bd hφ
  exact Measure.integrableOn_of_bounded hD.ne (hφ.1.mul (hθ.1.comp (Continuous.prodMk_right g)).star).aestronglyMeasurable
    (Eventually.of_forall (hK g))

theorem Ker.cont [LocallyCompactSpace (UA σ X.J)] [FirstCountableTopology (UA σ X.J)]
    (hb : ∀ Ω : Set (UA σ X.J), IsCompact Ω → ∃ C : ℝ≥0, ∀ g ∈ Ω, ht g ≤ C) (hθ : Ker θ) (hφ : IsRapid φ) (hD : μ D < ⊤) :
    Continuous fun g => pet μ D φ (θ g) := by
  obtain ⟨K, k, h0, hK⟩ := hθ.bd hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  obtain ⟨Ω, hΩ, hg⟩ := exists_compact_mem_nhds g
  obtain ⟨C, hC⟩ := hb Ω hΩ
  refine continuousAt_of_dominated (bound := fun _ => K * (C : ℝ) ^ k) (Eventually.of_forall (hθ.meas hφ)) ?_
    (integrableOn_const hD.ne) (Eventually.of_forall fun h => ?_)
  · filter_upwards [hg] with x hx
    refine Eventually.of_forall fun h => (hK x h).trans ?_
    have : (ht x : ℝ) ≤ C := hC x hx
    gcongr
  · exact (continuous_const.mul (hθ.1.comp (Continuous.prodMk_left h)).star).continuousAt

theorem theta_act (om : Rep σ X W) (Ψ : Fn F n d) (u g : UA σ X.J) (h x : UA σ W.J) :
    theta om (om (u, h) Ψ) g x = theta om Ψ (g * u) (x * h) := by
  rw [theta, theta, ← Module.End.mul_apply, ← map_mul]; rfl

theorem theta_add {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F _)
    (hΨ : Ψ ∈ schA F _) (g h) : theta om (Φ + Ψ) g h = theta om Φ g h + theta om Ψ g h := by
  simp only [theta, map_add]
  exact thetaSum_add F (hp _ _ hΦ) (hp _ _ hΨ)

theorem theta_smul (om : Rep σ X W) (c : ℂ) (Φ : Fn F n d) (g h) : theta om (c • Φ) g h = c * theta om Φ g h := by
  simp only [theta, map_smul, thetaSum_smul]

theorem exists_form {om : Rep σ X W} (hp : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F _)
    (hk : ∀ Ψ ∈ schA F (Fin n × Fin d), Ker (theta om Ψ)) (hD : μ D < ⊤) {Q : Type} [AddCommGroup Q] [Module ℂ Q]
    (P : Submodule ℂ Q) (C : Q →ₗ[ℂ] (UA σ W.J → ℂ)) (hr : ∀ Φ ∈ P, IsRapid (C Φ)) (g : UA σ X.J) :
    ∃ L : Q →ₗ[ℂ] Fn F n d →ₛₗ[starRingEnd ℂ] ℂ, ∀ Φ ∈ P, ∀ Ψ ∈ schA F _, L Φ Ψ = th om μ D (C Φ) Ψ g := by
  obtain ⟨q, hq⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
  obtain ⟨q', hq'⟩ := (schA F (Fin n × Fin d)).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  have i := fun (a : Q) (b : Fn F n d) => (hk _ (q' b).2).int (hr _ (q a).2) hD g
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => th om μ D (C (q a)) (q' b) g) (fun a a' b => ?_)
    (fun c a b => ?_) (fun a b b' => ?_) fun c a b => ?_, fun Φ hΦ Ψ hΨ => ?_⟩
  · simp only [th, pet, map_add, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (i a b) (i a' b)
  · simp only [th, pet, map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul, RingHom.id_apply]
  · simp only [th, pet, map_add, Submodule.coe_add, theta_add hp (q' b).2 (q' b').2, star_add, mul_add]
    exact integral_add (i a b) (i a b')
  · simp only [th, pet, map_smul, Submodule.coe_smul, theta_smul, star_mul', smul_eq_mul, mul_left_comm _ (star c),
      integral_const_mul]
    rfl
  · have e : q Φ = ⟨Φ, hΦ⟩ := LinearMap.congr_fun hq ⟨Φ, hΦ⟩
    have e' : q' Ψ = ⟨Ψ, hΨ⟩ := LinearMap.congr_fun hq' ⟨Ψ, hΨ⟩
    change th om μ D (C (q Φ)) (q' Ψ) g = _
    rw [e, e']

theorem th_right [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable (ratU σ W.J)] (hD : IsFundamentalDomain (ratU σ W.J) D μ)
    {om : Rep σ X W} {Ψ : Fn F n d} (hθ : Ker (theta om Ψ)) (hφ : IsRapid φ) (g h) :
    th om μ D (fun x => φ (x * h)) (om (1, h) Ψ) g = th om μ D φ Ψ g := by
  simp only [th, pet, theta_act, mul_one]
  exact PositivityTheory.ThKF.L2.integral_right hD (fun x => φ x * star (theta om Ψ g x)) (fun γ hγ x => by
    rw [hφ.2.1 γ hγ, ← hθ.2.1 1 (one_mem _) γ hγ g x, one_mul]) h

theorem exists_fac {P A Z : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (f : P →ₗ[ℂ] A) (g : P →ₗ[ℂ] Z) (h : ∀ x, f x = 0 → g x = 0) : ∃ C : A →ₗ[ℂ] Z, ∀ x, C (f x) = g x := by
  obtain ⟨C, hC⟩ := ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap).exists_extend
  refine ⟨C, fun x => (LinearMap.congr_fun hC ⟨f x, x, rfl⟩).trans ?_⟩
  exact congrArg ((LinearMap.ker f).liftQ g h) (f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)

end GlobalTheory.ThK.Dbl.TC

end
