import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad.FourierTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  haveI : Module.Finite F E :=
    Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  haveI : Module.Finite A.K A.L := Module.Finite.equiv A.push.symm.out.equiv
  exact Module.Finite.trans A.K A.L

theorem star_smul_F (A : Et F E) (c : F) (y : A.L) : star (c • y) = c • star y := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, mul_comm, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]

def beta (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.L :=
  LinearMap.mk₂ F (fun y' y => Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)))
    (by intro a b c; simp only [star_add, add_mul, map_add, mul_add])
    (by intro c a b
        rw [star_smul_F, smul_mul_assoc, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])
    (by intro a b c; simp only [mul_add, map_add])
    (by intro c a b
        rw [mul_smul_comm, LinearMap.map_smul_of_tower, mul_smul_comm, LinearMap.map_smul])

theorem beta_apply (A : Et F E) (x : A.K) (y' y : A.L) :
    beta A x y' y = Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y' * y)) := rfl

theorem algMap_inj (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) :
    Function.Injective (algebraMap A.K A.L) := by
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  rw [injective_iff_map_eq_zero]
  intro k hk
  by_contra hne
  obtain ⟨k', hk'⟩ := hK.mul_inv_cancel hne
  have h : algebraMap A.K A.L (k * k') = 0 := by rw [map_mul, hk, zero_mul]
  rw [hk', map_one] at h
  exact one_ne_zero h

theorem beta_symm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    ∀ a b, beta A x a b = beta A x b a := by
  intro a b
  rw [beta_apply, beta_apply]
  congr 2
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, star_mul, star_mul, star_star, star_star]
  ring

theorem trace_algMap [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (c : A.K) :
    Algebra.trace A.K A.L (algebraMap A.K A.L c) = 2 * c := by
  apply algMap_inj A hK hL
  rw [(GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.1, A.star_K, map_mul, map_ofNat]
  ring

theorem beta_sepLeft [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).SeparatingLeft := by
  haveI : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  haveI : CharZero F := Unram.charZero (F := F) (E := E)
  intro a ha
  by_contra hne
  have hsa : star a ≠ 0 := by
    intro h; apply hne; simpa using congrArg star h
  obtain ⟨u, hu⟩ := hL.mul_inv_cancel hsa
  have h2 : (2 : A.K) ≠ 0 := by
    have : (2 : A.K) = algebraMap F A.K 2 := by rw [map_ofNat]
    rw [this]
    intro h
    exact two_ne_zero ((injective_iff_map_eq_zero (algebraMap F A.K)).1 (algebraMap F A.K).injective _ h)
  obtain ⟨t, ht⟩ := hK.mul_inv_cancel h2
  have htr : ∀ k : A.K, Algebra.trace F A.K k = 0 := by
    intro k
    have := ha (u * algebraMap A.K A.L (((x⁻¹ : A.Kˣ) : A.K) * t * k))
    rw [beta_apply, ← mul_assoc, hu, one_mul, trace_algMap A hK hL] at this
    have e : (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k)) = k := by
      calc (x : A.K) * (2 * (((x⁻¹ : A.Kˣ) : A.K) * t * k))
          = ((x : A.K) * ((x⁻¹ : A.Kˣ) : A.K)) * (2 * t) * k := by ring
        _ = k := by rw [Units.mul_inv, ht, one_mul, one_mul]
    rwa [e] at this
  have h1 : (1 : A.K) = 0 :=
    (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1.1 1 (fun n => by rw [Algebra.traceForm_apply, one_mul]; exact htr n)
  exact one_ne_zero h1

theorem beta_isSymm [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.K) :
    (beta A x).IsSymm := LinearMap.BilinForm.isSymm_def.2 (beta_symm A hK hL x)

theorem beta_nondeg [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) (x : A.Kˣ) :
    (beta A x).Nondegenerate :=
  ((beta_isSymm A hK hL x).isRefl.nondegenerate_iff_separatingLeft).2 (beta_sepLeft A hK hL x)

theorem cont_psi {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  have h : (fun b => ψ b) =ᶠ[𝓝 a] fun _ => ψ a := by
    filter_upwards [Metric.ball_mem_nhds a one_pos] with b hb
    have h1 : ψ (b - a) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact le_of_lt hb)
    calc ψ b = ψ (a + (b - a)) := by rw [add_sub_cancel]
      _ = ψ a * ψ (b - a) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ a := by rw [h1, mul_one]
  exact continuousAt_const.congr h.symm

end GlobalTheory.JR.WeilQuad.FourierTest

open GlobalTheory.JR.WeilQuad.FourierTest in

theorem GlobalTheory.JR.WeilQuad.fOp_isTest_add : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧
      ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  intro F E _ _ _ _ _ A ψ x μ ω h φ hφ
  obtain ⟨hK, hL, hψ, hsd, -⟩ := h
  haveI := hsd.1
  haveI := finite_F_L A
  have hker : A.kerL ψ (x : A.K) = fun a b => ψ (beta A x a b) := rfl
  have hint : ∀ f : A.L → ℂ, IsTest f → ∀ y, Integrable (fun y' => f y' * A.kerL ψ (x : A.K) y' y) μ := by
    intro f hf y
    rw [hker]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hf.2.mul_right)
    exact hf.1.continuous.mul
      ((cont_psi hψ).comp (IsModuleTopology.continuous_of_linearMap ((beta A x).flip y)))
  refine ⟨?_, fun φ' hφ' => ?_⟩
  · have := (GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ A.L (beta A x)
      (beta_isSymm A hK hL x) (beta_nondeg A hK hL x)).2 μ hsd.1 φ hφ
    unfold fOp
    rw [hker]
    exact this
  · funext y
    simp only [fOp, fourB, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)
