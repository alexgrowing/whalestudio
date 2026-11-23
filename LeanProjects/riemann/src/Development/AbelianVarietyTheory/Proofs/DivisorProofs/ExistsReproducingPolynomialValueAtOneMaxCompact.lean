import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

noncomputable section

open MeasureTheory MvPolynomial
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1

namespace GlobalTheory.PsCo.Pc3.ReproPf

variable {n : ℕ} (ε : Fin n → Bool)

def pt (k : KG ε) : ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ :=
  Sum.elim (fun x => toMK k x.1 x.2) (fun x => star (toMK k x.1 x.2))

theorem ev_eq (k : KG ε) (P : Poly n) : ev (toMK k) P = eval (pt ε k) P := rfl

theorem continuous_toMK : Continuous fun k : KG ε => toMK k :=
  Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem continuous_pt : Continuous (pt ε) := by
  refine continuous_pi fun v => ?_
  rcases v with x | x
  · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε))
  · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp (continuous_toMK ε)))

def evL : Poly n →ₗ[ℂ] (KG ε → ℂ) where
  toFun P k := eval (pt ε k) P
  map_add' P Q := by ext k; simp
  map_smul' c P := by ext k; simp [MvPolynomial.smul_eval]

theorem continuous_evL (P : Poly n) : Continuous (evL ε P) :=
  (MvPolynomial.continuous_eval P).comp (continuous_pt ε)

def Fd (d : ℕ) : Submodule ℂ (KG ε → ℂ) := (restrictTotalDegree _ ℂ d).map (evL ε)

instance (d : ℕ) : FiniteDimensional ℂ (Fd ε d) := by
  unfold Fd; infer_instance

theorem continuous_of_mem {d : ℕ} {f : KG ε → ℂ} (hf : f ∈ Fd ε d) : Continuous f := by
  obtain ⟨P, -, rfl⟩ := Submodule.mem_map.1 hf
  exact continuous_evL ε P

theorem integrable_of_cont {f : KG ε → ℂ} (hf : Continuous f) : Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem star_evL (P : Poly n) : ∃ Q : Poly n, Q.totalDegree ≤ P.totalDegree ∧
    ∀ k, star (evL ε P k) = evL ε Q k := by
  refine ⟨rename Sum.swap (map (starRingEnd ℂ) P), ?_, fun k => ?_⟩
  · exact (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ _))
  · change (starRingEnd ℂ) (eval (pt ε k) P) = eval (pt ε k) (rename Sum.swap (map (starRingEnd ℂ) P))
    rw [eval_rename, eval_map, ← coe_eval₂Hom]
    induction P using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p v hp =>
      simp only [map_mul, hp, eval_X, coe_eval₂Hom, eval₂_X]
      rcases v with x | x <;> simp [pt]

def gram (d : ℕ) : Fd ε d →ₗ[ℂ] Module.Dual ℂ (Fd ε d) :=
  LinearMap.mk₂ ℂ (fun g f => ∫ k, (g : KG ε → ℂ) k * (f : KG ε → ℂ) k ∂(muK ε))
    (fun g g' f => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g'.2).mul (continuous_of_mem ε f.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun g f f' => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f.2)))
        (integrable_of_cont ε ((continuous_of_mem ε g.2).mul (continuous_of_mem ε f'.2))))
    (fun c g f => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact integral_const_mul c _)

theorem gram_injective (d : ℕ) : Function.Injective (gram ε d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro g hg
  obtain ⟨P, hP, hgP⟩ := Submodule.mem_map.1 g.2
  obtain ⟨Q, hQ, hQk⟩ := star_evL ε P
  have hQm : evL ε Q ∈ Fd ε d :=
    Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2
      (hQ.trans ((mem_restrictTotalDegree _ _ _).1 hP)))
  have h0 := LinearMap.congr_fun hg ⟨evL ε Q, hQm⟩
  simp only [gram, LinearMap.mk₂_apply, LinearMap.zero_apply] at h0
  have hc : Continuous (g : KG ε → ℂ) := continuous_of_mem ε g.2
  have e1 : ∀ k, (g : KG ε → ℂ) k * evL ε Q k = ((‖(g : KG ε → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [← hQk, ← hgP, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  simp_rw [e1, integral_complex_ofReal, Complex.ofReal_eq_zero] at h0
  have hnn : 0 ≤ᵐ[muK ε] fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := Filter.Eventually.of_forall fun k => by positivity
  have hc2 : Continuous fun k => ‖(g : KG ε → ℂ) k‖ ^ 2 := hc.norm.pow 2
  have hint : Integrable (fun k => ‖(g : KG ε → ℂ) k‖ ^ 2) (muK ε) :=
    integrableOn_univ.1 (hc2.continuousOn.integrableOn_compact isCompact_univ)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hfun := (hc2.ae_eq_iff_eq (muK ε) continuous_const).1 hae
  ext k
  have h1 : ‖(g : KG ε → ℂ) k‖ ^ 2 = 0 := congrFun hfun k
  have h2 : (g : KG ε → ℂ) k = 0 := by simpa using h1
  simpa using h2

theorem fock_reproducing_formula : Repro := by
  intro n ε d
  have hfin : Module.finrank ℂ (Fd ε d) = Module.finrank ℂ (Module.Dual ℂ (Fd ε d)) :=
    (Subspace.dual_finrank_eq).symm
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 (gram_injective ε d)
  let Λ : Module.Dual ℂ (Fd ε d) := (LinearMap.proj (R := ℂ) (φ := fun _ : KG ε => ℂ) 1).comp (Fd ε d).subtype
  obtain ⟨g, hg⟩ := hs Λ
  obtain ⟨Q, hQ, hgQ⟩ := Submodule.mem_map.1 g.2
  refine ⟨Q, (mem_restrictTotalDegree _ _ _).1 hQ, fun P hP => ?_⟩
  have h := LinearMap.congr_fun hg ⟨evL ε P, Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ _).2 hP)⟩
  simp only [gram, LinearMap.mk₂_apply, Λ, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.proj_apply] at h
  rw [← hgQ] at h
  exact h.symm

end GlobalTheory.PsCo.Pc3.ReproPf

namespace GlobalTheory.PsCo.Pc3

theorem fock_reproducing_formula : Repro := ReproPf.fock_reproducing_formula

end GlobalTheory.PsCo.Pc3
