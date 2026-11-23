import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction

open scoped ComplexOrder InnerProductSpace

namespace GlobalTheory.HatNF

section abstract

variable {V E ι : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ev_symm_of_nonneg (ev : V →ₗ[ℂ] E) (T : Module.End ℂ V) (h : ∀ v, 0 ≤ ⟪ev v, ev (T v)⟫_ℂ) (v w : V) :
    ⟪ev w, ev (T v)⟫_ℂ = ⟪ev (T w), ev v⟫_ℂ := by
  have hd : ∀ u, ⟪ev u, ev (T u)⟫_ℂ = ⟪ev (T u), ev u⟫_ℂ := by
    intro u
    rw [← inner_conj_symm (ev (T u)) (ev u)]
    exact (Complex.conj_eq_iff_im.mpr (Complex.nonneg_iff.mp (h u)).2.symm).symm
  have h1 := hd (v + w)
  have h2 := hd (v + Complex.I • w)
  have h3 := hd v
  have h4 := hd w
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (1 / 2 + Complex.I / 2) * h3
    - (1 / 2 + Complex.I / 2 * (-Complex.I * Complex.I)) * h4
    + (1 / 2 : ℂ) * (⟪ev w, ev (T v)⟫_ℂ - ⟪ev (T w), ev v⟫_ℂ - ⟪ev v, ev (T w)⟫_ℂ + ⟪ev (T v), ev w⟫_ℂ) * hI

variable [Fintype ι] [DecidableEq ι]

theorem ev_symm_single (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v w : V) :
    ⟪ev w, ev (K (Pi.single i 1) v)⟫_ℂ = ⟪ev (K (Pi.single i 1) w), ev v⟫_ℂ := by
  have hp : ∀ j, (0 : ℂ) < ((Pi.single i 1 : ι → ℂ) + 1) j := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa using add_pos (zero_lt_one' ℂ) (zero_lt_one' ℂ)
    · simp [hj]
  have h1 := ev_symm_of_nonneg ev _ (h _ hp) v w
  simp only [map_add, map_one, LinearMap.add_apply, Module.End.one_apply, inner_add_left, inner_add_right] at h1
  linear_combination h1

theorem algHom_apply_eq_sum (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V) (f : ι → ℂ) (v : V) :
    ev (K f v) = ∑ i, f i • ev (K (Pi.single i 1) v) := by
  have hf : f = ∑ i, f i • (Pi.single i 1 : ι → ℂ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

theorem ev_adj (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v w : V) :
    ⟪ev w, ev (K f v)⟫_ℂ = ⟪ev (K (fun i => star (f i)) w), ev v⟫_ℂ := by
  rw [algHom_apply_eq_sum, algHom_apply_eq_sum ev K (fun i => star (f i)), inner_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, inner_smul_left, ev_symm_single ev K h]
  simp

theorem ev_single_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (i : ι) (v : V) :
    ‖ev (K (Pi.single i 1) v)‖ ≤ ‖ev v‖ := by
  have hid : K (Pi.single i 1) (K (Pi.single i 1) v) = K (Pi.single i 1) v := by
    rw [← Module.End.mul_apply, ← map_mul, ← Pi.single_mul, mul_one]
  have h1 := ev_symm_single ev K h i v (K (Pi.single i 1) v)
  rw [hid] at h1
  set a := ev (K (Pi.single i 1) v)
  have h2 : ‖a‖ * ‖a‖ ≤ ‖a‖ * ‖ev v‖ := by
    calc ‖a‖ * ‖a‖ = ‖⟪a, a⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [sq]
      _ = ‖⟪a, ev v⟫_ℂ‖ := by rw [h1]
      _ ≤ _ := norm_inner_le_norm _ _
  rcases (norm_nonneg a).eq_or_lt with h0 | h0
  · rw [← h0]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left h2 h0

theorem ev_le (ev : V →ₗ[ℂ] E) (K : (ι → ℂ) →ₐ[ℂ] Module.End ℂ V)
    (h : ∀ f : ι → ℂ, (∀ i, 0 < f i) → ∀ v, 0 ≤ ⟪ev v, ev (K f v)⟫_ℂ) (f : ι → ℂ) (v : V) :
    ‖ev (K f v)‖ ≤ (∑ i, ‖f i‖) * ‖ev v‖ := by
  rw [algHom_apply_eq_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (ev_single_le ev K h i v) (norm_nonneg _)

end abstract

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

theorem kappa_ptAdj_ptB : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ f : M.Ty P → ℂ, PtAdj P Bs (d.κ f) ∧ PtB P Bs (d.κ f) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN f
  classical
  let ev : (Fin P.r → ℂ) × Q.Mx P.k P.r →
      Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := fun x =>
    { toFun := fun Φ => B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let K : (M.Ty P → ℂ) →ₐ[ℂ] Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :=
    (P5.Kfp.fstAlg _).comp d.κ
  have hpos : ∀ x, ∀ g : M.Ty P → ℂ, (∀ i, 0 < g i) → ∀ v, 0 ≤ ⟪ev x v, ev x (K g v)⟫_ℂ := fun x g hg v =>
    P5.kappaFibrePos Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hD.1 X d hN.1 hN.2.1 hN.2.2.1 hN.2.2.2 g hg v x.1 x.2
  refine ⟨fun Φ Ψ x _ => ?_, ∑ i, ‖f i‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Φ x _ => ?_⟩
  · rw [hN.2.2.1.1 f]
    exact ev_adj (ev x) K (hpos x) f Φ Ψ
  · exact ev_le (ev x) K (hpos x) f Φ

end GlobalTheory.HatNF
