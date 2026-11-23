import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def antisymEvalOn {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ)) :
    MvPolynomial (T × Fin N) ℝ →ₗ[ℝ] C(Ω, ℝ) where
  toFun p := ⟨fun x => eval (x : T × Fin N → ℝ) p, (continuous_eval p).comp continuous_subtype_val⟩
  map_add' p q := by ext x; simp
  map_smul' c p := by ext x; simp

@[simp] lemma antisymEvalOn_apply {T : Type*} {N : ℕ} (Ω : Set (T × Fin N → ℝ))
    (p : MvPolynomial (T × Fin N) ℝ) (x : Ω) : antisymEvalOn Ω p x = eval (x : T × Fin N → ℝ) p :=
  rfl

lemma abs_coeff_le_sum_abs_coeff {σ : Type*} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m p| ≤ ∑ m' ∈ p.support, |coeff m' p| := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m' => |coeff m' p|) (fun _ _ => abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma exists_uniform_coeff_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {σ : Type*} (G : E →ₗ[ℝ] MvPolynomial σ ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : E) (m : σ →₀ ℕ), |coeff m (G y)| ≤ C * ‖y‖ := by
  let b := Module.finBasis ℝ E
  let c : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖c i‖ * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|,
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _), fun y m => ?_⟩
  have hy : G y = ∑ i, b.repr y i • G (b i) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum]
    simp only [map_smul]
  rw [hy, coeff_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [coeff_smul, smul_eq_mul, abs_mul]
  have h1 : |b.repr y i| ≤ ‖c i‖ * ‖y‖ := by
    have := (c i).le_opNorm y
    simpa [c, Real.norm_eq_abs] using this
  calc |b.repr y i| * |coeff m (G (b i))|
      ≤ (‖c i‖ * ‖y‖) * ∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))| :=
        mul_le_mul h1 (abs_coeff_le_sum_abs_coeff _ _) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖c i‖ * (∑ m' ∈ (G (b i)).support, |coeff m' (G (b i))|) * ‖y‖ := by ring

theorem AntisymStability.proof (hB1 : AntisymDivisible.Statement) : AntisymStability.Statement := by
  intro T _ _ N j Om hOm
  set Ω : Set (T × Fin N → ℝ) :=
    ⋃ (τ : T) (a : Fin N) (b : Fin N) (_ : a.val < j ∧ j ≤ b.val), Om τ a b with hΩdef
  have hΩc : IsCompact Ω :=
    isCompact_iUnion fun τ => isCompact_iUnion fun a => isCompact_iUnion fun b =>
      isCompact_iUnion fun h => (hOm τ a b h.1 h.2).1
  have : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩc
  have : FiniteDimensional ℝ (homogeneousSubmodule (T × Fin N) ℝ (antisymDegree T N + 1)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  have : FiniteDimensional ℝ (antisymSpace T N j) :=
    Submodule.finiteDimensional_of_le (fun P hP => hP.1)
  let Φ : antisymSpace T N j →ₗ[ℝ] C(Ω, ℝ) := (antisymEvalOn Ω).comp (antisymSpace T N j).subtype
  obtain ⟨g, hg⟩ := Φ.rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict Φ)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_coeff_bound (E := LinearMap.range Φ) ((antisymSpace T N j).subtype.comp g)
  refine ⟨C, fun P hP => ?_⟩
  let P' : antisymSpace T N j := ⟨P, hP⟩
  let y := Φ.rangeRestrict P'
  let Q : antisymSpace T N j := g y
  have hQ : Φ Q = Φ P' := by
    have h1 : Φ.rangeRestrict Q = y := LinearMap.congr_fun hg y
    exact congrArg Subtype.val h1
  have hker : Φ (P' - Q) = 0 := by rw [map_sub, hQ, sub_self]
  have hvan : ∀ x ∈ Ω, eval x ((P' - Q : antisymSpace T N j) : MvPolynomial (T × Fin N) ℝ) = 0 := by
    intro x hx
    have := congrArg (fun f : C(Ω, ℝ) => f ⟨x, hx⟩) hker
    simpa [Φ] using this
  obtain ⟨l, hl, hPl⟩ := hB1 T N j _ (P' - Q).2 (fun τ a b ha hb => by
    obtain ⟨_, _, O, hO, hne, hOsub⟩ := hOm τ a b ha hb
    refine ⟨O, hO, hne, fun x hx => hvan x ?_⟩
    exact Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨b,
      Set.mem_iUnion.2 ⟨⟨ha, hb⟩, hOsub hx⟩⟩⟩⟩)
  refine ⟨l, hl, fun M hM hbd m => ?_⟩
  have hPQ : P - antisymDelta T N * l = (Q : MvPolynomial (T × Fin N) ℝ) := by
    rw [← hPl, Submodule.coe_sub]
    simp [P']
  rw [hPQ]
  have hy : ‖y‖ ≤ M := by
    have e : ‖y‖ = ‖Φ P'‖ := rfl
    rw [e, ContinuousMap.norm_le _ hM]
    rintro ⟨x, hx⟩
    have hx' := hx
    simp only [hΩdef, Set.mem_iUnion] at hx'
    obtain ⟨τ, a, b, ⟨ha, hb⟩, hxO⟩ := hx'
    simpa [Φ, P', Real.norm_eq_abs] using hbd τ a b ha hb x hxO
  calc |coeff m (Q : MvPolynomial (T × Fin N) ℝ)| ≤ C * ‖y‖ := hC y m
    _ ≤ C * M := mul_le_mul_of_nonneg_left hy hC0

end GroundTheory.Heights₂.Heights
