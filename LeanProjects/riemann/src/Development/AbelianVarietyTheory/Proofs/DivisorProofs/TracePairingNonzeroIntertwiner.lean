import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv

noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]

theorem avg_inner_map {T : W →L[ℂ] W} (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : W) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : W →ₗ[ℂ] W), hT⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y

theorem avg_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact hemb.isInducing.secondCountableTopology

theorem avg_continuous_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

def avgF (T : Mat n → (W →L[ℂ] W)) (S : Mat n → (Z →L[ℂ] Z)) (e : W) (f : Z) (w : W) (k : KG ε) : Z :=
  ⟪T (toMK k) e, w⟫_ℂ • S (toMK k) f

theorem avgF_continuous {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Continuous (avgF (ε := ε) T S e f w) := by
  have h1 : Continuous fun k : KG ε => T (toMK k) e :=
    (hT.2.2 e).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  have h2 : Continuous fun k : KG ε => S (toMK k) f :=
    (hS.2.2 f).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  exact (h1.inner continuous_const).smul h2

theorem avgF_integrable {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Integrable (avgF (ε := ε) T S e f w) (muK ε) := by
  have := avg_secondCountable ε
  exact integrableOn_univ.1 ((avgF_continuous hT hS e f w).continuousOn.integrableOn_compact isCompact_univ)

def avgMapL {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z) :
    W →ₗ[ℂ] Z where
  toFun w := ∫ k, avgF T S e f w k ∂(muK ε)
  map_add' x y := by
    rw [← integral_add (avgF_integrable hT hS e f x) (avgF_integrable hT hS e f y)]
    congr 1; funext k; simp [avgF, inner_add_right, add_smul]
  map_smul' c x := by
    rw [RingHom.id_apply, ← integral_smul]
    congr 1; funext k; simp [avgF, inner_smul_right, smul_smul]

theorem avgMapL_apply {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : avgMapL hT hS e f w = ∫ k, avgF T S e f w k ∂(muK ε) := rfl

theorem avgMapL_intertwines {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (g : KG ε) (w : W) : avgMapL hT hS e f (T (toMK g) w) = S (toMK g) (avgMapL hT hS e f w) := by
  rw [avgMapL_apply, avgMapL_apply, ← (S (toMK g)).integral_comp_comm (avgF_integrable hT hS e f w),
    ← integral_mul_left_eq_self _ g]
  congr 1; funext k
  have hm : toMK (g * k) = toMK g * toMK k := rfl
  simp only [avgF, hm, hT.1.2 _ g.2 _ k.2, hS.1.2 _ g.2 _ k.2, ContinuousLinearMap.comp_apply, map_smul]
  rw [avg_inner_map (hT.2.1 _ g.2)]

end

theorem tracePairing_nonzero_intertwiner : AvgMap := by
  intro n ε W _ _ _ T Z _ _ _ S Γ hT hS hne
  classical
  set b := stdOrthonormalBasis ℂ W
  set c := stdOrthonormalBasis ℂ Z
  let φ : Fin (Module.finrank ℂ Z) → Z →L[ℂ] ℂ := fun j =>
    LinearMap.toContinuousLinearMap ((innerₛₗ ℂ (c j)).comp Γ)
  have hφ : ∀ j u, φ j u = ⟪c j, Γ u⟫_ℂ := fun j u => rfl
  have hpt : ∀ i j (k : KG ε), φ j (avgF T S (b i) (c j) (b i) k) =
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
    intro i j k
    simp [avgF, hφ, map_smul, inner_conj_symm]
  have hint : ∀ i j, Integrable (fun k : KG ε =>
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ) (muK ε) := fun i j =>
    ((φ j).integrable_comp (avgF_integrable hT hS (b i) (c j) (b i))).congr
      (Filter.Eventually.of_forall fun k => hpt i j k)
  have key : ∀ i j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ =
      ∫ k, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ ∂(muK ε) := by
    intro i j
    rw [avgMapL_apply, ← hφ, ← (φ j).integral_comp_comm (avgF_integrable hT hS _ _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => hpt i j k)
  have hsum : ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) =
      ∑ i, ∑ j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ := by
    simp only [key]
    have hpw : ∀ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) =
        ∑ i, ∑ j, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
      intro k
      simp only [trK, LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ c, map_sum,
        Finset.sum_mul, Finset.mul_sum, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact Finset.sum_comm
    simp_rw [hpw]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
  rw [hsum] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨avgMapL hT hS (b i) (c j), fun h0 => hj ?_, fun k hk v => ?_⟩
  · rw [h0, LinearMap.zero_apply, map_zero, inner_zero_right]
  · have hk' : k ∈ Set.range (fun g : KG ε => toMK g) := by rw [Formalism.REAL.range_toMK]; exact hk
    obtain ⟨g, rfl⟩ := hk'
    exact avgMapL_intertwines hT hS (b i) (c j) g v

end GlobalTheory.PsCo.PcEF
