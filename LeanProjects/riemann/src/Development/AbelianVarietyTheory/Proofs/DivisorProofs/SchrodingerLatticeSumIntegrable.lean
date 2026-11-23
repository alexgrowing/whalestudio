import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

namespace GlobalTheory.LagrIntg

def linC {R : Type} [CommRing R] {κ : Type} [Fintype κ] {r : ℕ} (c : Fin r → κ → R) (y : Fin r → R) : κ → R :=
  fun k => ∑ j, y j * c j k

def linD {R : Type} [CommRing R] {κ : Type} [Fintype κ] {r : ℕ} (d : Fin r → κ → R) (z : κ → R) : Fin r → R :=
  fun i => ∑ k, d i k * z k

theorem linD_linC {F R : Type} [Field F] [CommRing R] (e : F →+* R) {κ : Type} [Fintype κ] {r : ℕ}
    (a p : Fin r → κ → F) (hp : ∀ i j, ∑ k, p i k * a j k = if i = j then 1 else 0) (y : Fin r → R) :
    linD (fun i k => e (p i k)) (linC (fun j k => e (a j k)) y) = y := by
  funext i
  simp only [linD, linC, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ k, e (p i k) * (y j * e (a j k)) = y j * e (if i = j then 1 else 0) := by
    intro j
    rw [← hp i j, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]; ring
  simp only [h, apply_ite e, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_leftInv {F : Type} [Field F] {κ : Type} [Fintype κ] {r : ℕ} (a : Fin r → κ → F)
    (ha : LinearIndependent F a) : ∃ p : Fin r → κ → F, ∀ i j, ∑ k, p i k * a j k = if i = j then 1 else 0 := by
  let A : (Fin r → F) →ₗ[F] (κ → F) :=
    { toFun := fun y => ∑ j, y j • a j
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.smul_sum, smul_smul] }
  have hA : LinearMap.ker A = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    funext i
    exact Fintype.linearIndependent_iff.1 ha y hy i
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective A hA
  refine ⟨fun i k => P (fun k' => if k = k' then 1 else 0) i, fun i j => ?_⟩
  have h1 : A (fun j' => if j = j' then 1 else 0) = a j := by
    simp [A]
  have h2 : P (a j) = fun j' => if j = j' then 1 else 0 := by
    rw [← h1]; exact LinearMap.congr_fun hP _
  have h3 : P (a j) i = ∑ k, P (fun k' => if k = k' then (1 : F) else 0) i * a j k := by
    conv_lhs => rw [pi_eq_sum_univ (a j)]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [← h3, h2]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end GlobalTheory.LagrIntg

namespace GlobalTheory.LagrIntg

variable (F : Type) [Field F] [NumberField F]

noncomputable def archPart : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

noncomputable def finPart : AF F →+* FiniteAdeleRing (𝓞 F) F :=
  RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

variable {F}

theorem continuous_linC {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ : Type} [Fintype κ]
    {r : ℕ} (c : Fin r → κ → R) : Continuous (linC c) :=
  continuous_pi fun _ => continuous_finset_sum _ fun j _ => (continuous_apply j).mul continuous_const

theorem continuous_linD {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ : Type} [Fintype κ]
    {r : ℕ} (d : Fin r → κ → R) : Continuous (linD d) :=
  continuous_pi fun _ => continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_apply k)

theorem comp_mem_SB {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {κ : Type} [Fintype κ] {r : ℕ}
    (c d : Fin r → κ → R) (hdc : ∀ y, linD d (linC c y) = y)
    {g : (κ → R) → ℂ} (hg : g ∈ SB (κ → R)) : (g ∘ linC c) ∈ SB (Fin r → R) := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  show IsLocallyConstant (g ∘ linC c) ∧ HasCompactSupport (g ∘ linC c)
  refine ⟨hg'.1.comp_continuous (continuous_linC c), ?_⟩
  have h1 : tsupport (g ∘ linC c) ⊆ linC c ⁻¹' tsupport g :=
    closure_minimal (fun y hy => subset_tsupport g hy) ((isClosed_tsupport g).preimage (continuous_linC c))
  have hsub : tsupport (g ∘ linC c) ⊆ linD d '' tsupport g := fun y hy => ⟨linC c y, h1 hy, hdc y⟩
  exact (hg'.2.image (continuous_linD d)).of_isClosed_subset (isClosed_tsupport _) hsub

variable (F) in

theorem exists_schwartz_comp {κ : Type} [Fintype κ] {r : ℕ} (c d : Fin r → κ → mixedEmbedding.mixedSpace F)
    (hdc : ∀ y, linD d (linC c y) = y) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    ∃ f' : SchwartzMap (Fin r → mixedEmbedding.mixedSpace F) ℂ, ∀ y, f' y = f (linC c y) := by
  let Lc : (Fin r → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := linC c
      map_add' := by intro y z; funext k; simp [linC, add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a y; funext k; simp [linC, Finset.smul_sum, smul_mul_assoc] }
  let Ld : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin r → mixedEmbedding.mixedSpace F) :=
    { toFun := linD d
      map_add' := by intro y z; funext k; simp [linD, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a y; funext k; simp [linD, Finset.smul_sum, mul_smul_comm] }
  let Lc' := LinearMap.toContinuousLinearMap Lc
  let Ld' := LinearMap.toContinuousLinearMap Ld
  have hb : ∃ (k : ℕ) (C : ℝ), ∀ y, ‖y‖ ≤ C * (1 + ‖Lc' y‖) ^ k := by
    refine ⟨1, ‖Ld'‖, fun y => ?_⟩
    have e : Ld' (Lc' y) = y := hdc y
    calc ‖y‖ = ‖Ld' (Lc' y)‖ := by rw [e]
      _ ≤ ‖Ld'‖ * ‖Lc' y‖ := Ld'.le_opNorm _
      _ ≤ ‖Ld'‖ * (1 + ‖Lc' y‖) ^ 1 := by
        rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  exact ⟨SchwartzMap.compCLM ℝ Lc'.hasTemperateGrowth hb f, fun y => rfl⟩

variable (F) in

theorem pureA_comp_mem {κ : Type} [Fintype κ] {r : ℕ} (a p : Fin r → κ → F)
    (hp : ∀ i j, ∑ k, p i k * a j k = if i = j then 1 else 0)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    (fun x : Fin r → AF F => pureA F f g (linC (fun j k => algebraMap F (AF F) (a j k)) x)) ∈ schA F (Fin r) := by
  obtain ⟨f', hf'⟩ := exists_schwartz_comp F (fun j k => ((archPart F).comp (algebraMap F (AF F))) (a j k))
    (fun i k => ((archPart F).comp (algebraMap F (AF F))) (p i k)) (linD_linC _ a p hp) f
  have hg' := comp_mem_SB (fun j k => ((finPart F).comp (algebraMap F (AF F))) (a j k))
    (fun i k => ((finPart F).comp (algebraMap F (AF F))) (p i k)) (linD_linC _ a p hp) hg
  refine Submodule.subset_span ⟨f', _, hg', ?_⟩
  funext x
  have hA : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (linC (fun j k => algebraMap F (AF F) (a j k)) x i).1) =
      linC (fun j k => ((archPart F).comp (algebraMap F (AF F))) (a j k))
        (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) := by
    funext k
    show archPart F (linC (fun j k => algebraMap F (AF F) (a j k)) x k) = _
    simp only [linC, map_sum, map_mul]
    rfl
  have hB : (fun i => (linC (fun j k => algebraMap F (AF F) (a j k)) x i).2) =
      linC (fun j k => ((finPart F).comp (algebraMap F (AF F))) (a j k)) (fun i => (x i).2) := by
    funext k
    show finPart F (linC (fun j k => algebraMap F (AF F) (a j k)) x k) = _
    simp only [linC, map_sum, map_mul]
    rfl
  simp only [pureA, Function.comp_apply, hf']
  rw [hA, hB]

theorem integrable_lagrForm : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (r : ℕ) (u : Fin r → (κ → F) × (κ → F)), LinearIndependent F (fun j => (u j).1) →
    ∀ μ : @Measure (Fin r → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ φ ∈ schA F κ, Integrable (fun x : Fin r → AF F => schr ψ (∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))) φ 0) μ := by
  intro F _ _ ψ hψ κ _ r u hu μ hμ φ hφ
  letI : MeasurableSpace (Fin r → AF F) := borel _
  haveI : BorelSpace (Fin r → AF F) := ⟨rfl⟩
  obtain ⟨p, hp⟩ := exists_leftInv (fun j => (u j).1) hu
  have hmem : (fun x => φ (linC (fun j k => algebraMap F (AF F) ((u j).1 k)) x)) ∈ schA F (Fin r) := by
    have hle : schA F κ ≤ (schA F (Fin r)).comap
        (LinearMap.funLeft ℂ ℂ (linC (fun j k => algebraMap F (AF F) ((u j).1 k)))) := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, hg, rfl⟩
      exact pureA_comp_mem F (fun j => (u j).1) p hp f hg
    exact hle hφ
  have hint : Integrable (fun x => φ (linC (fun j k => algebraMap F (AF F) ((u j).1 k)) x)) μ :=
    schA_integrable F (Fin r) μ hμ _ hmem
  let W : (Fin r → AF F) → (κ → AF F) × (κ → AF F) := fun x =>
    ∑ j, x j • ((fun k => algebraMap F (AF F) ((u j).1 k)), (fun k => algebraMap F (AF F) ((u j).2 k)))
  have hW1 : ∀ x, (W x).1 = linC (fun j k => algebraMap F (AF F) ((u j).1 k)) x := by
    intro x; funext k
    simp [W, linC, Prod.fst_sum, Finset.sum_apply]
  have hWc : Continuous W := continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const
  have hT : Continuous fun x => ψ ((0 : κ → AF F) ⬝ᵥ (W x).2 + ⅟(2 : AF F) * ((W x).1 ⬝ᵥ (W x).2)) :=
    hψ.1.comp (by fun_prop)
  refine (hint.bdd_mul (c := 1)
    (f := fun x => ψ ((0 : κ → AF F) ⬝ᵥ (W x).2 + ⅟(2 : AF F) * ((W x).1 ⬝ᵥ (W x).2)))
    hT.aestronglyMeasurable (ae_of_all _ fun x => (GlobalTheory.StdCharFromIsStd.norm_psi hψ _).le)).congr
    (ae_of_all _ fun x => ?_)
  show ψ ((0 : κ → AF F) ⬝ᵥ (W x).2 + ⅟(2 : AF F) * ((W x).1 ⬝ᵥ (W x).2)) * φ _ =
    ψ ((0 : κ → AF F) ⬝ᵥ (W x).2 + ⅟(2 : AF F) * ((W x).1 ⬝ᵥ (W x).2)) * φ (0 + (W x).1)
  rw [zero_add, hW1]

end GlobalTheory.LagrIntg
