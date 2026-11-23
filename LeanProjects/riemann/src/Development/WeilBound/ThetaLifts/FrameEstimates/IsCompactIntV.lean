import Mathlib
import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def stdF (κ : Type) (u : HeightOneSpectrum (𝓞 F)) : (κ → Fv F u) → ℂ :=
  Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1

def Good (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) : Prop :=
  (∀ u, φ u ∈ SB (κ → Fv F u)) ∧ ∀ᶠ u in cofinite, φ u = stdF κ u

def pf (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) (y : κ → Af F) : ℂ :=
  ∏ᶠ u, φ u fun i => evalV F u (y i)

theorem pure_eq (f : SInf F κ) (φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ) :
    pure f φ = pureA F f (pf φ) := rfl

theorem ev_int (y : κ → Af F) : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  eventually_all.2 fun i => (y i).2

theorem cont_evalV (u : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F u) :=
  (continuous_apply u).comp RestrictedProduct.continuous_coe

theorem isOpen_intAf : IsOpen {a : Af F | ∀ v, evalV F v a ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intV (u : HeightOneSpectrum (𝓞 F)) :
    IsCompact {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F} := by
  have h : IsCompact (u.adicCompletionIntegers F : Set (Fv F u)) := isCompact_iff_compactSpace.2
    (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F u)
  simpa [Set.pi] using isCompact_univ_pi fun _ : κ => h

theorem isCompact_box (C : ∀ u : HeightOneSpectrum (𝓞 F), Set (Fv F u)) (hC : ∀ u, IsCompact (C u))
    (h : ∀ᶠ u in cofinite, C u ⊆ u.adicCompletionIntegers F) : IsCompact {a : Af F | ∀ u, evalV F u a ∈ C u} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {u | C u ⊆ u.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 h
  let P := RestrictedProduct (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 S)
  have h1 : IsCompact {x : P | ∀ u, x u ∈ C u} := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    convert isCompact_univ_pi hC
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ u -
      exact hy u
    · intro hx
      exact ⟨⟨x, fun u hu => hu (hx u trivial)⟩, fun u => hx u trivial, rfl⟩
  have h2 := h1.image (RestrictedProduct.continuous_inclusion hS)
  have e : {a : Af F | ∀ u, evalV F u a ∈ C u} = RestrictedProduct.inclusion _ _ hS '' {x : P | ∀ u, x u ∈ C u} := by
    ext a
    constructor
    · intro ha
      exact ⟨⟨a.1, fun u hu => hu (ha u)⟩, ha, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [e]
  exact h2

theorem pf_eq_prod {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (S : Finset (HeightOneSpectrum (𝓞 F)))
    (y : κ → Af F) (h : ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F) :
    pf φ y = ∏ u ∈ S, φ u fun i => evalV F u (y i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun u hu => ?_
  by_contra hn
  apply hu
  simp only
  rw [(h u hn).1, stdF, Set.indicator_of_mem (by exact (h u hn).2)]
  rfl

theorem exists_fin {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : ∀ᶠ u in cofinite, φ u = stdF κ u)
    (y : κ → Af F) : ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ u ∉ S, φ u = stdF κ u ∧ ∀ i, evalV F u (y i) ∈ u.adicCompletionIntegers F :=
  ⟨(hφ.and (ev_int y)).toFinset, fun u hu => by
    by_contra hn
    exact hu (Set.Finite.mem_toFinset _ |>.2 hn)⟩

theorem pf_mem {φ : ∀ u : HeightOneSpectrum (𝓞 F), (κ → Fv F u) → ℂ} (hφ : Good φ) : pf φ ∈ SB (κ → Af F) := by
  have hc : ∀ u, Continuous fun (y : κ → Af F) i => evalV F u (y i) := fun u =>
    continuous_pi fun i => (cont_evalV u).comp (continuous_apply i)
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨S, hS⟩ := exists_fin hφ.2 x
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i v, evalV F v (y i - x i) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => (isOpen_intAf.preimage (f := fun y : κ → Af F => y i - x i) (by fun_prop)).mem_nhds
        (by intro v; simp)
    have h2 : ∀ᶠ y in 𝓝 x, ∀ u ∈ S, φ u (fun i => evalV F u (y i)) = φ u fun i => evalV F u (x i) :=
      (eventually_all_finset S).2 fun u _ => ((hφ.1 u).1.comp_continuous (hc u)).eventually_eq x
    filter_upwards [h1, h2] with y h1 h2
    rw [pf_eq_prod S x hS, pf_eq_prod S y fun u hu => ⟨(hS u hu).1, fun i => ?_⟩]
    · exact Finset.prod_congr rfl h2
    · have := add_mem (h1 i u) ((hS u hu).2 i)
      rwa [map_sub, sub_add_cancel] at this
  · have hK : ∀ i : κ, IsCompact {a : Af F | ∀ u, evalV F u a ∈ (fun x => x i) '' tsupport (φ u)} := fun i =>
      isCompact_box _ (fun u => (hφ.1 u).2.isCompact.image (continuous_apply i)) (by
        filter_upwards [hφ.2] with u hu
        rintro _ ⟨x, hx, rfl⟩
        rw [hu] at hx
        exact closure_minimal Set.support_indicator_subset (isCompact_intV u).isClosed hx i)
    refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
    by_contra h0
    refine hy fun i _ u => ⟨fun i => evalV F u (y i), subset_tsupport _ (fun h => h0 ?_), rfl⟩
    obtain ⟨S, hS⟩ := exists_fin hφ.2 y
    classical
    rw [pf_eq_prod (insert u S) y fun v hv => hS v fun h => hv (Finset.mem_insert_of_mem h)]
    exact Finset.prod_eq_zero (Finset.mem_insert_self _ _) h

theorem smul_pureA (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) : c • pureA F f g = pureA F (c • f : SInf F κ) g := by
  funext x
  simp [pureA, mul_assoc]

theorem sum_of_span {S : Set ((κ → AF F) → ℂ)} {T : Set ((κ → Af F) → ℂ)}
    (h : ∀ Φ ∈ S, ∃ (f : SInf F κ) (g : (κ → Af F) → ℂ), g ∈ T ∧ Φ = pureA F f g) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ Submodule.span ℂ S) :
    ∃ (m : ℕ) (f : Fin m → SInf F κ) (φ : Fin m → (κ → Af F) → ℂ), (∀ i, φ i ∈ T) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, g, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f φ h1 h2 using fun i => h (g i) (g i).2
  refine ⟨m, fun i => c i • f i, φ, h1, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h2, smul_pureA]

theorem exists_one : ∃ f : SInf F κ, f 0 = 1 := by
  classical
  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have h2 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  exact ⟨hs.toSchwartzMap hc, by simp [h2]⟩

def finPt (y : κ → Af F) : κ → AF F := fun i => ((0, y i) : AF F)

theorem pureA_zero (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) :
    pureA F f g (finPt y) = f 0 * g y := by
  have e : (fun _ : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) = 0 := funext fun _ => map_zero _
  exact congrArg (fun z => f z * g y) e

end PositivityTheory.ThKEst.FiniteAdelicSupportCompactness

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK FiniteAdelicSupportCompactness

theorem soFin_of : SoFin := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have good : ∀ φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      pf φ ∈ SB (Fin n × Fin d → Af F) := fun φ h1 h2 =>
    pf_mem ⟨h1, by
      filter_upwards [h2, hP.good.std] with v a b
      exact a.trans b⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun Φ hΦ => ?_, fun φ hφ => ?_⟩
  · refine sum_of_span (T := soFin B M) ?_ hΦ
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, pf φ, ⟨good φ h1 h2, fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩⟩, rfl⟩
  · refine sum_of_span (T := (SB (Fin n × Fin d → Af F) : Set _)) ?_ hΦ
    rintro _ ⟨f, g, h1, rfl⟩
    exact ⟨f, g, h1, rfl⟩
  · refine (Submodule.span_le.2 ?_ : M.So B.ψ B.τ₁ ≤ schA F _) hΦ
    rintro _ ⟨f, φ, h1, h2, -, rfl⟩
    exact Submodule.subset_span ⟨f, pf φ, good φ h1 h2, rfl⟩
  · obtain ⟨f₀, h0⟩ := exists_one (F := F) (κ := Fin n × Fin d)
    obtain ⟨m, c, g, hg⟩ := Submodule.mem_span_set'.1 (hφ.2 f₀)
    choose f χ h1 h2 h3 h4 using fun i => (g i).2
    have e : ∀ y, φ y = ∑ i, c i * f i 0 * pf (χ i) y := fun y => by
      have := congrFun hg (finPt y)
      rw [pureA_zero, h0, one_mul, Finset.sum_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h4, pure_eq, Pi.smul_apply, pureA_zero, smul_eq_mul, mul_assoc]
    refine ⟨m, fun i => c i * f i 0, χ, fun i => ⟨h1 i, h2 i, h3 i⟩, fun f' => ?_⟩
    funext x
    rw [Finset.sum_apply]
    simp only [pure_eq, pureA, Pi.smul_apply, smul_eq_mul, e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end PositivityTheory.ThKEst

end
