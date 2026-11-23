import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPlaneConstantTermGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section
namespace GlobalTheory.ThK.KFinCoef
open GlobalTheory.SiegelSet GlobalTheory.ThK.RealLineGrowthDerivative

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem smooth_lineDer {K : Subgroup (GAd σ J)} {S : Set (GAd σ J)} {f : GAd σ J → ℂ}
    (hs : ∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => f (k * (List.ofFn fun j => γ j (t j)).prod))
    {ζ : ℝ → GAd σ J} (hζ : IsRealLine σ J ζ) (hζK : ∀ s, ζ s ∈ K) :
    ∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => lineDer ζ f (k * (List.ofFn fun j => γ j (t j)).prod) := by
  intro k hk m γ hγ hγK
  have hH := hs k hk (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) γ ζ)
    (fun i => by induction i using Fin.lastCases <;> simp [hζ, hγ])
    (fun i s => by induction i using Fin.lastCases <;> simp [hζK, hγK])
  have := contDiff_partial_last hH
  simp only [prod_ofFn_snoc, ← mul_assoc] at this
  simpa only [lineDer] using this

theorem differentiableAt_of_smooth {K : Subgroup (GAd σ J)} {S : Set (GAd σ J)} {f : GAd σ J → ℂ}
    (hs : ∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => f (k * (List.ofFn fun j => γ j (t j)).prod))
    {ζ : ℝ → GAd σ J} (hζ : IsRealLine σ J ζ) (hζK : ∀ s, ζ s ∈ K) :
    ∀ k ∈ S, DifferentiableAt ℝ (fun t => f (k * ζ t)) 0 := by
  intro k hk
  have h := (hs k hk 1 (fun _ => ζ) (fun _ => hζ) (fun _ => hζK)).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => f (k * ζ t)) = ((fun s : Fin 1 → ℝ => f (k * (List.ofFn fun i => (fun _ => ζ) i (s i)).prod)) ∘
      fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

theorem mem_span_iff {S : Set (GAd σ J)} {e : ℕ} (b : Fin e → GAd σ J → ℂ) (g : GAd σ J → ℂ) :
    (fun x : S => g x) ∈ Submodule.span ℂ (Set.range fun j (x : S) => b j x) ↔
      ∃ c : Fin e → ℂ, ∀ k ∈ S, g k = ∑ j, c j * b j k := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun k hk => ?_⟩
    have := congrFun hc ⟨k, hk⟩
    simpa [Finset.sum_apply, eq_comm] using this
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext x
    simp [Finset.sum_apply, hc x x.2]

theorem span_lineDer {K : Subgroup (GAd σ J)} {S : Set (GAd σ J)} (hSK : ∀ k ∈ S, ∀ k' ∈ K, k * k' ∈ S)
    {e : ℕ} {b : Fin e → GAd σ J → ℂ} (hb : ∀ j, ∀ k' ∈ K, ∃ c : Fin e → ℂ, ∀ k ∈ S, b j (k * k') = ∑ l, c l * b l k)
    {f : GAd σ J → ℂ} (hf : ∃ c : Fin e → ℂ, ∀ k ∈ S, f k = ∑ j, c j * b j k)
    {ζ : ℝ → GAd σ J} (hζK : ∀ s, ζ s ∈ K) (hd : ∀ k ∈ S, DifferentiableAt ℝ (fun t => f (k * ζ t)) 0) :
    ∃ c : Fin e → ℂ, ∀ k ∈ S, lineDer ζ f k = ∑ j, c j * b j k := by
  set V : Submodule ℂ (S → ℂ) := Submodule.span ℂ (Set.range fun j (x : S) => b j x) with hV
  have hshift : ∀ t, (fun x : S => f (x * ζ t)) ∈ V := by
    intro t
    obtain ⟨c, hc⟩ := hf
    have hbj : ∀ j, (fun x : S => b j (x * ζ t)) ∈ V := fun j => (mem_span_iff b (fun x => b j (x * ζ t))).2 (hb j _ (hζK t))
    have : (fun x : S => f (x * ζ t)) = ∑ j, c j • fun x : S => b j (x * ζ t) := by
      funext x
      simp [Finset.sum_apply, hc _ (hSK x x.2 _ (hζK t))]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbj j)
  haveI : FiniteDimensional ℂ V := by
    rw [hV]; first | exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _) | exact Module.Finite.span_of_finite ℂ (Set.finite_range _)
  have hclosed : IsClosed ((V.restrictScalars ℝ : Submodule ℝ (S → ℂ)) : Set (S → ℂ)) :=
    Submodule.closed_of_finiteDimensional V
  have hslope : ∀ t : ℝ, (fun x : S => slope (fun t => f (x * ζ t)) 0 t) ∈ V.restrictScalars ℝ := by
    intro t
    have : (fun x : S => slope (fun t => f (x * ζ t)) 0 t) =
        (t - 0)⁻¹ • ((fun x : S => f (x * ζ t)) - fun x : S => f (x * ζ 0)) := by
      funext x; simp [slope_def_module]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hshift t) (hshift 0))
  have hlim : Filter.Tendsto (fun t : ℝ => fun x : S => slope (fun t => f (x * ζ t)) 0 t) (𝓝[≠] (0 : ℝ))
      (𝓝 fun x : S => lineDer ζ f x) :=
    tendsto_pi_nhds.2 fun x => hasDerivAt_iff_tendsto_slope.1 (hd x x.2).hasDerivAt
  have hmem : (fun x : S => lineDer ζ f x) ∈ V := hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hslope)
  exact (mem_span_iff b _).1 hmem

theorem bounded_differentiable_foldr_lineDer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (K : Subgroup (GAd σ J)) (S : Set (GAd σ J)), IsCompact S → (∀ k ∈ S, ∀ k' ∈ K, k * k' ∈ S) →
    ∀ (e : ℕ) (b : Fin e → GAd σ J → ℂ), (∀ j, ContinuousOn (b j) S) →
      (∀ j, ∀ k' ∈ K, ∃ c : Fin e → ℂ, ∀ k ∈ S, b j (k * k') = ∑ l, c l * b l k) →
    ∀ a : GAd σ J → ℂ, (∃ c : Fin e → ℂ, ∀ k ∈ S, a k = ∑ j, c j * b j k) →
      (∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => a (k * (List.ofFn fun j => γ j (t j)).prod)) →
      ∀ l : List (ℝ → GAd σ J), (∀ ζ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ J ζ ∧ ∀ s, ζ s ∈ K) →
        (∃ C : ℝ, ∀ k ∈ S, ‖l.foldr GlobalTheory.SiegelSet.lineDer a k‖ ≤ C) ∧
        ∀ ζ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J ζ → (∀ s, ζ s ∈ K) → ∀ k ∈ S,
          DifferentiableAt ℝ (fun t => l.foldr GlobalTheory.SiegelSet.lineDer a (k * ζ t)) 0 := by
  intro F E _ _ _ _ _ σ _ n J K S hS hSK e b hbc hb a ha hsa
  have good : ∀ l : List (ℝ → GAd σ J), (∀ ζ ∈ l, IsRealLine σ J ζ ∧ ∀ s, ζ s ∈ K) →
      (∃ c : Fin e → ℂ, ∀ k ∈ S, l.foldr lineDer a k = ∑ j, c j * b j k) ∧
      ∀ k ∈ S, ∀ (m : ℕ) (γ : Fin m → ℝ → GAd σ J), (∀ j, IsRealLine σ J (γ j)) → (∀ j s, γ j s ∈ K) →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin m → ℝ => l.foldr lineDer a (k * (List.ofFn fun j => γ j (t j)).prod) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨ha, hsa⟩
    | cons ζ l ih =>
      intro hl
      obtain ⟨hζ, hζK⟩ := hl ζ List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih fun ζ' h => hl ζ' (List.mem_cons_of_mem _ h)
      exact ⟨span_lineDer hSK hb h1 hζK (differentiableAt_of_smooth h2 hζ hζK),
        smooth_lineDer h2 hζ hζK⟩
  intro l hl
  obtain ⟨⟨c, hc⟩, hs⟩ := good l hl
  refine ⟨?_, fun ζ hζ hζK k hk => differentiableAt_of_smooth hs hζ hζK k hk⟩
  have hcont : ContinuousOn (fun k => ∑ j, c j * b j k) S :=
    continuousOn_finset_sum _ fun j _ => continuousOn_const.mul (hbc j)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  exact ⟨C, fun k hk => by rw [hc k hk]; exact hC k hk⟩

end GlobalTheory.ThK.KFinCoef
