import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UAut.JointDer

theorem prod_ofFn_append {G : Type} [Monoid G] {d k : ℕ} (δ : Fin d → ℝ → G) (γ : Fin k → ℝ → G) (s : Fin d → ℝ)
    (t : Fin k → ℝ) :
    (List.ofFn fun i => Fin.append δ γ i (Fin.append s t i)).prod =
      (List.ofFn fun a => δ a (s a)).prod * (List.ofFn fun i => γ i (t i)).prod := by
  have e : (fun i => Fin.append δ γ i (Fin.append s t i)) = Fin.append (fun a => δ a (s a)) (fun i => γ i (t i)) := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  rw [e, List.ofFn_fin_append, List.prod_append]

theorem contDiff_append {d k : ℕ} : ContDiff ℝ ∞ fun q : (Fin d → ℝ) × (Fin k → ℝ) => Fin.append q.1 q.2 := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.addCases (fun a => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]; exact (contDiff_apply ℝ ℝ a).comp contDiff_fst
  · simp only [Fin.append_right]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd

theorem iteratedFDeriv_slice {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] {H : A × B → ℂ} (hH : ContDiff ℝ ∞ H) (m : ℕ) (a : A) (t : B) :
    iteratedFDeriv ℝ m (fun t => H (a, t)) t =
      (iteratedFDeriv ℝ m H (a, t)).compContinuousLinearMap fun _ => ContinuousLinearMap.inr ℝ A B := by
  have e : (fun t => H (a, t)) = (fun q => H ((a, 0) + q)) ∘ ContinuousLinearMap.inr ℝ A B := by
    funext t; simp
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _
    (show ContDiff ℝ ∞ fun q => H ((a, 0) + q) from hH.comp (contDiff_const.add contDiff_id)) _
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_left]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem commute_prod_realLine {k : ℕ} {γ : Fin k → ℝ → GAd σ J} (hγ : ∀ i, IsRealLine σ J (γ i)) (t : Fin k → ℝ)
    {u : GAd σ J} (hu : u ∈ finPts σ J) : Commute (List.ofFn fun i => γ i (t i)).prod u := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  obtain ⟨w, τ, Z, -, h⟩ := hγ i
  obtain ⟨y, e, -⟩ := h (t i)
  show Commute (γ i (t i)) u
  rw [e]
  exact commute_embArch σ J y (mem_finPts_iff_forall.1 hu w)

end GlobalTheory.UAut.JointDer

open GlobalTheory.UAut.JointDer in

theorem GlobalTheory.UAut.continuous_iteratedFDeriv_prod_realLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) → (∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧ ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u) → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → IsSm σ J φ → ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (γ i)) → ∀ m : ℕ, Continuous fun p : GAd σ J × (Fin k → ℝ) => iteratedFDeriv ℝ m (fun t : Fin k → ℝ => φ (p.1 * (List.ofFn fun i => γ i (t i)).prod)) p.2 := by
  intro F E _ _ _ _ _ σ _ n J _ d δ hδ hchart φ hlev hsm k γ hγ m
  obtain ⟨U, hUo, hU⟩ := hlev
  obtain ⟨W, hW, s, hs, hWs⟩ := hchart _ (hUo.mem_nhds U.one_mem)
  set P : (Fin k → ℝ) → GAd σ J := fun t => (List.ofFn fun i => γ i (t i)).prod with hP
  set Q : (Fin d → ℝ) → GAd σ J := fun s => (List.ofFn fun a => δ a (s a)).prod with hQ
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨x₀, t₀⟩ := p₀
  let H : (Fin d → ℝ) × (Fin k → ℝ) → ℂ := fun q => φ (x₀ * (Q q.1 * P q.2))
  have hH : ContDiff ℝ ∞ H := by
    have h1 := hsm (d + k) (Fin.append δ γ)
      (fun i => Fin.addCases (fun a => by simpa [Fin.append_left] using hδ a)
        (fun j => by simpa [Fin.append_right] using hγ j) i) x₀
    have h2 := h1.comp contDiff_append
    convert h2 using 1
    funext q
    simp only [Function.comp_apply, H, prod_ofFn_append, hP, hQ]
  have key : ∀ x, x₀⁻¹ * x ∈ W → ∀ t, φ (x * P t) = H (s (x₀⁻¹ * x), t) := by
    intro x hx t
    obtain ⟨u, huU, huf, e⟩ := hWs _ hx
    have hc : Commute (P t) u := commute_prod_realLine hγ t huf
    have hx' : x = x₀ * (Q (s (x₀⁻¹ * x)) * u) := by
      simp only [hQ]
      rw [← e]
      group
    calc φ (x * P t) = φ (x₀ * (Q (s (x₀⁻¹ * x)) * u) * P t) := by rw [← hx']
      _ = φ ((x₀ * (Q (s (x₀⁻¹ * x)) * P t)) * u) := by
          congr 1
          simp only [mul_assoc]
          rw [hc.eq]
      _ = H (s (x₀⁻¹ * x), t) := hU u huU huf _
  have hev : ∀ᶠ p : GAd σ J × (Fin k → ℝ) in 𝓝 (x₀, t₀),
      (iteratedFDeriv ℝ m H (s (x₀⁻¹ * p.1), p.2)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) =
      iteratedFDeriv ℝ m (fun t => φ (p.1 * P t)) p.2 := by
    have hmem : {p : GAd σ J × (Fin k → ℝ) | x₀⁻¹ * p.1 ∈ W} ∈ 𝓝 (x₀, t₀) :=
      (continuous_const.mul continuous_fst).continuousAt.preimage_mem_nhds (by simpa using hW)
    filter_upwards [hmem] with p hp
    rw [← iteratedFDeriv_slice hH, show (fun t => φ (p.1 * P t)) = fun t => H (s (x₀⁻¹ * p.1), t) from
      funext (key p.1 hp)]
  refine ContinuousAt.congr ?_ hev
  have hcont : Continuous fun q => (iteratedFDeriv ℝ m H q).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin k → ℝ)) :=
    (ContinuousMultilinearMap.continuous_precomp _).comp (hH.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  have hsx : ContinuousAt (fun p : GAd σ J × (Fin k → ℝ) => s (x₀⁻¹ * p.1)) (x₀, t₀) :=
    hs.comp_of_eq (continuous_const.mul continuous_fst).continuousAt (by simp)
  exact hcont.continuousAt.comp (hsx.prodMk continuousAt_snd)

end
