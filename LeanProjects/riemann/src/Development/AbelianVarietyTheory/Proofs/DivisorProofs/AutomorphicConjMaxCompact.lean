import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.StdPar.RealConj

open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}

theorem commute_real_fin {a k : GAd σ J} (ha : a ∈ infPts σ J) (hk : k ∈ finPts σ J) : Commute a k :=
  (GAd_ext σ J (fun w => by simp [mem_finPts_iff_forall.1 hk w]) fun v => by simp [mem_infPts_iff_forall.1 ha v] :
    a * k = k * a)

theorem foldr_lineDer_rightConj (a : GAd σ J) (f : GAd σ J → ℂ) (l : List (ℝ → GAd σ J)) :
    l.foldr lineDer (fun x => f (x * a)) =
      fun x => (l.map fun γ t => a⁻¹ * γ t * a).foldr lineDer f (x * a) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    simp [mul_assoc]

variable {K₁ K₂ : Subgroup (GAd σ J)} {a : GAd σ J}

theorem isAutOn_realConj (hCM : IsCMExt F E σ) (ha : a ∈ infPts σ J) (hK : ∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁)
    {ψ : GAd σ J → ℂ} (h : IsAutOn σ J X Y S K₂ ψ) : IsAutOn σ J X Y S K₁ (fun y => ψ (y * a)) := by
  refine ⟨fun u hu g => ?_, fun γ hγ hγ' g => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_assoc]; exact h.leftN u hu _
  · simp only [mul_assoc]; exact h.leftM γ hγ hγ' _
  · obtain ⟨U, hU, hUψ⟩ := h.level
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    show ψ (g * k * a) = ψ (g * a)
    rw [mul_assoc, ← (commute_real_fin ha hkf).eq, ← mul_assoc]
    exact hUψ k hk hkf _
  · exact h.cont.comp (continuous_id.mul continuous_const)
  · exact GlobalTheory.EisCont.CentreFinite.isSm_mul_right hCM h.smooth a
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN (l.map fun γ t => a⁻¹ * γ t * a) (by
      intro γ' hγ'
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hγ'
      exact GlobalTheory.EisCont.CentreFinite.isRealLine_conj hCM (hl γ hγ) a)
    refine ⟨max C 0 * (height σ J a : ℝ) ^ N, fun g => ?_⟩
    rw [foldr_lineDer_rightConj]
    have hh : (height σ J (g * a) : ℝ) ≤ (height σ J g : ℝ) * (height σ J a : ℝ) := by
      exact_mod_cast height_mul_le σ J g a
    have h0 : (0 : ℝ) ≤ (height σ J (g * a) : ℝ) := by positivity
    calc ‖(l.map fun γ t => a⁻¹ * γ t * a).foldr lineDer ψ (g * a)‖ ≤ C * (height σ J (g * a) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height σ J (g * a) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height σ J g : ℝ) * (height σ J a : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)
      _ = max C 0 * (height σ J a : ℝ) ^ N * (height σ J g : ℝ) ^ N := by ring
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : K₂ => fun g => ψ (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * a)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    have hk2 : a⁻¹ * k * a ∈ K₂ := (hK _).2 (by simpa [mul_assoc] using hk)
    refine ⟨fun g => ψ (g * (a⁻¹ * k * a)), Submodule.subset_span ⟨⟨_, hk2⟩, rfl⟩, ?_⟩
    funext g
    simp [LinearMap.funLeft_apply, Function.comp, mul_assoc]
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z ψ}).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * a)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨dop z ψ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    funext g
    exact (hz.2 ψ h.smooth a ha g).symm

theorem isCuspOn_realConj (hCM : IsCMExt F E σ) (ha : a ∈ infPts σ J) (hK : ∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁)
    {ψ : GAd σ J → ℂ} (h : IsCuspOn σ J X Y S K₂ ψ) : IsCuspOn σ J X Y S K₁ (fun y => ψ (y * a)) :=
  ⟨isAutOn_realConj hCM ha hK h.1, fun S' hS' μ 𝓕 h1 h2 h3 g => by
    have := h.2 S' hS' μ 𝓕 h1 h2 h3 (g * a)
    simpa only [mul_assoc, Pi.zero_apply] using this⟩

theorem isCuspComp_zero_realConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E),
      GlobalTheory.SiegelSet.IsWittFrame σ J X Y → ∀ (K₁ K₂ : Subgroup (GAd σ J)) (a : GAd σ J), a ∈ GlobalTheory.AdelicU.infPts σ J →
        (∀ k, k ∈ K₂ ↔ a * k * a⁻¹ ∈ K₁) → ∀ (S : Finset (Fin r)) (φ : GAd σ J → ℂ),
          GlobalTheory.StdPar.IsCuspComp σ J X Y S K₁ φ 0 → GlobalTheory.StdPar.IsCuspComp σ J X Y S K₂ φ 0 := by
  intro F E _ _ _ _ _ σ hCM n J _ r X Y _ K₁ K₂ a ha hK S φ h
  have hK' : ∀ k, k ∈ K₁ ↔ a⁻¹ * k * a⁻¹⁻¹ ∈ K₂ := fun k => by
    rw [hK]; simp [mul_assoc]
  obtain ⟨h0, c, hc, hs⟩ := h
  refine ⟨?_, c, hc, fun ψ hψ μ 𝓕 h1 h2 g g' => ?_⟩
  · exact isCuspOn_realConj hCM (inv_mem ha) hK' h0
  · have := hs _ (isCuspOn_realConj hCM ha hK hψ) μ 𝓕 h1 h2 g (g' * a⁻¹)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this

end GlobalTheory.StdPar.RealConj
