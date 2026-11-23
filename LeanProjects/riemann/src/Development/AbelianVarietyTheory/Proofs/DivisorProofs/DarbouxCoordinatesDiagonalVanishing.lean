import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox

noncomputable section

namespace GlobalTheory.DblEvalLeft

open GlobalTheory.DblEvalLaw

theorem siegel_law_and_mem_degPSOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (J : Matrix (Fin n) (Fin n) E) (X₂ : Spc F E (n + n)), X₂.J = dblGram finSumFinEquiv J →
    ∀ (W : Spc F E d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X₂.J) (incM F W.J)) (Fin (n + n) × Fin d)),
    (∀ u, (∀ j, uᵀ j ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
    ∀ (χ₁ χ : Chr F E) (om₂ : Rep σ X₂ W), IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X₂.J) (incM F W.J) co χ₁ χ om₂ →
    (∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ∀ φ ∈ schA F (Fin (n + n) × Fin d),
      om₂ ((p : UA σ X₂.J), 1) φ 0 = (χ (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) : ℂ) *
        GlobalTheory.Doubling.npow (absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) ((d : ℂ) / 2) * φ 0) ∧
    ∀ K : Subgroup (UA σ X₂.J), ∀ Φ ∈ schA F (Fin (n + n) × Fin d),
      FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (k, 1) Φ}) →
      (fun g => om₂ (g, 1) Φ 0) ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K χ (((d : ℂ) - (n : ℂ)) / 2) := by
  intro F E _ _ _ _ _ σ B n d J X₂ hX₂ W co hΔ χ₁ χ om₂ hom
  obtain ⟨-, ⟨d', hd', hsplB, dd, omd, hdc, ⟨-, hus, hSR⟩, hbox⟩, hcont⟩ := hom
  have hJB : incM F X₂.J = blkMat finSumFinEquiv (incM F J) (-(incM F J)) := by
    rw [hX₂, dblGram, incM, incM, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
  have hΔ' : ∀ u : Matrix (Fin d) (Fin (n + n)) (AE F E), (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) →
      (d'.e u).1 = 0 := fun u hu => by
    have h := hd' uᵀ
    rw [Matrix.transpose_transpose] at h
    rw [h]
    exact hΔ uᵀ (by simpa only [Matrix.transpose_transpose] using hu)
  have hev := proj_mem_adm F (Fin (n + n) × Fin d ⊕ Fin (n + n) × Fin d) 0
  have law : ∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype, ∀ φ ∈ schA F (Fin (n + n) × Fin d),
      om₂ ((p : UA σ X₂.J), 1) φ 0 = (χ (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p) : ℂ) *
        GlobalTheory.Doubling.npow (absE F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) ((d : ℂ) / 2) * φ 0 := by
    intro p φ hφ
    have hk := apply_zero_of_keepsDiag finSumFinEquiv hJB hdc hus.toIsSplitting hSR hbox hΔ' hev
      (fun φ₁ h₁ φ₂ h₂ => GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ₁ h₁ φ₂ h₂)
      (GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F _) (p : UA σ X₂.J) p.2 φ hφ
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply] at hk
    have hsc : ∀ u : (AE F E)ˣ, ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) u) : ℝ) ^
        ((Fintype.card (Fin d) : ℝ) / 2) : ℝ) : ℂ) = GlobalTheory.Doubling.npow (absE F E u) ((d : ℂ) / 2) := by
      intro u
      rw [GlobalTheory.ModuAdele.modu_norm_eq_absE, GlobalTheory.Doubling.npow, Complex.ofReal_cpow (NNReal.coe_nonneg _)]
      congr 1
      push_cast
      simp only [Fintype.card_fin]
    rw [hk, hsc]
    rfl
  refine ⟨law, fun K Φ hΦ hfin => ?_⟩
  rw [mem_degPSOf]
  refine ⟨fun p g => ?_, ?_, ?_⟩
  · have hφ : om₂ (g, 1) Φ ∈ schA F (Fin (n + n) × Fin d) := hsplB.pres g Φ hΦ
    have hmul : om₂ ((p : UA σ X₂.J) * g, 1) Φ = om₂ ((p : UA σ X₂.J), 1) (om₂ (g, 1) Φ) := by
      rw [show ((p : UA σ X₂.J) * g, (1 : UA σ W.J)) = ((p : UA σ X₂.J), 1) * (g, 1) by simp, map_mul,
        Module.End.mul_apply]
    have he : ((d : ℂ) - (n : ℂ)) / 2 + (Fintype.card (Fin n) : ℂ) / 2 = (d : ℂ) / 2 := by
      simp only [Fintype.card_fin]
      ring
    rw [hmul, law p _ hφ, ← he]
  · exact (hcont _ (proj_mem_adm F _ 0) Φ hΦ).comp (continuous_id.prodMk continuous_const)
  · let L : ((Fin (n + n) × Fin d → AF F) → ℂ) →ₗ[ℂ] (UA σ X₂.J → ℂ) :=
      { toFun := fun Ψ g => om₂ (g, 1) Ψ 0
        map_add' := fun Ψ Ψ' => funext fun g => by simp
        map_smul' := fun a Ψ => funext fun g => by simp }
    haveI := hfin
    refine isKFinite_iff.2 ⟨(Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om₂ (k, 1) Φ}).map L, inferInstance, fun k hk => ?_⟩
    refine ⟨om₂ (k, 1) Φ, Submodule.subset_span ⟨k, hk, rfl⟩, funext fun g => ?_⟩
    show om₂ (g, 1) (om₂ (k, 1) Φ) 0 = om₂ (g * k, 1) Φ 0
    rw [show (g * k, (1 : UA σ W.J)) = (g, 1) * (k, 1) by simp, map_mul, Module.End.mul_apply]

end GlobalTheory.DblEvalLeft

end
