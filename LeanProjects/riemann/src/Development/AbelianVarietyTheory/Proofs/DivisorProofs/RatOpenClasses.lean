import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
noncomputable section

namespace GlobalTheory.DoublingRat

theorem rat_open_classes : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    (∀ δ ∈ ratU σ W.J, i (1, δ) ∈ ratU σ W₂.J) ∧
      (∀ δ δ' : UA σ W.J, i (1, δ) * (i (1, δ'))⁻¹ ∈ (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) → δ = δ') ∧
      (∀ γ ∈ ratU σ W.J, χX (Matrix.GeneralLinearGroup.det γ.1) = 1) ∧ Countable (ratU σ W.J) := by
  intro _ F E _ _ _ _ _ σ B n m Xs W M χX χW om r s' r₁ s₁ hP _ W₂ _ _ _ i hi K _ _ φ₀ _ _ μ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro δ hδ
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hδ)
    refine Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨blkGL finSumFinEquiv ((1 : GL (Fin m) E), d), ?_⟩)
    apply Units.ext
    change ((blkGL finSumFinEquiv ((1 : GL (Fin m) E), d) : GL _ E) : Matrix _ _ E).map (inclR (AF F)) = mat (i (1, δ))
    rw [val_blkGL, blkMat_map _ _ (map_zero _), hi]
    have h1 : mat δ = (d : Matrix _ _ E).map (inclR (AF F)) := by
      show δ.1.val = _
      rw [← hd]; rfl
    rw [h1]
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  · intro δ δ' h
    rw [← map_inv, ← map_mul] at h
    have h2 := mem_siegelOf.1 h
    change KeepsDiag finSumFinEquiv (mat (i ((1, δ) * (1, δ')⁻¹))) at h2
    rw [hi, keepsDiag_blkMat] at h2
    have h3 : δ * δ'⁻¹ = 1 := by
      apply Subtype.ext
      apply Units.ext
      have h4 : mat (δ * δ'⁻¹) = mat (1 : UA σ W.J) := by simpa using h2
      exact h4
    exact mul_inv_eq_one.1 h3
  · intro γ hγ
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
    rw [← hd]
    have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (inclR (AF F)) d) =
        Units.map (inclR (F := F) (E := E) (AF F) : E →* AE F E) (Matrix.GeneralLinearGroup.det d) := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rw [h1]
    exact hP.hX.2 _
  · haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin m) (Fin m) E) :=
      inferInstanceAs (Countable (Fin m → Fin m → E))
    haveI : Countable (GL (Fin m) E) := Units.val_injective.countable
    haveI : Countable (Matrix.GeneralLinearGroup.map (n := Fin m) (inclR (F := F) (E := E) (AF F))).range :=
      MonoidHom.rangeRestrict_surjective _ |>.countable
    exact Function.Injective.countable (f := fun x : ratU σ W.J =>
      (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ :
        (Matrix.GeneralLinearGroup.map (n := Fin m) (inclR (F := F) (E := E) (AF F))).range))
      fun x y h => by
        have h' := congrArg Subtype.val h
        apply Subtype.ext; apply Subtype.ext; exact h'

end GlobalTheory.DoublingRat

end
