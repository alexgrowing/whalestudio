import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNormOneIdeles
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.SplitApprox
open GlobalTheory.AdelicU.Supp

theorem strongApprox_split_herm : GlobalTheory.Published.StrongApproxSU → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (V : Spc F E n) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s → 2 ≤ n → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) →
    ∀ g : UA σ V.J, (mat g).det = 1 → g ∈ closure {x | ∃ γ ∈ ratU σ V.J, ∃ k ∈ UAt σ V (evFin F v), x = γ * k} := by
  intro H F E _ _ _ _ _ σ B n V r s hB hV h2 v hτ g hg
  have hcm := hB.cm
  let w0 := (inferInstance : Nonempty (InfinitePlace F)).some
  have hVd : V.J.det ≠ 0 := det_ne_zero_of_map _ _ (det_ne_zero_of_hasSig (hV.sig w0))
  have hδ : (1 : E) ≠ 0 := one_ne_zero
  have hJ' : IsHermND σ ((1 : E) • V.Jᵀ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_one, one_mul, hV.herm]
    · rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hδ) hVd
  have hidem := isPlacesIdem_placeIdem (F := F) v
  let τ := hτ.some
  have hnc := GlobalTheory.Published.StrongApprox.not_isCompact_split σ h2 hJ' v (placeIdem v)
    (hidem.2.2.1 v (Finset.mem_singleton_self _)) (splitIdemAd hcm τ) (splitIdemAd_mul_self hcm _)
    (splitIdemAd_mul_sigR hcm _) (splitIdemAd_add_sigR hcm _)
  let g' : HA (AF F) σ ((1 : E) • V.Jᵀ) :=
    (⟨g.1, (mem_UG_iff_mem_HR _ hδ _).1 g.2⟩ : HR (AF F) σ ((1 : E) • V.Jᵀ))
  have hg' : g' ∈ GlobalTheory.Published.SUAdelic σ ((1 : E) • V.Jᵀ) := GlobalTheory.Published.StrongApprox.mem_SUAdelic.2 hg
  have hcl := H F E σ hcm _ _ h2 hJ' ∅ {v} _ hidem hnc g' hg'
  have e : toUA V.J hδ g' = g := rfl
  rw [← e]
  refine map_mem_closure (continuous_toUA V.J hδ) hcl ?_
  rintro y ⟨γ, hγ, k, hk, rfl⟩
  refine ⟨toUA V.J hδ γ, ?_, toUA V.J hδ k, ?_, map_mul _ _ _⟩
  · obtain ⟨γ0, -, hγ0⟩ := Subgroup.mem_map.1 hγ.2
    exact Subgroup.mem_subgroupOf.2 ⟨γ0, hγ0⟩
  · intro u hu
    ext i j
    have hk2 := hk.2 i j
    change u • ((HA.mat (AF F) σ _ k).1 - 1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j = 0
    rw [Algebra.smul_def, ← hk2, ← mul_assoc, ← map_mul, mul_placeIdem hu, map_zero, zero_mul]

end GlobalTheory.SplitApprox
