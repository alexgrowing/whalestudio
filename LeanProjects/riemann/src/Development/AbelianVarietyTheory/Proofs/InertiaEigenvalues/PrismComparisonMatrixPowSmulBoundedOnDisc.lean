import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDiscStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormBreuilKisinHomUniformizerFrobeniusLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem comparisonMatrix_bounded : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f) bk.J ι → ∀ ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀), ht.Rel (BK.hf f X) f g ε → ∃ (k : ℕ) (x : Matrix (Fin d) (Fin d) B.A), x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε := by
  intro l _ K bk d ρ τ s ht hper B f g ι tb ε hrel
  have hnorm := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f g
  let Φ : Disc l (BK.hf f X) bk.ρ₀ →+* Disc l (BK.hf f X) bk.ρ₀ := Disc.map B.D.φ hnorm.2
  have hΦ : IsDiscMap B.D.φ Φ := isDiscMap_map _ _
  have hreg := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f) ι tb
  have hpair := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  have heq := GlobalTheory.T.comparisonMatrix_frobenius_disc l K bk d ρ τ s ht hper B f hreg.2.1 f g ε hrel Φ hΦ
  have hQ : ht.A.map (BK.hf g) * ht.A'.map (BK.hf g) =
      BK.hf g bk.E ^ ht.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
    rw [← Matrix.map_mul (f := BK.hf g), ht.A_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _), map_pow]
  obtain ⟨h, c, hc⟩ := GlobalTheory.T.matrix_phi_equation_to_family_equation B.A (Disc l (BK.hf f X) bk.ρ₀) (toDisc l (BK.hf f X) bk.ρ₀) Φ
    (BK.hf f bk.E) (BK.hf g bk.E) hpair.2.1 d d (ht.a + s.N) (ht.a + s.N) ht.b (ht.A.map (BK.hf f))
    (ht.A.map (BK.hf g)) (ht.A'.map (BK.hf g)) hQ ε heq
  have hφX : B.D.φ (BK.hf f X) = BK.hf f X ^ l := by
    have h1 : B.D.φ (f.f X) = f.f (bk.prism.D.φ X) := (f.f_φ X).symm
    have h2 : bk.prism.D.φ X = X ^ l := frobS_X l bk.a
    exact h1.trans ((congrArg f.f h2).trans (map_pow f.f _ l))
  have key := GlobalTheory.T.exists_bounded_of_phi_equation_disc l K bk B.A (BK.hf f) ι tb B.D.φ hφX Φ hΦ (Fin d × Fin d) c
    (fun _ _ => Set.toFinite _) h (fun j => ε j.1 j.2)
  have htend : Filter.Tendsto (fun j : Fin d × Fin d => ε j.1 j.2) Filter.cofinite
      (nhds (0 : Disc l (BK.hf f X) bk.ρ₀)) := by
    simp only [Filter.cofinite_eq_bot, Filter.tendsto_bot]
  have hsum : ∀ j : Fin d × Fin d, HasSum (fun i => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
      (toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2) := fun j => by
    have hs := hasSum_fintype (fun i : Fin d × Fin d => Φ (ε i.1 i.2) * toDisc l (BK.hf f X) bk.ρ₀ (c i j))
    have e : toDisc l (BK.hf f X) bk.ρ₀ (BK.hf f bk.E) ^ h * ε j.1 j.2 =
        ∑ k : Fin d × Fin d, Φ (ε k.1 k.2) * toDisc l (BK.hf f X) bk.ρ₀ (c k j) := hc j
    convert hs using 1
  have k2 := key htend hsum
  obtain ⟨k, v, hv, -⟩ := k2
  refine ⟨k, Matrix.of fun i j => v (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (i, j)

end GlobalTheory.BSP
