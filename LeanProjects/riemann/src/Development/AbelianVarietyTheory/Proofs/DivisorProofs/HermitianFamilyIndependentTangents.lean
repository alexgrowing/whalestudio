import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

namespace GlobalTheory.LieMetFam

theorem exists_hermFam_met : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (K : Type) [Field K] [NumberField K] (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z), yK ≫ genStr O.s.T.Z = spMap fK → ∀ {n : ℕ} (b : Fin n → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G), (∀ σ : K →+* ℂ, LinearIndependent ℂ (fun i => bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (b i))) → ∃ h : HermFam K (Fin n → K), ∀ (σ : K →+* ℂ) (z : GlobalTheory.CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin n → K), h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i)) (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i)) := by
  intro D O x K _ _ fK yK hK n b hb
  classical
  have hz0 : ∀ σ : K →+* ℂ, (spMap σ ≫ yK) ≫ genStr O.s.T.Z = spMap (σ.comp fK) := fun σ => by
    rw [Category.assoc, hK, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  let z0 : ∀ σ : K →+* ℂ, GlobalTheory.CxPts (genStr O.s.T.Z) (σ.comp fK) := fun σ => ⟨spMap σ ≫ yK, hz0 σ⟩
  let B : ∀ σ : K →+* ℂ, (Fin n → K) → TanM ((z0 σ).1 ≫ genι O.s.T.Z) O.s.T.Z.t.G := fun σ w =>
    bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (∑ i, w i • b i)
  have hBadd : ∀ σ w w', B σ (w + w') = B σ w + B σ w' := fun σ w w' => by
    simp only [B, Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add]
  have hBsmul : ∀ σ (a : K) w, B σ (a • w) = σ a • B σ w := fun σ a w => by
    simp only [B, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smulₛₗ]
  have hBsum : ∀ σ w, B σ w = ∑ k, σ (w k) • bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (b k) :=
    fun σ w => by simp only [B, map_sum, map_smulₛₗ]
  have hh : ∀ σ : K →+* ℂ, IsBlockMetric (x.met (σ.comp fK) (z0 σ)) := fun σ =>
    (x.met_smooth (σ.comp fK)).1 (z0 σ)
  refine ⟨{ form := fun σ u v => x.met (σ.comp fK) (z0 σ) (B σ v) (B σ u),
            add_right := fun σ u v w => by simp only [hBadd, map_add, LinearMap.add_apply],
            smul_right := fun σ a u v => by simp only [hBsmul, map_smul, LinearMap.smul_apply, smul_eq_mul],
            conj_symm := fun σ u v => ((hh σ).1 _ _).symm,
            posDef := fun σ m v hv => ?_ }, ?_⟩
  · have hli : LinearIndependent ℂ (fun i => B σ (v i)) := by
      letI := σ.toAlgebra
      have h1 : LinearIndependent ℂ (fun i => algebraMap K ℂ ∘ v i) := linearIndependent_algebraMap_comp_iff.2 hv
      refine Fintype.linearIndependent_iff.2 fun g hg => ?_
      have h2 : ∑ k, (∑ i, g i * σ (v i k)) • bcTan σ (Category.assoc (spMap σ) yK (genι O.s.T.Z)).symm (b k) = 0 := by
        rw [← hg]
        simp only [hBsum, Finset.smul_sum, Finset.sum_smul, smul_smul]
        exact Finset.sum_comm
      have h3 := Fintype.linearIndependent_iff.1 (hb σ) _ h2
      refine Fintype.linearIndependent_iff.1 h1 g (funext fun k => ?_)
      simpa [Finset.sum_apply, RingHom.algebraMap_toAlgebra] using h3 k
    exact (hh σ).gram_posDef hli
  · intro σ z hz u v
    have e : z = ⟨spMap σ ≫ yK, hz0 σ⟩ := Subtype.ext hz
    subst e
    rfl

end GlobalTheory.LieMetFam
