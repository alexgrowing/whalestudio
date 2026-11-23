import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT.Indep

theorem integral_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ Φ : unipRad σ J (col0 X) → ℂ, (∀ (ν : (ratPts σ J).subgroupOf (unipRad σ J (col0 X))) u, Φ (ν • u) = Φ u) →
    ∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
    ∀ (μ' : Measure (unipRad σ J (col0 X))) (𝓕' : Set (unipRad σ J (col0 X))), μ'.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕' μ' → μ' 𝓕' = 1 →
    ∫ u in 𝓕, Φ u ∂μ = ∫ u in 𝓕', Φ u ∂μ' := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS Φ hΦ μ 𝓕 hμ h𝓕 h1 μ' 𝓕' hμ' h𝓕' h1'
  obtain ⟨hCM, -, hJ, -, hW, -, -⟩ := hS
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (col0 X) := by
    have e : col0 X = X.submatrix id (Fin.castLE (show 1 ≤ r + 1 by omega)) := by
      ext i j
      rw [Subsingleton.elim j 0]
      rfl
    rw [e]
    exact GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  classical
  let φ : GAd σ J → ℂ := fun x => if hx : x ∈ unipRad σ J (col0 X) then Φ ⟨x, hx⟩ else 0
  have e : (ratPts σ J ⊓ unipRad σ J (col0 X)).subgroupOf (unipRad σ J (col0 X)) = (ratPts σ J).subgroupOf (unipRad σ J (col0 X)) :=
    Subgroup.ext fun u => ⟨fun hu => (Subgroup.mem_subgroupOf.1 hu).1,
      fun hu => Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hu, u.2⟩⟩
  have hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (ratPts σ J ⊓ unipRad σ J (col0 X)) φ := by
    intro γ hγ g
    by_cases hg : g ∈ unipRad σ J (col0 X)
    · have hγg : γ * g ∈ unipRad σ J (col0 X) := (unipRad σ J (col0 X)).mul_mem hγ.2 hg
      simp only [φ, dif_pos hg, dif_pos hγg]
      have hν : (⟨γ, hγ.2⟩ : unipRad σ J (col0 X)) ∈ (ratPts σ J).subgroupOf (unipRad σ J (col0 X)) := Subgroup.mem_subgroupOf.2 hγ.1
      exact hΦ ⟨_, hν⟩ ⟨g, hg⟩
    · have hγg : γ * g ∉ unipRad σ J (col0 X) := fun h' => hg (by simpa using (unipRad σ J (col0 X)).mul_mem ((unipRad σ J (col0 X)).inv_mem hγ.2) h')
      simp only [φ, dif_neg hg, dif_neg hγg]
  have k1 := GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h𝓕) h1 hφ 1
  have k2 := GlobalTheory.Cusp.constTermOn_eq_of_measure_eq_one (e ▸ h𝓕') h1' hφ 1
  have hφN : ∀ u : unipRad σ J (col0 X), φ (u * 1) = Φ u := fun u => by simp [φ]
  simp only [hφN] at k1 k2
  exact k1.symm.trans k2

end GlobalTheory.EisCT.Indep
