import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLeftInverseExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementDualLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneComplementSplitBasis

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.ComplPair

theorem isPair_compl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → G.q = 0 → 1 ≤ G.p →
      ∀ (M₁ : Model σ G.V W₁) (om₁ : Rep σ G.V W₁), M₁.IsGood B.ψ → M₁.IsWeil B.ψ X.β (X.β / X.α) om₁ →
        IsPair B M₁ X.β (X.β / X.α) om₁ (a - G.p) G.p (a + a' - G.p - 1) (G.p - 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH' hq _ M₁ om₁ hM₁ hom₁
  have hP := (Check.isPair_of_isTriple hT).1
  have hW : G.W.IsSkew σ B (a + a' - G.p) G.p := by
    have h := hT.geo.hW
    rwa [hq, add_zero] at h
  obtain ⟨P, hPι⟩ := GlobalTheory.plane_iota_leftInverse F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH'
  have hW₁ : W₁.IsSkew σ B (a + a' - G.p - 1) (G.p - 1) :=
    ⟨GlobalTheory.plane_compl_skew F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH',
      GlobalTheory.SkewPlaneSig.hasSig_skew_complement F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH' P hPι,
      GlobalTheory.isLattice_complement_of_adapted_plane F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH' P hPι,
      GlobalTheory.AdaptedPlaneDual.dual_complement F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH',
      GlobalTheory.SkewPlane.cartan_compl F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH' P hPι,
      GlobalTheory.AdaptedPlaneBasis.isSplitBasis_of_isAdapted F E σ B hT.base _ _ G.W W₁ H' i₀ i₁ _ _ hW hH'⟩
  have hres₁ : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.β / X.α) d₁ := by
    intro u
    rw [hP.resW u, hH'.rank, pow_add, neg_one_sq, mul_one]
  exact ⟨hT.base, hT.geo.hV, hW₁, hM₁, hP.hX, hP.hW, hP.resX, hres₁, hom₁⟩

end GlobalTheory.ThK.ComplPair
