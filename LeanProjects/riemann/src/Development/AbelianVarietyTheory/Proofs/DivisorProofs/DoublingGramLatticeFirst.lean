import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingStabilizerCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingStabilizersStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DoublingZeta

theorem zeta_integrable : GlobalTheory.Published.SiegelEisensteinDoubled → GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → G.q = 0 → 1 ≤ G.p →
    ∀ W₂ : Spc F E ((a + a') + (a + a')), W₂.J = dblGram finSumFinEquiv G.W.J → W₂.L = sumLat finSumFinEquiv G.W.L G.W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (G.W.θ w) (-G.W.θ w)) →
    ∀ i : UA σ G.W.J × UA σ G.W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K X.α (-(a : ℂ) / 2),
    (∀ s : ℂ, ((a + a' : ℕ) : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s) g) →
    ∀ μ : Measure (UA σ G.W.J), μ.IsHaarMeasure →
    ∃ R₁ : ℝ, ∀ s : ℂ, R₁ < s.re → Integrable (fun g => (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (-(a : ℂ) / 2) s) (i (1, g)) * (((X.α (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) μ := by

  intro hSE hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM hq hp W₂ hJ hL hθ i hi K hK hI φ₀ hφ₀ hconv μ hμ
  have hKc : IsCompact (K : Set (UA σ W₂.J)) :=
    GlobalTheory.T.doubling_stabilizer_compact hKP F E σ B hM.triple.base (a + a') _ _ G.W hM.triple.geo.hW W₂ hJ hL hθ K hK
  obtain ⟨-, hfc, hαc⟩ := GlobalTheory.DblUnfoldCont.continuity hSE hKP F E σ B a a' G X om om' R Rf hM hq hp W₂ hJ hL hθ i hi K hK hI φ₀ hφ₀
    hconv μ hμ
  obtain ⟨R₀, hR₀⟩ := GlobalTheory.T.exists_integrable_hgtOf_rpow_doubling_embedding hKP F E σ B hM.triple.base (a + a') _ _ G.W hM.triple.geo.hW W₂ hJ hL hθ i hi K hK hI μ hμ
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hφ₀.2.1.continuousOn
  have hn : (Fintype.card (Fin (a + a')) : ℂ) = ((a + a' : ℕ) : ℂ) := by simp
  refine ⟨R₀ - ((a + a' : ℕ) : ℝ) / 2, fun s hs => ?_⟩
  have hint := hR₀ (s.re + ((a + a' : ℕ) : ℝ) / 2) (by linarith)
  have hio : Continuous fun g : UA σ G.W.J => i (1, g) := by
    obtain ⟨hic, -, -⟩ := GlobalTheory.DblUnfoldCont.continuity hSE hKP F E σ B a a' G X om om' R Rf hM hq hp W₂ hJ hL hθ i hi K hK hI φ₀ hφ₀
      hconv μ hμ
    exact hic.comp (continuous_const.prodMk continuous_id)
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  refine (hint.const_mul C).mono' (((hfc s).comp hio).mul hαc).aestronglyMeasurable (.of_forall fun g => ?_)
  set x := i (1, g)
  have hpos := hgtOf_pos (e := finSumFinEquiv) (mat := (UG (cA σ) (incM F W₂.J)).subtype) (ν := absE F E) (K := K) x
  have h1 : ‖φ₀ x‖ ≤ C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
      ((-(a : ℂ) / 2 + (Fintype.card (Fin (a + a')) : ℂ) / 2).re) :=
    IsIwasawa.norm_le hI hφ₀.1 (fun k hk => hC k hk) x
  have h2 := norm_flatSec (δ := absAOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E)) (K := K) φ₀ (-(a : ℂ) / 2) s x
  rw [norm_mul, Circle.norm_coe, mul_one]
  change ‖flatSec _ K φ₀ (-(a : ℂ) / 2) s x‖ ≤ _
  rw [h2]
  change ‖φ₀ x‖ * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ _ ≤ _
  rw [hn] at h1
  have hre : ((-(a : ℂ) / 2 + ((a + a' : ℕ) : ℂ) / 2)).re = -(a : ℝ) / 2 + ((a + a' : ℕ) : ℝ) / 2 := by simp
  have hre' : (-(a : ℂ) / 2).re = -(a : ℝ) / 2 := by simp
  rw [hre] at h1
  rw [hre']
  have hp0 : (0 : ℝ) < ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) := hpos
  calc ‖φ₀ x‖ * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ (s.re - -(a : ℝ) / 2)
      ≤ (C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
          (-(a : ℝ) / 2 + ((a + a' : ℕ) : ℝ) / 2)) *
        ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ (s.re - -(a : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp0.le _)
    _ = C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
          (s.re + ((a + a' : ℕ) : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add hp0]; congr 2; ring

theorem zeta_integrable_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
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
    ∃ R₁ : ℝ, ∀ s : ℂ, R₁ < s.re → Integrable (fun g => (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (1, g)) * (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) μ := by
  intro hKP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hI φ₀ hφ₀ hconv μ hμ
  have hKc : IsCompact (K : Set (UA σ W₂.J)) :=
    GlobalTheory.T.doubling_stabilizer_compact hKP F E σ B hP.base d _ _ W hP.skew W₂ hJ hL hθ K hK
  obtain ⟨hic, hfc, hαc⟩ := GlobalTheory.DblUnfoldCont.continuity_pair hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ
    i hi K hK hI φ₀ hφ₀ hconv μ hμ
  obtain ⟨R₀, hR₀⟩ := GlobalTheory.T.exists_integrable_hgtOf_rpow_doubling_embedding hKP F E σ B hP.base d _ _ W hP.skew W₂ hJ hL hθ i hi K hK hI μ hμ
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hφ₀.2.1.continuousOn
  have hn : (Fintype.card (Fin d) : ℂ) = (d : ℂ) := by simp
  refine ⟨R₀ - (d : ℝ) / 2, fun s hs => ?_⟩
  have hint := hR₀ (s.re + (d : ℝ) / 2) (by linarith)
  have hio : Continuous fun g : UA σ W.J => i (1, g) := hic.comp (continuous_const.prodMk continuous_id)
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  refine (hint.const_mul C).mono' (((hfc s).comp hio).mul hαc).aestronglyMeasurable (.of_forall fun g => ?_)
  set x := i (1, g)
  have hpos := hgtOf_pos (e := finSumFinEquiv) (mat := (UG (cA σ) (incM F W₂.J)).subtype) (ν := absE F E) (K := K) x
  have h1 : ‖φ₀ x‖ ≤ C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
      (((((n : ℂ) - (d : ℂ)) / 2) + (Fintype.card (Fin d) : ℂ) / 2).re) :=
    IsIwasawa.norm_le hI hφ₀.1 (fun k hk => hC k hk) x
  have h2 := norm_flatSec (δ := absAOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E)) (K := K) φ₀
    (((n : ℂ) - (d : ℂ)) / 2) s x
  rw [norm_mul, Circle.norm_coe, mul_one]
  change ‖flatSec _ K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s x‖ ≤ _
  rw [h2]
  change ‖φ₀ x‖ * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ _ ≤ _
  rw [hn] at h1
  have hre : ((((n : ℂ) - (d : ℂ)) / 2) + (d : ℂ) / 2).re = (((n : ℂ) - (d : ℂ)) / 2).re + (d : ℝ) / 2 := by simp
  rw [hre] at h1
  have hp0 : (0 : ℝ) < ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) := hpos
  calc ‖φ₀ x‖ * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ (s.re - (((n : ℂ) - (d : ℂ)) / 2).re)
      ≤ (C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
          ((((n : ℂ) - (d : ℂ)) / 2).re + (d : ℝ) / 2)) *
        ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^ (s.re - (((n : ℂ) - (d : ℂ)) / 2).re) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp0.le _)
    _ = C * ((hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K x : ℝ≥0) : ℝ) ^
          (s.re + (d : ℝ) / 2) := by
        rw [mul_assoc, ← Real.rpow_add hp0]; congr 2; ring

end GlobalTheory.DoublingZeta
