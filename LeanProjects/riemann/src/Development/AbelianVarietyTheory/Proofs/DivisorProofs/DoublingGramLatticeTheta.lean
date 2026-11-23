import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableTsumComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatOpenClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactOfIsStabSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingGramLatticeFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingGramLatticeSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingGramLatticeThirdStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DoublingUnfoldCusp

theorem unfold_cusp : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
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
    ∃ R₀ : ℝ, (d : ℝ) / 2 ≤ R₀ ∧ ∀ s : ℂ, R₀ < s.re →
      Integrable (fun g => (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (1, g)) * (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) μ ∧
      ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
      ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → GlobalTheory.ThKLiftCusp.IsCuspW W f →
      ∀ h, ∫ h' in 𝓕, f h' * (GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, h')) * (((χX (Matrix.GeneralLinearGroup.det h'.1))⁻¹ : Circle) : ℂ)) ∂μ =
        ∫ g, ((flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (1, g)) * (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ)) * f (h * g) ∂μ := by
  intro hKP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  obtain ⟨R₁, hR₁⟩ := GlobalTheory.T.doubling_gram_lattice_first hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  obtain ⟨R₂, hR₂⟩ := GlobalTheory.T.doubling_gram_lattice_second hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  have hlaw := GlobalTheory.DoubledFlatDiag.flatOf_diag hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  obtain ⟨hrat, hinj, hα1, hcnt⟩ := GlobalTheory.DoublingRat.rat_open_classes hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  obtain ⟨hic, hΦc, hwc⟩ := GlobalTheory.DblUnfoldCont.continuity_pair hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  have hvan := GlobalTheory.T.doubling_gram_lattice_third hKP F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  haveI := hμ
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalRing (Matrix (Fin d) (Fin d) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalRing (Matrix (Fin (d + d)) (Fin (d + d)) (AE F E)) := Matrix.topologicalRing
  haveI : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (GL (Fin (d + d)) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  haveI : IsTopologicalGroup (UA σ W₂.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI := hcnt
  refine ⟨max ((d : ℝ) / 2) (max R₁ R₂), le_max_left _ _, fun s hs => ?_⟩
  have h0 : (d : ℝ) / 2 < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have h1 : R₁ < s.re := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have h2 : R₂ < s.re := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  refine ⟨hR₁ s h1, fun 𝓕 h𝓕 f hf hfΓ hfd hcusp h => ?_⟩
  have hfin := hR₂ s h2 𝓕 h𝓕 f hf hfΓ hfd h
  exact GlobalTheory.UnfoldPartial.unfold_of_nonopen_zero i _ _ (ratU σ W.J) μ 𝓕 _ f
    (fun g : UA σ W.J => (((χX (Matrix.GeneralLinearGroup.det g.1))⁻¹ : Circle) : ℂ))
    (fun h : UA σ W.J => ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ)) hic h𝓕 (hLI s h0).1 (hΦc s) hrat hinj
    (hLI s h0).2 hf hfΓ hwc
    (fun x y => by simp only [Subgroup.coe_mul, map_mul, mul_inv, Circle.coe_mul])
    (fun γ hγ => by simp only [hα1 γ hγ, inv_one, Circle.coe_one])
    (fun x => Circle.norm_coe _) (hlaw s)
    (fun h => by rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]) h hfin
    (hvan s h0 𝓕 h𝓕 f hf hfΓ hfd hcusp h hfin)

end GlobalTheory.DoublingUnfoldCusp

end
