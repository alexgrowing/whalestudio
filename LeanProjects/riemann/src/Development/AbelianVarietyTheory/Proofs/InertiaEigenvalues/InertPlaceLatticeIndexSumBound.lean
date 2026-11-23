import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualSumLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPrimeIdemOfInert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasing
import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StdLatticeMapEqIffMemGLintValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInertStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.InertIdx

theorem indexSum_inert : ∀ (D : D7) (W : HSp D) (n : ℕ), 2 * W.rank + 5 ≤ n → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) → ∀ C : Finset (GA D W), (∀ g ∈ C, SuppF W f g ∧ g ∉ KsphC W ∅) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ KsphC W ∅ → g = g') → ∑ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) ≤ 8 * (Ideal.absNorm v.asIdeal : ℝ) ^ (-(4 : ℝ)) := by
  classical
  intro D W n hn v f hf ⟨w, hw⟩ C hC hdist
  obtain ⟨ε, hε, rfl⟩ := hf
  have hP := GlobalTheory.HeckeRowsCompare.isPrimeIdem_of_inert (P := w) hw hε
  have hc := GlobalTheory.LabChar.fixed_of_tie hP
  obtain ⟨ϖ, σ, q, π, hU, -, hCh, hV⟩ := GlobalTheory.InertLoc.exists_chart hc hP
  obtain ⟨β, ι, hFr, hGC⟩ := hV W
  obtain ⟨hσσ, hσv, -, -, ⟨x0, hx0, hx0v⟩, -, -⟩ := hU
  let K := GlobalTheory.InertLoc.LP D w
  let O := w.adicCompletionIntegers D.host.E

  have hσO : ∀ x : O, σ (x : K) ∈ O := fun x => by
    show Valued.v (σ (x : K)) ≤ 1
    rw [hσv]; exact x.2
  let cO : O ≃+* O :=
    { toFun := fun x => ⟨σ x, hσO x⟩, invFun := fun x => ⟨σ x, hσO x⟩,
      left_inv := fun x => Subtype.ext (hσσ x), right_inv := fun x => Subtype.ext (hσσ x),
      map_mul' := fun x y => Subtype.ext (map_mul σ _ _), map_add' := fun x y => Subtype.ext (map_add σ _ _) }
  let cK : K ≃+* K :=
    { toFun := σ, invFun := σ, left_inv := hσσ, right_inv := hσσ, map_mul' := map_mul σ, map_add' := map_add σ }

  let H : GA D W → Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K) := fun g =>
    if hg : SuppF W (algebraMap (AF D.host.F) (AE D) ε) g then (hGC.2.2.1 g hg).choose else 1
  have hH : ∀ g ∈ C, ι (H g) = g := fun g hg => by
    simp only [H, dif_pos (hC g hg).1]
    exact (hGC.2.2.1 g (hC g hg).1).choose_spec
  have hinj : Set.InjOn (fun g => ((H g : GL (Fin W.rank) K))) C := fun g hg g' hg' e => by
    rw [← hH g hg, ← hH g' hg', Subtype.ext e]
  have hsum := Finset.sum_image (f := fun x : GL (Fin W.rank) K =>
      ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map (((x : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2)) hinj
  have hterm : ∀ g ∈ C, (latIndex W g : ℝ) ^ (-(n : ℝ) / 2) = ((((Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((((H g : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K)).mulVecLin.restrictScalars O)).toAddSubgroup.relIndex
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).toAddSubgroup : ℕ) : ℝ) ^ (-(n : ℝ) / 2) := fun g hg => by
    conv_lhs => rw [← hH g hg]
    rw [GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert D W v ε hε w σ π β ι hCh hFr hGC (H g)]
  rw [Finset.sum_congr rfl hterm, ← hsum]

  have hcard : Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue, ← GlobalTheory.LFun.InertChart.absNorm_eq
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (IsLocalRing.ResidueField O) := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (by
      have := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
      exact this))
  have hunit : IsUnit (cO ⟨x0, hx0⟩ - ⟨x0, hx0⟩) := by
    have hne : σ x0 - x0 ≠ 0 := fun e => by rw [e, map_zero] at hx0v; exact zero_ne_one hx0v
    refine isUnit_iff_exists_inv.2 ⟨⟨(σ x0 - x0)⁻¹, ?_⟩, Subtype.ext ?_⟩
    · show Valued.v ((σ x0 - x0)⁻¹) ≤ 1
      rw [map_inv₀, hx0v, inv_one]
    · exact mul_inv_cancel₀ hne
  have hunitary : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      ((x : Matrix (Fin W.rank) (Fin W.rank) K).map cK)ᵀ * (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) *
        (x : Matrix (Fin W.rank) (Fin W.rank) K) = (1 : Matrix (Fin W.rank) (Fin W.rank) O).map (algebraMap O K) := by
    intro x hx
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (H g).2
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h1
  have hnontriv : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) ≠
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
    intro x hx he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 he
    have h2 := (hGC.2.2.2 (H g)).2 h1
    rw [hH g hg] at h2
    exact (hC g hg).2 h2
  have hdist' : ∀ x ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))), ∀ x' ∈ C.image (fun g => ((H g : GL (Fin W.rank) K))),
      (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map ((x' : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) →
      x = x' := by
    intro x hx x' hx' he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨g', hg', rfl⟩ := Finset.mem_image.1 hx'
    have hm : (Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank)))).map
        (((((H g)⁻¹ * H g' : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) K)) : GL (Fin W.rank) K) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
        Submodule.span O (Set.range (Pi.basisFun K (Fin W.rank))) := by
      have hcomp : ∀ (a b : GL (Fin W.rank) K), ((((a * b : GL (Fin W.rank) K)) : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) =
          ((a : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O).comp ((b : Matrix (Fin W.rank) (Fin W.rank) K).mulVecLin.restrictScalars O) := by
        intro a b
        ext y : 1
        simp [Matrix.mulVec_mulVec]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcomp, Submodule.map_comp, ← he, ← Submodule.map_comp, ← hcomp, inv_mul_cancel]
      ext y
      simp
    have h1 := (GlobalTheory.T.stdLattice_map_eq_iff_mem_GLint_valuationSubring K O W.rank _).1 hm
    have h2 := (hGC.2.2.2 _).2 h1
    rw [map_mul, map_inv, hH g hg, hH g' hg'] at h2
    rw [hdist g hg g' hg' h2]
  have key := GlobalTheory.HermNbr.selfDual_sum_le O K cO cK (fun x => Subtype.ext (hσσ x)) (fun x => rfl)
    ⟨⟨x0, hx0⟩, hunit⟩ W.rank n 1 (by simp) (by simp) hn
    (C.image fun g => ((H g : GL (Fin W.rank) K))) hunitary hnontriv hdist'
  refine key.trans (le_of_eq ?_)
  rw [hcard]
  have hv0 : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hv0]
  norm_num

end GlobalTheory.InertIdx

end
