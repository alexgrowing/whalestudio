import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PairingNormalisingConstantLogLeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFormIntegralOnDualFr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDualityStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreservedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtNormMulWeylPairingIntegralSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefiniteStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem testLatticeCondition_dualFr_sumLat_delK : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (R : ℝ), 1 ≤ R → SpreadLe lam R → ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Nonempty C] (M : C → ι → Submodule (𝓞 K) (Fin n → K)), (∀ c τ, IsSelfDualK (G τ) (M c τ)) → ∀ (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ), IsMetric ((sumGram lam e G)⁻¹)ᵀ X → TestLatticeCondition N X (dualFr (sumLat lam e fun c => delK lam (M c))) (bound (Fintype.card ι) n R) := by
  intro K _ _ _ _ v₀ hv ι _ n lam R hR hsp G hG C _ M hM N e X hX
  have hGh : ∀ τ, (G τ)ᴴ = G τ := fun τ => (hG τ).1
  have hdel : ∀ c, Submodule.IsLattice K (delK lam (M c)) := fun c =>
    (GlobalTheory.T.nablaDeltaOperator_lattice_preserved K ι n lam (M c) fun τ => (hM c τ).1).2
  obtain ⟨hlat, hN, hdual⟩ := GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual K ι n lam C N e (fun c => delK lam (M c)) hdel
  haveI : Finite C := by
    let i₀ : VVIdx lam := (e ⟨0, hN⟩).2
    refine Finite.of_injective (fun c : C => e.symm (c, i₀)) ?_
    intro a b hab
    exact (Prod.ext_iff.1 (e.symm.injective hab)).1
  letI : Fintype C := Fintype.ofFinite C
  obtain ⟨hval, hH, hHi, hGu⟩ := GlobalTheory.T.sumPairingGramMatrix_values_and_definite K ι n lam G hG C N e
  have hHu : IsUnit (sumGram lam e G).det := by
    have h1 := (hH.2.2 v₀.embedding).isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at h1
    have h2 : ((sumGram lam e G).map v₀.embedding).det = v₀.embedding (sumGram lam e G).det :=
      (RingHom.map_det v₀.embedding (sumGram lam e G)).symm
    rw [h2] at h1
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  have hnab : hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c))
      = sumLat lam e fun c => nabK lam (M c) := by
    rw [hdual G hGh]
    congr 1
    funext c
    rw [(GlobalTheory.T.transported_weylLattice_hermitianDuality K ι n lam G (M c) hGh hGu fun τ => (hM c τ).1).2]
    congr 1
    funext τ
    exact (hM c τ).2
  obtain ⟨s, hs, hse, hsb⟩ := GlobalTheory.T.pairing_normalising_constant_log_le_bound K ι n lam R hR hsp
  have hint : ∀ x ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
      ∀ y ∈ hdualFr (sumGram lam e G) (sumLat lam e fun c => delK lam (M c)),
        (s : K) * (star x ⬝ᵥ sumGram lam e G *ᵥ y) ∈ (algebraMap (𝓞 K) K).range := by
    intro x hx y hy
    rw [hnab] at hx hy
    rw [hval, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [← hse]
    exact GlobalTheory.T.extNorm_mul_weylPairing_integral_selfDual K ι n lam G (M c) hGh hGu (hM c) _
      ((Submodule.mem_iInf _).1 hx c) _ ((Submodule.mem_iInf _).1 hy c)
  have hint' := dualForm_integral_on_dualFr K N (sumGram lam e G) hH.1 hHu _ s hint
  have hD := (GlobalTheory.T.dualLattice_isLattice_and_hermitianDual.1 K N (sumGram lam e G) _ hHu hlat).1
  have hne : dualFr (sumLat lam e fun c => delK lam (M c)) ≠ ⊥ := by
    intro h0
    have htop := hD.span_eq_top
    rw [h0] at htop
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simp at htop
  refine ⟨hD.fg, hne, fun v => (hX v).1, le_trans ?_ hsb⟩
  exact GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form K v₀ hv N _ X ⟨hHi.2.1, hX⟩ s hs _ hD.fg hne hint'

end GlobalTheory.TestLat
