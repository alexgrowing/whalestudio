import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphIsometricForms
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphChangeOfModel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K₂ : Type} {ι₂ : K₂ → Type}

theorem exists_form_not_mem {P : Ideal (MRing ι)} {d : ℕ} {g : (Σ k, ι₂ k) → MRing ι} (hP : IsArithVar P d)
    (hBP : IsBasePtFree P g) : ∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P := by
  intro k₂
  by_contra hall
  push Not at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k₂ i
  have hle : Ideal.span (Set.range fun j : ι₂ k₂ => g ⟨k₂, j⟩) ≤ P :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle] at hN
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp (hprime.mem_of_pow_mem N hN)
  exact hi k hk

end GraphChangeOfModel

open GraphChangeOfModel IndefiniteRowSideFullHecke.Inter in

theorem GraphChangeOfModel.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hIso : IsomInvariance.Statement) (hGI : GraphIsometricForms.Statement) : GraphChangeOfModel.Statement := by
  intro I hI K _ ι _ K₂ _ ι₂ _ P d g δ G J L L₁ hP hg hBP hImg hJ hL hL₁ ha hh
  obtain ⟨hΓ, himg, hdeg⟩ := hGr K ι K₂ ι₂ P d g δ hP hg (exists_form_not_mem hP hBP)
  obtain ⟨G'⟩ := hGF K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d isBlockMap_inl hΓ
  obtain ⟨J', hJ', -⟩ := hEU G'.Φ _ (fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂))
  have e1 := hAI3 I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV _ d G' J' L₁
    (fun j => pullHerm isBlockMap_inl (L₁ j)) isBlockMap_inl hΓ (by rw [himg]; exact hP) hJ' hL₁
    (fun j => isPullHerm_pullHerm _ _)
  have e2 := hAI3 I hI K₂ ι₂ (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inr inrV _ d G J L
    (fun j => pullHerm isBlockMap_inr (L j)) isBlockMap_inr hΓ hImg hJ hL
    (fun j => isPullHerm_pullHerm _ _)
  have e3 := hIso (K ⊕ K₂) (Sum.elim ι ι₂) (I (K ⊕ K₂) (Sum.elim ι ι₂)) (hI _ _) _ d
    (fun j => pullHerm isBlockMap_inl (L₁ j)) (fun j => pullHerm isBlockMap_inr (L j)) hΓ
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inl (isPullHerm_pullHerm _ _) (hL₁ j))
    (fun j => Inter.IsPullHerm.isSmoothHerm isBlockMap_inr (isPullHerm_pullHerm _ _) (hL j))
    (fun j => hGI K ι K₂ ι₂ P d g δ (L₁ j) (L j) _ _ hP hg hBP (ha j) (hh j) (isPullHerm_pullHerm _ _)
      (isPullHerm_pullHerm _ _))
  rw [hdeg G' J' hJ', himg] at e1
  rw [← e2, ← e3, e1]
  simp

end GroundTheory.Heights₂.Heights.HilbertSamuel
