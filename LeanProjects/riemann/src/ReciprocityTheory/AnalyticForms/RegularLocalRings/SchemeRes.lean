import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsSncDataW
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WeightedSieveThreeParameter
import ReciprocityTheory.AnalyticForms.RegularLocalRings.NormEvalLeOfVarsSubset
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WCharts
import ReciprocityTheory.AnalyticForms.RegularLocalRings.NeZeroOfSpanEqMaximalIdeal

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

open Classical in

def WData.idxEquiv (w : WData P D hP) : w.Idx ≃ Fin (Fintype.card w.Idx) :=
  Fintype.equivFin w.Idx

open Classical in

def WData.toAlgRes (w : WData P D hP) {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (hD : IsMultiHomogIdeal D) (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q) :
    AlgRes ι P D e where
  M := w.M
  top := w.topology
  compact := w.compactSpace
  t2 := w.t2Space
  n := Fintype.card w.Idx
  amb i := (w.pres (w.idxEquiv.symm i).1 (w.idxEquiv.symm i).2).n
  ideal i := (w.pres (w.idxEquiv.symm i).1 (w.idxEquiv.symm i).2).K
  src i := w.src (w.idxEquiv.symm i)
  isOpen_alt_bis i := w.isOpen_alt_bis _
  cover x := by
    obtain ⟨c, hc⟩ := w.cover x
    exact ⟨w.idxEquiv c, by simpa using hc⟩
  coord i := w.coord (w.idxEquiv.symm i)
  isEmbedding i := w.isEmbedding _
  image i := w.image _
  trans i j := w.trans _ _
  regular i := w.regular_coord _
  dim i x hx := w.dim_coord he _ x hx
  lift i := w.lift (w.idxEquiv.symm i)
  lift_one i := w.lift_one _
  lift_mem i := w.lift_mem _
  compat i j := w.compat _ _
  surj z hz hzD := by
    obtain ⟨c, x, hx, h⟩ := w.surj hD z hz hzD
    obtain ⟨i, rfl⟩ := w.idxEquiv.symm.surjective c
    exact ⟨i, x, hx, h⟩
  inj i j := w.inj hD _ _
  inv i := w.inv hD _
  bd i := w.bd (w.idxEquiv.symm i)
  le_bd i := w.le_bd _
  zero_bd i := w.zero_bd hD _
  rc := w.rc
  comp := w.comp
  sncAt i := w.sncAt he _
  comp_eq i := w.comp_eq he _
  mult f a hf hfP hzero := by
    obtain ⟨m, hm⟩ := w.mult he hD hcomp f a hf hfP hzero
    exact ⟨m, fun i x hx => hm _ x hx⟩

theorem algRes_of_logResStC (hQ : FinalTheorems.FinTypeQE)
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (hP : IsMultiHomogIdeal P) (hrad : P.IsRadical) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hsing : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ¬ IsRegularLocalRing (locAt (chartIdeal P p) z) → ∀ f ∈ D, eval z f = 0)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (locAt (chartIdeal P p) z) = e)
    (hL : FinalTheorems.LogResStC (projX P hP) (projB P D hP)) :
    Nonempty (AlgRes ι P D e) := by
  obtain ⟨w⟩ := exists_wData_of_logRes hQ hP hD hrad hsing hcomp hL
  exact ⟨w.toAlgRes (w.ringKrullDim_stalk e hD hcomp hdim) hD hcomp⟩

end

end ReciprocityTheory.AnForm.R
