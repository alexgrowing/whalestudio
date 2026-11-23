import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOneLMemZalg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.TorusDeriv

noncomputable def blockL (E : Type) [Field E] (r s : ℕ) : Lie E (r + s) :=
  ∑ i : Fin r, toL (Matrix.single (Fin.castAdd s i) (Fin.castAdd s i) (1 : Cinf E))

theorem blockL_apply (E : Type) [Field E] (r s : ℕ) (i j : Fin (r + s)) (w : InfinitePlace E) :
    blockL E r s i j w = if i = j then (if (i : ℕ) < r then (1 : ℂ) else 0) else 0 := by
  have e : blockL E r s i j w =
      ∑ k : Fin r, ((Matrix.single (Fin.castAdd s k) (Fin.castAdd s k) (1 : Cinf E)) i j) w := by
    simp only [blockL, Finset.sum_apply]
    rfl
  rw [e]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have : Fin.castAdd s (⟨i, hi⟩ : Fin r) = i := Fin.ext rfl
        simp [this]
      · intro b _ hb
        have : Fin.castAdd s b ≠ i := fun h => hb (Fin.ext (show (b : ℕ) = i from congrArg Fin.val h))
        simp [Matrix.single_apply, this]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : Fin.castAdd s k ≠ i := fun h => hi (by rw [← h]; exact k.2)
      simp [Matrix.single_apply, this]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (Fin.castAdd s k = i ∧ Fin.castAdd s k = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this]

theorem hasDerivAt_entries {ι : Type} [Fintype ι] {a : ℕ} (f : ℝ → Fin a → Fin a → ι → ℂ) (X : Fin a → Fin a → ι → ℂ)
    (h : ∀ i j w, HasDerivAt (fun t => f t i j w) (X i j w) 0) : HasDerivAt f X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => h i j w

theorem hasDerivAt_aInf (E : Type) [Field E] [NumberField E] (r s : ℕ) :
    HasDerivAt (fun t : ℝ => toL (aInf E (r + s) r t).val) (blockL E r s) 0 := by
  refine hasDerivAt_entries _ _ fun i j w => ?_
  rw [blockL_apply]
  have e : (fun t : ℝ => (toL (aInf E (r + s) r t).val) i j w) = fun t : ℝ =>
      if i = j then Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0) else 0 := by
    funext t
    by_cases hij : i = j
    · subst hij
      simp [aInf]
    · simp [aInf, hij]
  rw [e]
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).cexp
    · simp only [if_neg hi]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  · simp only [if_neg hij]
    exact hasDerivAt_const _ _

theorem lie_blockL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) :
    lie E (r + s) (blockL E r s) =
      ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.CapelliTrace.sum_Eop _ _, blockL, map_sum]
  rfl

theorem hasDerivAt_aT_right : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  intro E _ _ _ r s F g t
  have h0 : aInf E (r + s) r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  have h1 := hasDerivAt_curve F (g * aT E (r + s) r t) (aInf E (r + s) r) (blockL E r s) h0
    (hasDerivAt_aInf E r s)
  have h2 : HasDerivAt (fun u : ℝ => F.1 ((g * aT E (r + s) r t) * infGL E (r + s) (aInf E (r + s) r (u - t))))
      (lieD (blockL E r s) F.1 (g * aT E (r + s) r t)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  rw [← lie_blockL]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have e : aT E (r + s) r u = aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r (u - t)) := by
    rw [← aT, ← PExpFin.aT_add]
    congr 1
    ring
  simp only []
  rw [e, mul_assoc]

end GlobalTheory.CompanionTheory.Conc.TorusDeriv
