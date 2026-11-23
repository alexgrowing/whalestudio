import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTrianglePeriodAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumIntegralNeg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedRealAverageKernelIsAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.JetsDivPeriodIsAlgebraic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFourierCoeffHeisenbergExpansion
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedTranslateEqAlgebraicCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTrianglePeriodAlgebraicStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
namespace GlobalTheory.BotAlgI
theorem classSum_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ dg : D.what₂.Tau →₀ ℕ, ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      Finsupp.mapDomain Prod.fst k = dg → IsAlgebraic ℚ (X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h x / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX dg
  obtain ⟨Ω, hΩ, hjet⟩ := _root_.GlobalTheory.T.bottom_translate_jets_algebraic hP hI hL hX dg
  refine ⟨Ω, hΩ, fun t x hx h hh k hk => ?_⟩
  obtain ⟨n, c, w, hc, hw, hf⟩ := _root_.GlobalTheory.T.bottom_fourier_coeff_heisenberg_expansion hP hI hL hX t
  choose n' c' w' hc' hw' hm using fun p => _root_.GlobalTheory.T.twisted_moved_translate_algebraic hP hI hL hX t x hx h hh (w p) (hw p)
  have hψ := hX.is.isVac.1
  have hθ : IsInfFam W.θ := hX.is.isVac.2.inf
  have hv : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW X.vac := hX.is.isVac.2.theta
  set φ : PolF D WW.rank A.rank := MvPolynomial.monomial k 1 with hφ
  set pt : (WO (GlobalTheory.Grid.neg A) WW → ℂ) → (WO (GlobalTheory.Grid.neg A) WW → ℂ) := fun f =>
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B f φ with hpt
  have comb : ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, (y p).map (infPart D) = 0) →
      pt (∑ p, a p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) =
        ∑ p, a p • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) := fun n a y hy => by
    have h1 := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
      X.rA.B X.rW.B X.vac hv n a y hy φ).1
    have h2 : ∀ p, heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) (pt X.vac) = pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (y p) X.vac) :=
      fun p => by
        have := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hψ hθ (fun τ => -X.rA.s τ) X.rW.s
          X.rA.B X.rW.B X.vac hv 1 (fun _ => 1) (fun _ => y p) (fun _ => hy p) φ).1
        simpa using this
    simp only [← h2]
    exact h1.symm
  have e1 : ∀ g, ((X.ω t).toSgn true) ((GlobalTheory.Grid.ofSgn true A).symm x, h) g = X.ω t (x, h) g := fun g => rfl
  have move : ∀ g, IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW g → X.ω t (x, h) (pt g) = pt (X.ω t (x, h) g) := fun g hg => by
    rw [← e1, ← e1]
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ (hX.is.weil t) W.θ hθ ((GlobalTheory.Grid.ofSgn true A).symm x) hx h hh
      (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B g φ hg
  have hval : X.ker W.ψ W.θ t φ h x / Ω =
      ∑ p, c p * ∑ q, c' p q * (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) 0 / Ω) := by
    have e2 : X.ker W.ψ W.θ t φ h x = X.ω t (x, h) (pt (X.f t)) 0 := rfl
    have e3 : ∀ p, X.ω t (x, h) (pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac)) =
        ∑ q, c' p q • pt (heisO W.ψ (GlobalTheory.Grid.neg A) WW (w' p q) X.vac) := fun p => by
      rw [move _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv _), hm p, comb _ _ _ (hw' p)]
    rw [e2, hf, comb _ _ _ hw, map_sum]
    simp only [map_smul, e3, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_div, Finset.mul_sum, mul_div_assoc]
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun p _ => mul_mem (mem_algebraicClosure_iff.2 (hc p)) (sum_mem fun q _ => mul_mem
    (mem_algebraicClosure_iff.2 (hc' p q)) (mem_algebraicClosure_iff.2 (hjet _ (hw' p q) k hk)))
theorem classSums_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hI hL hX
  obtain ⟨v, N, z, w, κ, hv, hz, hw, hκ1, hκ2, hcls⟩ := _root_.GlobalTheory.T.bottom_class_sum_integral_neg hP hI hL hX
  obtain ⟨dg, hproj⟩ := _root_.GlobalTheory.T.twisted_real_average_kernel_isAlgebraic hP hI hL hX
  obtain ⟨Ω, hΩ, hdict⟩ := _root_.GlobalTheory.BotAlgI.classSum_kernel_isAlgebraic hP hI hL hX dg
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  refine ⟨(v : ℂ) * Ω, mul_ne_zero hv' hΩ, fun t h hh k => ?_⟩
  choose m r U hr hU heq using fun l => hproj κ hκ1 hκ2 t (z l) (hz l) h hh k
  have hval : X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / ((v : ℂ) * Ω) =
      ∑ l, ((w l : ℂ))⁻¹ * ∑ p, r l p * (X.ker W.ψ W.θ t (MvPolynomial.monomial (U l p) 1) h (z l) / Ω) := by
    rw [hcls t _ h hh]
    simp only [heq, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    field_simp
  rw [hval, ← mem_algebraicClosure_iff]
  refine sum_mem fun l _ => mul_mem (inv_mem ?_) (sum_mem fun p _ => mul_mem ?_ ?_)
  · rw [mem_algebraicClosure_iff]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((w l : ℚ)))
  · rw [mem_algebraicClosure_iff]; exact hr l p
  · rw [mem_algebraicClosure_iff]; exact hdict t (z l) (hz l) h hh (U l p) (hU l p)
end GlobalTheory.BotAlgI
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_classSums_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ Ω : ℂ, Ω ≠ 0 ∧ ∀ t, ∀ h ∈ GfC WW, ∀ k, IsAlgebraic ℚ (X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h / Ω) := by
  first | exact @_root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | exact _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic | (intros; apply _root_.GlobalTheory.BotAlgI.classSums_isAlgebraic <;> assumption)
end
