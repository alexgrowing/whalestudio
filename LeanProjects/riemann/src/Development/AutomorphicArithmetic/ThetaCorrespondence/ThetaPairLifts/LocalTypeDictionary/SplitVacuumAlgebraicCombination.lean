import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsAlgebraicSplitCharacterTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLocalSupportIdempotentStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.SplitVacAlg
open GlobalTheory.MovedAlg
section Comb
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}
end Comb
set_option maxHeartbeats 1000000 in
theorem split_vacuum_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hInp hLμ hX t N e P hP _ h hh hs
  classical
  have hψ : ∀ u v : WO (GlobalTheory.Grid.neg A) WW, u.map (infPart D) = 0 → v.map (infPart D) = 0 →
      IsAlgebraic ℚ (W.ψ (symplOH (GlobalTheory.Grid.neg A) WW u v)) :=
    fun u v hu hv => GlobalTheory.T.isAlgebraic_stdChar_halfSymplectic_realPart_zero hX.is.isVac.1 (GlobalTheory.Grid.neg A) WW u v hu hv
  have hchr := _root_.GlobalTheory.T.isAlgebraic_splitCharacter_twist hPr hInp hLμ hX
  have vac : IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac X.vac := isAlgComb_self
  have detAlg : ∀ (e' : AE D) (he' : IsSplitIdem D e') (g : GA D WW),
      IsAlgebraic ℚ (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (GlobalTheory.VecInv.detAt e' he'.1 WW g) : Circle) : ℂ) :=
    fun e' he' g => hchr e' he' _ (by
      change e' * (Formalism.L2.Theta.mt WW g).det + (1 - e') =
        e' * (e' * (Formalism.L2.Theta.mt WW g).det + (1 - e')) + (1 - e')
      rw [mul_add, ← mul_assoc, he'.1, mul_sub, mul_one, he'.1, sub_self, add_zero])
  have hecke : ∀ (e' : AE D) (he' : IsSplitIdem D e') (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D WW),
      Formalism.L2.NTheta.IsHeckeElt (stdLatSp WW hX.stdW.1) e' (ϖ : D.host.E) k α →
      IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, α) X.vac) := by
    intro e' he' ϖ k α hα
    obtain ⟨Δ, hΔ, heq⟩ := GlobalTheory.T.definiteBottom_splitHecke_vacuum hX t e' he' ϖ k α hα
    rw [heq]
    exact (isAlgComb_sum Δ hΔ).smul (isAlg_mul (detAlg e' he' α) (isAlg_sqrt_inv _))
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (by
      simpa using Ideal.pow_right_strictAnti P.asIdeal P.ne_bot P.isPrime.ne_top (by norm_num : 1 < 2))
  have gen := GlobalTheory.T.splitPlace_unitaryPoint_mem_heckeClosure (stdLatSp WW hX.stdW.1) P e ϖ hP hϖ hϖ2 h hh hs
  refine Submonoid.closure_induction
    (motive := fun x _ => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, x) X.vac)) ?_ ?_ ?_ gen
  · intro x hx
    rcases hx with (⟨hk, hks⟩ | ⟨k, hα⟩) | ⟨k, hα⟩
    · rw [GlobalTheory.T.definiteBottom_splitPlace_stabiliser_vacuum hX t e hP.1 x hk hks]
      exact vac.smul (detAlg e hP.1 x)
    · exact hecke e hP.1 ϖ k x hα
    · have hc := ((GlobalTheory.SplitPlace.split_local (stdLatSp WW hX.stdW.1) P e hP).2.2 ϖ hϖ hϖ2).2 k x⁻¹ hα |>.1
      have h2 := hecke (cA D e) (GlobalTheory.SplitScalar.isSplitIdem_conj hP.1)
        ⟨star (ϖ : D.host.E), ϖ.2.map (starRingEnd D.host.E).toIntAlgHom⟩ k _ hc
      exact (congrArg (fun y : GA D WW => IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, y) X.vac))
        (inv_inv x)).mp h2
  · show IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t 1 X.vac)
    rw [map_one]
    exact vac
  · intro x y _ _ hx hy
    have e1 : ((1 : GA D A), x * y) = (1, x) * (1, y) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    exact om_algComb hX hψ t 1 x hx hy
end GlobalTheory.SplitVacAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T) (N : ℕ) (e : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
    ∀ h ∈ GfC WW, Formalism.L2.Theta.SuppAt e WW h →
      GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac (X.ω t (1, h) X.vac) := by
  first | exact @_root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | exact _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination | (intros; apply _root_.GlobalTheory.SplitVacAlg.split_vacuum_algebraic_combination <;> assumption)
end
