import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.ExistsUnion
import Formalism.SharpRestriction.LevelLetterCocycles.JumpAndLengthOfAdmitted
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N

variable {D : D7}

def JumpsNoZero (i : D.nd.Loc) (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) ∧
    ∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1,
      (∃ U : Finset ℤ, U.card ≤ D.R.r ∧ (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) ∧
        ∀ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a → a ∈ U) ∧
      ¬ IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ 0

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem kill_of (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (M : GE D.nd →* Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) (h : ℕ) (hM : JumpsNoZero i M h)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C M) g v)
    (L2 : Lattice (O := ↥(OL C.LL)) (matRep (TruncatedSeriesCountingIdentities.locC C M))) :
    ∀ x : (Fin D.R.r → ↥C.LL.1) ⧸ L2.T, (∀ g, actD L2 g x = x) →
      ((D.nd.l i : ↥(OL C.LL)) ^ c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) • x = 0 := by
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≤ 4 * D.R.n := by
    rw [GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)]
    exact GlobalTheory.bridge_finrank_le D i w hw
  haveI : Finite (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) := by
    haveI := (D.nbr i w hw).Kw.2
    infer_instance
  obtain ⟨U, h1, h2, h3⟩ := exists_union (4 * D.R.n) D.R.r h hcard
    (fun τ a => IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a) (fun τ => ((hM w hw C).2 τ).1)
  have hn : U.card ≤ 4 * D.R.n * D.R.nV := h1.trans (Nat.mul_le_mul_left _ (Nat.le_add_right _ _))
  exact hK N h _ (D.nbr i w hw).Kw C.LL (hC w hw C)
    { V := Fin D.R.r → ↥C.LL.1, ρ := matRep (TruncatedSeriesCountingIdentities.locC C M), cont := hc, L := L2 } U hn h2 (hM w hw C).1
    (fun τ a ha => h3 τ a ha) (fun τ => ((hM w hw C).2 τ).2)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem invariants_length_admissible_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (h : ℕ)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))
    (hM : JumpsNoZero i (T2O D.nd i ρ π) h) :
    EmbeddingTypes.H0ColumnLengthBound i ρ π dc (fun _ => c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV)) := by
  intro _ u _ w hw _ C _ L2 hstd
  have hT2c : Continuous fun g => T2O D.nd i ρ π g := GlobalTheory.HTW.RecS.Model.continuous_twistedDual_rhoO i ρ π hρ
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hT2c).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM w hw C hc L2
  unfold EmbeddingTypes.lenInvD
  haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
  haveI : IsFractionRing ↥(OL C.LL) ↥C.LL.1 := Formalism.BasicNotions.Examples₂.LB.OL_frac C.LL
  refine EmbeddingTypes.len_le_of_kill (Br.PD D.loc D.nbr i w hw) L2.T hstd _ _ ?_
  intro x hx
  rw [Br.PD_p]
  exact hkill x fun g => hx g

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem length_invariants_Wprime_divisible_le_of_nonzero_jumps (i : D.nd.Loc) (N : ℕ) (hK : InvariantsKilledOverCyclotomic (D.loc (D.nd.l i))) (hC : CycAt N i)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (h : ℕ)
    (hW : Continuous fun g => WpO D.nd i ρ π g) (hM : JumpsNoZero i (WpO D.nd i ρ π) h)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i)) :
    (Br.h0W i u ρ π : ℝ) ≤ (D.R.r : ℝ) * (c0L (D.nd.l i) N h (4 * D.R.n * D.R.nV) : ℕ) := by
  let C := TruncatedSeriesCountingIdentities.CoefExt.self i u hu
  have e : TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) := by
    ext g a b
    rfl
  have hc : ∀ v, Continuous fun g => matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π)) g v :=
    fun v => (GlobalTheory.CrysChiOne.locC_cont' C _ hW).matrix_mulVec continuous_const
  have hkill := kill_of i N hK hC _ h hM u hu C hc
  rw [e] at hkill
  have hK' := GlobalTheory.LengthH0Bound.inv_killed (D.nbr i u hu) (WpO D.nd i ρ π) (decS D.nd u) (D.nd.l i) _
    (hkill (Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))))
  have hq := GlobalTheory.LengthH0Bound.lenUnit_le_of_kill D.R.r (D.nd.l i) _ (GlobalTheory.LengthH0Bound.natCast_ne_zero (D.nbr i u hu)) _ hK'
  exact_mod_cast hq

end UpperTheory.N

end
