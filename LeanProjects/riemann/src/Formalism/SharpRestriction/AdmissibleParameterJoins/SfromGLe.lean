import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLb
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowest_K_type_integral_formula (D : D7) (h : PlaceDegreeData.DiscreteSeriesLowestKTypeFormula D) : StandardLattice.SmallPrimeLengthBound D := h

theorem mass_ratio_alt (D : D7) (h : StandardLattice.MassRatio₂ D) : LocalBesselAndTopKernel.FamilySchurFormalDegree D := massRatio_host_of D h

theorem family_mass_ratio {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ∀ x (i : Fm.Ix x), StandardLattice.MassRatio₂ (Fm.D x i)) :
    LocalBesselAndTopKernel.SecondSizeStatement Fm :=
  fun x i => mass_ratio_alt (Fm.D x i) (h x i)

def IdxColTie (D : D7) : Prop := StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) = S.gaG D

def IdxRowTie (D : D7) : Prop := StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) = LocalBesselAndTopKernel.idxRows D

def ColHyp (D : D7) : Prop :=
  StandardLattice.GBig D ∧ (∀ i, StandardLattice.SplitsF D (D.host.g i)) ∧ ∀ u : D.what₂.Word, StandardLattice.SplitsF D (D.mem u).A.T ∧ StandardLattice.Mu0Tie D u

theorem signature_at_zero_sum (R : Ranks) : (sigYD R 0).1 + (sigYD R 0).2 = R.r := by
  simp only [sigYD, Ranks.rankY, Ranks.r, zero_mul, add_zero]
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  omega

theorem two_le_signature_at_zero (R : Ranks) : 2 ≤ (sigYD R 0).1 := by
  simp only [sigYD, Ranks.rankY, Ranks.r, zero_mul, add_zero]
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  omega

theorem column_row_ranks (D : D7) (Lv : LevelData D) (h4 : StandardLattice.Conclusion4f D Lv) (h2 : StandardLattice.VolumeEqMass₂ D)
    (hD : StandardLattice.FactDstar D) (hc : ColHyp D) (t1 : IdxColTie D) (t2 : IdxRowTie D) : LocalBesselAndTopKernel.FamilyMidVolume D := by
  intro V _ _ _ _ h L _
  refine ⟨fun hL u => ?_, fun hL => ?_⟩
  · have e := h4 hc.1 hc.2.1 u (hc.2.2 u).1 (hc.2.2 u).2
    have em : mass h L = StandardLattice.massI D D.R.k := mass_ortho_eq hL (std_ortho D.host.E D.R.k)
    rw [em, ← t1]
    exact e
  · have em : mass h L = StandardLattice.massI D D.R.r := mass_ortho_eq hL (std_ortho D.host.E D.R.r)
    have ev : D.vol (D.sp.Y 0) = StandardLattice.massI D ((sigYD D.R 0).1 + (sigYD D.R 0).2) :=
      h2.2 (D.sp.Y 0) _ _ (D.sp.Y_sig 0) (fun τ => D.Y_sigval 0 (Nat.zero_le _) τ) (two_le_signature_at_zero D.R)
    rw [signature_at_zero_sum] at ev
    rw [em, ← t2, hD, ← ev]
    rfl

theorem family_column_row_ranks {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 Cg cb Cu cT CT : ℝ)
    (h : S.OwnEv Fm fun C' Cl x i => LocalBesselAndTopKernel.hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT →
      (∃ Lv : LevelData (Fm.D x i), StandardLattice.Conclusion4f (Fm.D x i) Lv) ∧ StandardLattice.VolumeEqMass₂ (Fm.D x i) ∧ StandardLattice.FactDstar (Fm.D x i) ∧
        ColHyp (Fm.D x i) ∧ IdxColTie (Fm.D x i) ∧ IdxRowTie (Fm.D x i)) :
    LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i hh => ?_⟩
  obtain ⟨⟨Lv, h4⟩, h2, hD, hc, t1, t2⟩ := hx0 x hx i hh
  exact column_row_ranks _ Lv h4 h2 hD hc t1 t2

end Formalism.MainNotions.J

end
