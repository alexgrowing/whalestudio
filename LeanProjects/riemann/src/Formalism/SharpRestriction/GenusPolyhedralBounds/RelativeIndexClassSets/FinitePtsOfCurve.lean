import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem Kp_charZero (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : CharZero (Kp X la N) := by
  have := Kl_charZero X la
  exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

theorem unif_irreducible (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) : Irreducible (unif X la) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))

theorem unifO_irreducible (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Irreducible (unifO X la N) :=
  Op.irreducible_map X la N (unif_irreducible X la)

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem isUnif_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) : IsUnif (OsK X la G.w) (unifO X la G.N) := by
  have := hC.1
  have : Algebra.IsIntegral (Kp X la G.N) (OsK X la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp X la G.N) (unifO_irreducible X la G.N)

theorem finite_As_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) :
    Module.Finite (Op X la G.N) ↥(As (Op X la G.N) (OsK X la G.w)) := by
  have := hC.1
  have := hC.2.1
  have := Kp_charZero X la G.N
  exact (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).1

theorem isDVRAt_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) (ζ : PtsG G la) : IsDVRAt ζ := by
  have := hC.1
  have := hC.2.1
  have := Kp_charZero X la G.N
  exact (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2 ζ

theorem finite_pts_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) :
    Finite (PtsG G la) ∧
      (∑ᶠ ζ : PtsG G la, ep (unifO X la G.N) ζ * fdeg ζ) = Module.finrank (Kp X la G.N) (OsK X la G.w) := by
  have := hC.1
  have := hC.2.1
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  exact _root_.ramificationDegreeSum (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N) (unifO_irreducible X la G.N)
    (finite_As_of_curve Q hC)

theorem one_le_ep_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) (ζ : PtsG G la) : 1 ≤ ep (unifO X la G.N) ζ := by
  have := isDVRAt_of_curve Q hC ζ
  exact ep_pos ζ (isUnif_of_curve Q hC)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
