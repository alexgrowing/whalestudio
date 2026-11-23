import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem comp_nsmul {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {e : N'.X → Fin r → N.X}
    (he : ∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) (k : ℕ) (z : N'.X) (i : Fin r) : e (k • z) i = k • e z i := by
  induction k with
  | zero =>
    have h := he 0 0 i
    rw [add_zero] at h
    simpa using h
  | succ k ih => rw [succ_nsmul, he, ih, succ_nsmul]

theorem qEq_iff_of_rel {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hT : TensFacts W φ e wv)
    (hW : IsUnit (W + W.transpose).det) {k : ℕ} {a' b' : N'.QT k} {as bs : Fin r → N.QT k}
    (ha : QRelV W φ e wv a' as) (hb : QRelV W φ e wv b' bs) : N'.QEq a' b' ↔ ∀ i, N.QEq (as i) (bs i) := by
  have hadd := hT.2.2.1
  have he := hT.2.2.2.1
  constructor
  · rintro ⟨z, hy, hg⟩ i
    refine ⟨e z i, ?_, ?_⟩
    · rw [← hb.1 i, hy, hadd, comp_nsmul hadd, ha.1 i]
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z)
      rw [← hg] at h1
      have h2 := congrFun (GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W φ e wv hT hW _ _ _ hb.2 h1) i
      simpa using h2
  · intro h
    choose z hz using h
    obtain ⟨z', hz'⟩ := he.2 z
    refine ⟨z', ?_, ?_⟩
    · apply he.1
      funext i
      rw [hadd, comp_nsmul hadd, hz', ha.1 i, hb.1 i]
      exact (hz i).1
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z')
      have h2 : ((fun j => (as j).1.2) * fun j => N.io (e z' j)) = fun j => (bs j).1.2 :=
        funext fun j => by rw [Pi.mul_apply, hz']; exact ((hz j).2).symm
      rw [h2] at h1
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hT _ _ _ hb.2 h1

theorem qkPt_equiv_iff_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N)
    (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k)
    (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs →
    (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p' q' ps qs hp hq
  obtain ⟨a', as, ha', has, ha⟩ := hp
  obtain ⟨b', bs, hb', hbs, hb⟩ := hq
  have hT := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  have G := GlobalTheory.Ex.GtValues.points_correspond
  rw [((G R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).2.2 p' q' a' b' ha' hb', qEq_iff_of_rel hT hW ha hb]
  exact forall_congr' fun i =>
    (((G R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.2 _ _ _ _ (has i) (hbs i)).symm

end GlobalTheory.Mum.TensTor
