import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniquePointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_pow {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (h : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by
      have := h.2.2.1 0 0 j
      rw [add_zero] at this
      exact (add_eq_left.1 this.symm)
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem exists_ptRel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k ps
  have B := GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have B' := GlobalTheory.Ex.GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hT := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  choose qs hqs using fun i => ((B.2.2.2.2 k).1 (ps i)).exists
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT fun j => (qs j).1.2
  obtain ⟨y', hy'⟩ := hT.2.2.2.1.2 fun i => (qs i).1.1.toAdd
  have hk : v' ^ k = N'.io y' := by
    refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT _ _ (fun j => N.io (chi T ν ν' y' j))
      ?_ (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT y')
    have hp := gtRelV_pow hT hv' k
    have e : ((fun j => (qs j).1.2) ^ k : Fin r → N.Gt) = fun j => N.io (chi T ν ν' y' j) := by
      funext j
      rw [Pi.pow_apply, hy']
      exact (qs j).2
    rwa [e] at hp
  let q' : N'.QT k := ⟨(Multiplicative.ofAdd y', v'), hk⟩
  obtain ⟨p', hp'⟩ := (B'.2.2.2.2 k).2.1 q'
  exact ⟨p', q', qs, hp', hqs, fun i => congrFun hy' i, hv'⟩

end GlobalTheory.Mum.TensTor
