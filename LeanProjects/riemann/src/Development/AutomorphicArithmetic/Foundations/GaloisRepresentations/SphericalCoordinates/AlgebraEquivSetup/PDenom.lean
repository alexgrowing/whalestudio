import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegralStatement
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.InvMemLatMonoidOfMemAwaySupp

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed.TensorDenominatorBound

open IsDedekindDomain.HeightOneSpectrum

variable {p : ℕ} [Fact p.Prime]

private def HasDen (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) : Prop :=
  ∃ c : ℕ, 0 < c ∧ c.Coprime p ∧ c • z ∈ LaHat D

private theorem HasDen.add {D : Datum p} {u w : AfP p ⊗[ℚ] VQ D} (hu : HasDen D u) (hw : HasDen D w) :
    HasDen D (u + w) := by
  obtain ⟨c, hc0, hcp, hc⟩ := hu
  obtain ⟨d, hd0, hdp, hd⟩ := hw
  refine ⟨c * d, Nat.mul_pos hc0 hd0, Nat.Coprime.mul hcp hdp, ?_⟩
  rw [smul_add]
  refine AddSubgroup.add_mem _ ?_ ?_
  · rw [mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ hc d
  · rw [mul_smul]
    exact AddSubgroup.nsmul_mem _ hd c

private theorem hasDen_zero (D : Datum p) : HasDen D 0 := by
  exact ⟨1, Nat.one_pos, Nat.coprime_one_left p, by simp [AddSubgroup.zero_mem]⟩

private theorem hasDen_gen (D : Datum p) (a : AfP p) (x : D.La) :
    HasDen D (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) := by
  obtain ⟨j, hj0, hjp, hj⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p a
  refine ⟨j, hj0, hjp, ?_⟩
  rw [TensorProduct.smul_tmul', nsmul_eq_mul]
  unfold LaHat
  exact AddSubgroup.subset_closure ⟨_, x, hj, rfl⟩

private theorem hasDen_tmul (D : Datum p) (a : AfP p) (t : VQ D) : HasDen D (a ⊗ₜ[ℚ] t) := by
  induction t using TensorProduct.induction_on with
  | zero => simpa using hasDen_zero D
  | tmul q x =>
    have e : (q ⊗ₜ[ℤ] x : VQ D) = q • ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    exact hasDen_gen D (q • a) x
  | add s t hs ht =>
    rw [TensorProduct.tmul_add]
    exact hs.add ht

private theorem hasDen (D : Datum p) (z : AfP p ⊗[ℚ] VQ D) : HasDen D z := by
  induction z using TensorProduct.induction_on with
  | zero => exact hasDen_zero D
  | tmul a t => exact hasDen_tmul D a t
  | add s t hs ht => exact hs.add ht

private noncomputable def inAfH (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D :=
  (TensorProduct.mk ℚ (AfP p) (VQ D) 1).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ D.La 1).toAddMonoidHom

end UpperTheory.Gal.W2.Seed.TensorDenominatorBound

open UpperTheory.Gal.W2.Seed.TensorDenominatorBound in
theorem UpperTheory.Gal.W2.Seed.pDenom :
    Denom := by
  intro p _ D G L h
  haveI := D.finLa
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := D.La)
  choose c hc0 hcp hcm using fun x : D.La => hasDen D (L.actG h (inAfH D x))
  refine ⟨∏ x ∈ s, c x, Finset.prod_pos fun x _ => hc0 x,
    Nat.Coprime.prod_left fun x _ => hcp x, ?_⟩
  have hgen : ∀ x : D.La, (∏ y ∈ s, c y) • L.actG h (inAfH D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (s : Set D.La) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rw [← Finset.mul_prod_erase s c hy, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ (hcm y) _
    | zero => simp [AddSubgroup.zero_mem]
    | add y z _ _ hy hz =>
      rw [map_add, map_add, smul_add]
      exact AddSubgroup.add_mem _ hy hz
    | smul n y _ hy =>
      rw [map_zsmul, map_zsmul, smul_comm]
      exact AddSubgroup.zsmul_mem _ hy n
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAfH D x := by
      simp [inAfH, TensorProduct.smul_tmul']
    rw [e, map_smul, smul_comm]
    exact GlobalTheory.W2.smul_mem_laHat ha (hgen x)
  | zero => simp [AddSubgroup.zero_mem]
  | add y z _ _ hy hz =>
    rw [map_add, smul_add]
    exact AddSubgroup.add_mem _ hy hz
  | neg y _ hy =>
    rw [map_neg, smul_neg]
    exact AddSubgroup.neg_mem _ hy
