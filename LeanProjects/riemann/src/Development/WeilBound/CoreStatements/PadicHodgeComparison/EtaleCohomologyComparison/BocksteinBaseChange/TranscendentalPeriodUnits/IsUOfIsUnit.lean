import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BcrisRegularPeriodRing
import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.Imports

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Formalism.Per6 GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem σ_per (g : K.fixingSubgroup) (x : BdR l) : (per l K).σ g x = σD g.1 x := rfl

theorem isU_of_isUnit {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {a : A} (ha : IsUnit a) :
    f a ∈ f.range ∧ ∃ y ∈ f.range, f a * y = 1 :=
  ⟨⟨a, rfl⟩, f ha.unit⁻¹.1, ⟨_, rfl⟩, by rw [← map_mul, ha.mul_val_inv, map_one]⟩

theorem isUnit_of_isU {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) {a : A}
    (h : ∃ y ∈ f.range, f a * y = 1) : IsUnit a := by
  obtain ⟨_, ⟨c, rfl⟩, hc⟩ := h
  have h1 : a * c = 1 := hf (by rw [map_mul, hc, map_one])
  exact ⟨⟨a, c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

theorem loc_abs {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (x y : B) (hx : x ∈ f.range) (hy : y ∈ f.range) (h : x + y ∈ f.range ∧ ∃ z ∈ f.range, (x + y) * z = 1) :
    (x ∈ f.range ∧ ∃ z ∈ f.range, x * z = 1) ∨ (y ∈ f.range ∧ ∃ z ∈ f.range, y * z = 1) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_add] at h
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (isUnit_of_isU f hf h.2) with ha | hb
  · exact Or.inl (isU_of_isUnit f ha)
  · exact Or.inr (isU_of_isUnit f hb)

theorem σD_qQ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (z : ℚ_[l]) : σD g (qQ l z) = qQ l z := by
  have hb := period_ring_base.base l
  rw [← hb.ι_q, ← hb.ι_σ, hb.σ_q]

theorem σD_tQ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) : σD g (tQ l) = qQ l (period_ring_base.χ g) * tQ l := by
  have hb := period_ring_base.base l
  rw [← hb.ι_t, ← hb.ι_σ, hb.galois_t_transform, map_mul, hb.ι_q]

theorem qQ_mul_inv {z : ℚ_[l]} (hz : z ≠ 0) : qQ l z * qQ l z⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hz, map_one]

theorem facts : PeriodRingFacts := fun l _ K =>
  { i_σ := fun g a => by
      show algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (ACris.galCris (IntermediateField.fixingSubgroupEquiv K g) a)) =
        galBdRField (IntermediateField.fixingSubgroupEquiv K g) (algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l a))
      rw [galBdRField_algebraMap, ← ACris.gal_smul_def, ACris.iota_gal_smul]
    thetaSetup_structureMap_comp := fun z => by
      show algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (algebraMap (AInf ℂ_[l] l) (ACris.ACris ℂ_[l] l)
        (IsPerfectoidField.padicIntToWitt l z))) = algebraMap (BdRp l) (BdR l) (algebraMap ℚ_[l] (BdRp l) (z : ℚ_[l]))
      rw [ACris.iota_padicInt]
    frobenius_period := ACris.phi_periodT_eq_mul (untilt_epsilon (p := l))
    t_ne := DeRhamTwist.Twist.tQ_ne
    t_mem := ⟨ACris.iota ℂ_[l] l (tA l), rfl⟩
    q_mem := fun z => ⟨algebraMap ℚ_[l] (BdRp l) z, rfl⟩
    o_mem := fun k => ⟨_, rfl⟩
    σ_q := fun g z => σD_qQ g.1 z
    σ_mem := fun g x hx => (period_ring_base.base l).plus_σ g.1 x hx
    galois_t_transform := fun g => by
      have hχ : period_ring_base.χ g.1 ≠ 0 := by
        intro h0
        have h1 := σD_tQ (l := l) g.1
        rw [h0, map_zero, zero_mul, map_eq_zero_iff _ (σD g.1).injective] at h1
        exact DeRhamTwist.Twist.tQ_ne h1
      refine ⟨qQ l (period_ring_base.χ g.1), ⟨⟨_, rfl⟩, qQ l (period_ring_base.χ g.1)⁻¹, ⟨_, rfl⟩, ?_⟩, σD_tQ g.1⟩
      exact qQ_mul_inv hχ
    loc := fun x hx y hy h => loc_abs (algebraMap (BdRp l) (BdR l)) (IsFractionRing.injective _ _) x y hx hy h }

end CrystallineSemistableComparison
