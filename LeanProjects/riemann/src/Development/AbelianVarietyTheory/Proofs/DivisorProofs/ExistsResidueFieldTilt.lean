import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.TiltResidue

theorem preTilt_onto_algClosed_residue : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : CharP k p) (r : PreTilt O p →+* k), Function.Surjective r := by
  intro p _ C _ _ _ v O _ _ hpu _ hv
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hpu.out

  have hroot : ∀ y : O, ∃ z : O, z ^ p = y := by
    intro y
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C y) (Fact.out : p.Prime).pos
    have hw1 : v w ≤ 1 := by
      have h := hv.map_le_one y
      rw [← hw, map_pow] at h
      exact (pow_le_one_iff_of_nonneg zero_le (Fact.out : p.Prime).ne_zero).1 h
    obtain ⟨z, hz⟩ := hv.exists_of_le_one hw1
    exact ⟨z, hv.hom_inj (by rw [map_pow, hz, hw])⟩
  choose s hs using hroot
  have hcoeff : Function.Surjective (PreTilt.coeff (O := O) (p := p) 0) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨show Perfection (ModP O p) p from
      ⟨fun n => Ideal.Quotient.mk _ (s^[n] y), fun n => ?_⟩, rfl⟩
    rw [← map_pow, Function.iterate_succ_apply', hs]
  let q : ModP O p →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift _ (IsLocalRing.residue O) (fun a ha =>
      (IsLocalRing.residue_eq_zero_iff a).2
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hpm) ha))
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  have hchar : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have hac : IsAlgClosed (IsLocalRing.ResidueField O) := by
    refine IsAlgClosed.of_exists_root _ fun g hg hirr => ?_
    have hl : g ∈ Polynomial.lifts (IsLocalRing.residue O) :=
      (Polynomial.mem_lifts _).mpr
        (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)
    obtain ⟨f, rfl, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hg
    have hd : (f.map (algebraMap O C)).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective hv.hom_inj]
      intro h0
      have := Polynomial.degree_pos_of_irreducible hirr
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, Nat.cast_eq_zero] at h0
      rw [Polynomial.degree_eq_natDegree (hf.map _).ne_zero] at this
      have h1 : (f.map (IsLocalRing.residue O)).natDegree = 0 := by
        rw [← hdeg]; exact h0
      rw [h1] at this; exact lt_irrefl _ this
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hd
    have hi : IsIntegral O a := ⟨f, hf, by rw [← Polynomial.eval_map]; exact ha⟩
    obtain ⟨b, rfl⟩ := hv.exists_of_le_one (r := a) (hv.mem_of_integral hi)
    have hb : f.eval b = 0 := hv.hom_inj (by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]; exact ha)
    refine ⟨IsLocalRing.residue O b, ?_⟩
    rw [Polynomial.eval_map, Polynomial.eval₂_hom, hb, map_zero]
  exact ⟨IsLocalRing.ResidueField O, inferInstance, hac, hchar, q.comp (PreTilt.coeff 0),
    hq.comp hcoeff⟩

end GlobalTheory.TiltResidue
