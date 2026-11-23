import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.WeilDeligne GlobalTheory.Pst
open GlobalTheory.BKReal IsLocalRing Formalism.BasicNotions.Examples₂.LB

namespace GlobalTheory.AinfK

theorem fK_eq_resDeg {l : ℕ} [hl : Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w)
    (hj : Induces Bw) : fK Bw.Kw = resDeg l w := by
  have hN := normV_eq_pow (hj.mem_placesOver h)
  refine Nat.pow_right_injective hl.out.two_le (le_antisymm ?_ ?_)
  · obtain ⟨-, ω, hω, -⟩ := exists_gen l (fK Bw.Kw)
    have h1 := one_lt_pow_l l (fK Bw.Kw)
    have hm : ω ∈ K0 Bw.Kw := Kunr_fK Bw.Kw ▸ IntermediateField.subset_adjoin _ _ (show ω ^ l ^ fK Bw.Kw = ω by
      rw [← Nat.sub_add_cancel h1.le, pow_succ, hω.pow_eq_one, one_mul])
    have h2 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0) (actsAs_of_deg (by simp)) ⟨ω, hm.2⟩
    rw [mul_one, mul_zero, pow_zero, frobUr_pow_root _ _ (l ^ fK Bw.Kw - 1) (by omega)
      (fun hd => hl.out.not_dvd_one ((Nat.dvd_sub_iff_right h1.le (dvd_pow_self l (NeZero.ne _))).1 hd))
      (Subtype.ext hω.pow_eq_one)] at h2
    have h3 : ω = ω ^ l ^ resDeg l w :=
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (weilToGK Bw h (frob h)).2 _ hm.1).symm.trans h2
    have h4 := one_lt_normV w
    rw [hN] at h4
    have h5 : ω ^ (l ^ resDeg l w - 1) = 1 := mul_right_cancel₀ (hω.ne_zero (by omega)) (by
      rw [← pow_succ, Nat.sub_add_cancel h4.le, one_mul, ← h3])
    have := Nat.le_of_dvd (by omega) (hω.dvd_of_pow_eq_one _ h5)
    change l ^ _ ≤ l ^ _
    omega
  · change l ^ _ ≤ l ^ _
    rw [← hN, ← card_res]
    let u : 𝓞 E →+* ↥Bw.Kw.1 :=
      (Bw.j.comp ((algebraMap E Ω).comp (algebraMap (𝓞 E) E))).codRestrict Bw.Kw.1 fun x => Bw.j_E _
    let v : 𝓞 E →+* ↥(OL Bw.Kw) := u.codRestrict (OL Bw.Kw) fun x =>
      (map_isIntegral_int u (RingOfIntegers.isIntegral x)).tower_top
    have hk : ∀ x, ((residue _).comp v) x = 0 ↔ x ∈ w.asIdeal := fun x => by
      rw [RingHom.comp_apply, residue_eq_zero_iff, mem_max, ← h x, hj.valuation_lt_one_iff]
      rfl
    have := OL_resFinite Bw.Kw
    exact Nat.card_le_card_of_injective (Ideal.Quotient.lift w.asIdeal _ fun x hx => (hk x).2 hx)
      (RingHom.lift_injective_of_ker_le_ideal _ _ fun x hx => (hk x).1 hx)

end GlobalTheory.AinfK
