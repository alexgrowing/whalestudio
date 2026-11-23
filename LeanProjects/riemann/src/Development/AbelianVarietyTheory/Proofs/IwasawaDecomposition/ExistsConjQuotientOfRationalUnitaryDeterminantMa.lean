import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactorStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.RatPts

theorem exists_mul_apply_eq_of_mul_apply_eq_one_of_involution {L : Type} [Field L] (c : L →+* L) (hc : ∀ x, c (c x) = x) (hne : ∃ a, c a ≠ a)
    (z : L) (hz : z * c z = 1) : ∃ k : Lˣ, z * c (k : L) = k := by
  by_cases h : 1 + z = 0
  · obtain ⟨a, ha⟩ := hne
    refine ⟨Units.mk0 (a - c a) (sub_ne_zero.2 ha.symm), ?_⟩
    have hz1 : z = -1 := by linear_combination h
    rw [Units.val_mk0, map_sub, hc, hz1]
    ring
  · refine ⟨Units.mk0 (1 + z) h, ?_⟩
    rw [Units.val_mk0, map_add, map_one]
    linear_combination hz

theorem fixed_of_two {L : Type} [Field L] (c : L →+* L) (z : L) (k k' : Lˣ)
    (h : z * c (k : L) = k) (h' : z * c (k' : L) = k') :
    c ((k⁻¹ * k' : Lˣ) : L) = ((k⁻¹ * k' : Lˣ) : L) := by
  have h0 : c (k : L) ≠ 0 := (map_ne_zero c).2 k.ne_zero
  have h1 : (k : L) ≠ 0 := k.ne_zero
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  field_simp
  linear_combination c (k : L) * h' - c (k' : L) * h

open Classical in

theorem rat_points : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsRationalUnitaryDeterminantMap H (e1T H) ∧ (letI := H.cmStar; ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k) := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  letI := H.cmStar
  have h90 : ∀ z : unitary H.E, ∃ k : (H.E)ˣ, (z : H.E) * H.conj (k : H.E) = k := by
    intro z
    refine exists_mul_apply_eq_of_mul_apply_eq_one_of_involution (H.conj : H.E →+* H.E) (fun x => ?_) ?_ (z : H.E) ?_
    · show H.conj (H.conj x) = x
      rw [← hc, ← hc, IsCMField.complexConj_apply_apply]
    · by_contra hn
      push Not at hn
      exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext fun x => (hc x).trans (hn x))
    · show (z : H.E) * H.conj (z : H.E) = 1
      rw [← bridge_star_holds R H]
      exact z.2.2
  have hwd : ∀ (z : H.E) (k k' : (H.E)ˣ), z * H.conj (k : H.E) = k → z * H.conj (k' : H.E) = k' →
      (QuotientGroup.mk (diagUnits H.E k) : DtT H) = QuotientGroup.mk (diagUnits H.E k') := by
    intro z k k' h h'
    have hfix := fixed_of_two (H.conj : H.E →+* H.E) z k k' h h'
    have hF : ((k⁻¹ * k' : (H.E)ˣ) : H.E) ∈ H.F :=
      (IsCMField.complexConj_eq_self_iff H.E _).1 ((hc _).trans hfix)
    have hne : (⟨_, hF⟩ : H.F) ≠ 0 := fun e => (k⁻¹ * k').ne_zero (congrArg Subtype.val e)
    have e : upF H.F (Units.mk0 _ hne) = k⁻¹ * k' := Units.ext rfl
    have := (GlobalTheory.T.unitaryDeterminantKernel_open_and_factor R H).2.2.1 (Units.mk0 _ hne)
    rw [e, map_mul, map_inv] at this
    exact QuotientGroup.eq.2 this
  refine ⟨isRationalUnitaryDeterminantMap_rationalUnitaryToDeterminants H ?_, h90⟩
  choose s hs using h90
  refine ⟨MonoidHom.mk' (fun z => QuotientGroup.mk (diagUnits H.E (s z))) fun z z' => ?_,
    fun k z h => hwd z k (s z) h (hs z)⟩
  rw [← QuotientGroup.mk_mul, ← map_mul]
  refine hwd ((z * z' : unitary H.E) : H.E) _ _ (hs _) ?_
  rw [Submonoid.coe_mul, Units.val_mul, map_mul, mul_mul_mul_comm, hs, hs]

end GlobalTheory.Mem.RatPts
