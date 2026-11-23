import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaPowers

theorem finiteIndex_stabilizer (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (x : Ω) :
    (MulAction.stabilizer (G ℚ Ω) x).FiniteIndex := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hsub : MulAction.orbit (G ℚ Ω) x ⊆ (minpoly ℚ x).rootSet Ω := by
    rintro _ ⟨σ, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    have e := Polynomial.aeval_algHom_apply (σ : Ω →ₐ[ℚ] Ω) x (minpoly ℚ x)
    rw [minpoly.aeval, map_zero] at e
    exact e
  have hfin : (MulAction.orbit (G ℚ Ω) x).Finite := ((minpoly ℚ x).rootSet_finite Ω).subset hsub
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).mpr ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem cycMod_Ine_surjective (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) :
    Function.Surjective ((cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype) := by
  intro u
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Fact (1 < l ^ n) := ⟨Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt⟩
  have hs : Function.Surjective (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n)) :=
    ZMod.ringHom_surjective _
  haveI := IsLocalHom.of_surjective _ hs
  obtain ⟨v, hv⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hs this u
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA v
  refine ⟨⟨σ, hσ⟩, ?_⟩
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [cycMod, MonoidHom.comp_apply, hσv]
  exact hv

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
    ∀ F : Finset Ω, ∃ D : ℕ, 1 ≤ D ∧ ∀ (n : ℕ) (u : (ZMod (l ^ n))ˣ),
      ∃ s ∈ Ine (F := ℚ) A, (∀ x ∈ F, s x = x) ∧ cycMod ℚ Ω l n s = u ^ D := by
  intro l _ Ω _ _ _ A hA F
  let Fix : Subgroup (G ℚ Ω) := ⨅ x : F, MulAction.stabilizer (G ℚ Ω) (x : Ω)
  haveI : Fix.FiniteIndex :=
    Subgroup.finiteIndex_iInf fun x => finiteIndex_stabilizer Ω (x : Ω)
  let H : Subgroup (Ine (F := ℚ) A) := Fix.subgroupOf (Ine (F := ℚ) A)
  have hH0 : H.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.index, Nat.one_le_iff_ne_zero.mpr hH0, fun n u => ?_⟩
  set f := (cycMod ℚ Ω l n).comp (Ine (F := ℚ) A).subtype with hf
  have hsurj := cycMod_Ine_surjective l Ω A hA n
  have hdvd : (H.map f).index ∣ H.index := Subgroup.index_map_dvd H hsurj
  haveI : (H.map f).Normal := Subgroup.normal_of_comm _
  have hmem : u ^ H.index ∈ H.map f := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem _ u) _
  obtain ⟨h, hh, hfh⟩ := hmem
  refine ⟨h, h.2, fun x hx => ?_, hfh⟩
  have hfix : (h : G ℚ Ω) ∈ Fix := hh
  have := (Subgroup.mem_iInf.mp hfix) ⟨x, hx⟩
  exact this

end GlobalTheory.InertiaPowers
