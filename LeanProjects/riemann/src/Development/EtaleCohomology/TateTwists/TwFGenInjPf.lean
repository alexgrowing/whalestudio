import Development.EtaleCohomology.TateTwists.GenConnPf

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwFInj

theorem prim_field {q : ℕ} {k : Type} [Field k] (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int] using h

theorem pow_mod_eq {k : Type} [Field k] {q : ℕ} {z : k} (hz : IsPrimitiveRoot z q) (n : ℕ) :
    z ^ n = z ^ (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

theorem unit_unique {k : Type} [Field k] {q : ℕ} [NeZero q] {z : k} (hz : IsPrimitiveRoot z q)
    {u v : (ZMod q)ˣ} (h : z ^ (u : ZMod q).val = z ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective _ (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

theorem exists_unit {k : Type} [Field k] {q : ℕ} [NeZero q] {z x : k} (hz : IsPrimitiveRoot z q)
    (hx : IsPrimitiveRoot x q) : ∃ u : (ZMod q)ˣ, x = z ^ (u : ZMod q).val := by
  obtain ⟨j, hj, hjx⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : j.Coprime q := (hz.pow_iff_coprime (NeZero.pos q) j).1 (hjx ▸ hx)
  refine ⟨ZMod.unitOfCoprime j hc, ?_⟩
  rw [← hjx]
  congr 1
  simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hj]

end LateralTheory.EtaleFoundations.TwFInj

namespace LateralTheory.EtaleFoundations.TwFInj

variable {q : ℕ} [NeZero q] {B : Type} [CommRing B] {k : Type} [Field k] (π : B →+* k) {z : k}
  (hz : IsPrimitiveRoot z q)

noncomputable def ex (ξ : Prim q B) : (ZMod q)ˣ := Classical.choose (exists_unit hz (prim_field (ξ.map π)))

theorem ex_spec (ξ : Prim q B) : π ξ.1 = z ^ (ex π hz ξ : ZMod q).val :=
  Classical.choose_spec (exists_unit hz (prim_field (ξ.map π)))

theorem ex_rel {ζ ξ : Prim q B} {a : (ZMod q)ˣ} (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    ex π hz ξ = ex π hz ζ * a := by
  apply unit_unique hz
  rw [← ex_spec, h, map_pow, ex_spec π hz ζ, ← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_mod_eq hz]

noncomputable def L (i : ℤ) : (Prim q B →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (((ex π hz ξ) ^ i : (ZMod q)ˣ) : ZMod q))

theorem twRel_le_ker (i : ℤ) : twRel q i B ≤ LinearMap.ker (L π hz i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L, Finsupp.linearCombination_single, one_smul]
  apply ULift.ext
  simp [ex_rel π hz h, mul_zpow, mul_comm]

end LateralTheory.EtaleFoundations.TwFInj

theorem LateralTheory.EtaleFoundations.twF_gen_inj_of : LateralTheory.EtaleFoundations.twF_gen_inj := by
  intro q _ B _ hB i ζ c1 c2 hc
  simp only at hc
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  letI := Ideal.Quotient.field m
  let π := Ideal.Quotient.mk m
  have hz := LateralTheory.EtaleFoundations.TwFInj.prim_field (ζ.map π)
  let Φ := Submodule.liftQ _ (LateralTheory.EtaleFoundations.TwFInj.L π hz i) (LateralTheory.EtaleFoundations.TwFInj.twRel_le_ker π hz i)
  have h2 := congrArg Φ hc
  simp only [Φ, map_nsmul, Submodule.liftQ_apply, LateralTheory.EtaleFoundations.TwFInj.L, Finsupp.linearCombination_single, one_smul] at h2
  have h3 := congrArg ULift.down h2
  have h4 : (c1.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) =
      (c2.val : ZMod q) * ((LateralTheory.EtaleFoundations.TwFInj.ex π hz ζ ^ i : (ZMod q)ˣ) : ZMod q) := by
    simp only [nsmul_eq_mul] at h3
    exact h3
  simpa [ZMod.natCast_zmod_val] using (Units.mul_left_inj _).1 h4
