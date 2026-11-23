import Development.EtaleCohomology.EtaleSheaves.LeafTwSecKillCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec.FieldZ

variable {q : ℕ} [NeZero q] {K : Type} [CommRing K] [IsDomain K]

theorem prim_isPrim (ξ : Prim q K) : IsPrimitiveRoot ξ.1 q := by
  have : NeZero (q : K) := ⟨ξ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic q (Int.castRingHom K)]
  have h := ξ.2.2
  rw [Polynomial.aeval_def] at h
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  simpa [Polynomial.eval₂_eq_eval_map] using h

theorem pow_val (ζ : Prim q K) (n : ℕ) : ζ.1 ^ n = ζ.1 ^ ((n : ZMod q).val) := by
  rw [ZMod.val_natCast]
  conv_lhs => rw [← Nat.mod_add_div n q, pow_add, pow_mul, (prim_isPrim ζ).pow_eq_one, one_pow, mul_one]

theorem exists_unit (ζ ξ : Prim q K) : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val := by
  obtain ⟨i, hi, h⟩ := (prim_isPrim ζ).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one
  have hc : i.Coprime q := ((prim_isPrim ζ).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (h ▸ prim_isPrim ξ)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, h]

theorem unit_unique (ζ : Prim q K) {u v : (ZMod q)ˣ} (h : ζ.1 ^ (u : ZMod q).val = ζ.1 ^ (v : ZMod q).val) : u = v :=
  Units.ext (ZMod.val_injective q ((prim_isPrim ζ).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))

open Classical in

def ex (j : ℤ) (ζ : Prim q K) (ξ : Prim q K) : ZMod q :=
  if h : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val then (((h.choose) ^ j : (ZMod q)ˣ) : ZMod q) else 0

theorem ex_spec (j : ℤ) (ζ ξ : Prim q K) (u : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (u : ZMod q).val) :
    ex j ζ ξ = ((u ^ j : (ZMod q)ˣ) : ZMod q) := by
  have he : ∃ u : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (u : ZMod q).val := ⟨u, h⟩
  unfold ex
  rw [dif_pos he, unit_unique ζ (he.choose_spec.symm.trans h)]

def Φ (j : ℤ) (ζ : Prim q K) : (Prim q K →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination (ULift.{1} (ZMod q)) (fun ξ => ULift.up (ex j ζ ξ))

theorem rel_le (j : ℤ) (ζ : Prim q K) : twRel q j K ≤ LinearMap.ker (Φ j ζ) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ', ξ, a, h, rfl⟩
  obtain ⟨u, hu⟩ := exists_unit ζ ζ'
  have hξ : ξ.1 = ζ.1 ^ ((u * a : (ZMod q)ˣ) : ZMod q).val := by
    rw [h, hu, ← pow_mul, pow_val ζ, Units.val_mul, Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, Φ, map_sub, Finsupp.linearCombination_single]
  rw [ex_spec j ζ ξ _ hξ, ex_spec j ζ ζ' _ hu, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem key (j : ℤ) (ζ : Prim q K) (c : ZMod q)
    (h : (ULift.up.{1} c • Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) :
      (Prim q K →₀ ULift.{1} (ZMod q)) ⧸ twRel q j K) = 0) : c = 0 := by
  have h2 := congrArg ((twRel q j K).liftQ (Φ j ζ) (rel_le j ζ)) h
  rw [LinearMap.map_smul, Submodule.liftQ_apply, map_zero, Φ, Finsupp.linearCombination_single,
    ex_spec j ζ ζ 1 ((pow_one ζ.1).symm.trans (by rw [pow_val ζ 1, Nat.cast_one, Units.val_one]))] at h2
  have h3 := congrArg ULift.down h2
  simpa using h3

end FieldZ

theorem LeafTwFieldZ_of : LeafTwFieldZ := by
  intro q _ j K hK ζ c h
  have : IsDomain K := hK.isDomain
  exact FieldZ.key j ζ c h

end LateralTheory.E.E8.TwSec
