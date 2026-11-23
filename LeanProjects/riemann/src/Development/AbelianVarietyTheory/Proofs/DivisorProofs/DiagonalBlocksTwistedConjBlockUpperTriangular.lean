import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockParabolicSubgroupLeviProjection
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.BlocksTwist

theorem toG_map {F : Type} [Field F] (t : F →+* F) {m : ℕ} (M : Matrix (Fin m) (Fin m) F) (h : IsUnit M) :
    toG (M.map t) = gal t m (toG M) := by
  have h' : IsUnit (M.map t) := by simpa using h.map (t.mapMatrix)
  unfold toG
  rw [dif_pos h', dif_pos h]
  ext i j
  simp [gal]

theorem coe_gal {F : Type} [Field F] (t : F →+* F) (n : ℕ) (p : GL (Fin n) F) :
    ((gal t n p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (p : Matrix (Fin n) (Fin n) F).map t := by
  simp [gal]

theorem ent_map {F : Type} [Field F] (t : F →+* F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map t) i j = t (ent M i j) := by
  unfold ent
  split_ifs <;> simp

theorem tl_map {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map t) = (tl a M).map t := by
  ext i j; simp [tl, ent_map]

theorem br_map {F : Type} [Field F] (t : F →+* F) (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map t) = (br a b M).map t := by
  ext i j; simp [br, ent_map]

theorem inPar_gal {F : Type} [Field F] (t : F →+* F) (a : ℕ) {n : ℕ} (p : GL (Fin n) F) (hp : InPar a p) :
    InPar a (gal t n p) := by
  intro i j hj hi
  rw [coe_gal]
  simp [hp i j hj hi]

theorem blocks_twist : ∀ (F : Type) [Field F] (t : F →+* F) (a b n : ℕ), n = a + b → ∀ (p x : GL (Fin n) F), InPar a p → InPar a x → tlG a (p⁻¹ * x * gal t n p) = (tlG a p)⁻¹ * tlG a x * gal t a (tlG a p) ∧ brG a b (p⁻¹ * x * gal t n p) = (brG a b p)⁻¹ * brG a b x * gal t b (brG a b p) := by
  intro F _ t a b n hn p x hp hx
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := BlockPar.block_par F a b n hn
  let p' : H := ⟨p, (hH p).2 hp⟩
  let x' : H := ⟨x, (hH x).2 hx⟩
  let g' : H := ⟨gal t n p, (hH _).2 (inPar_gal t a p hp)⟩
  have key : π (p'⁻¹ * x' * g') = (π p')⁻¹ * π x' * π g' := by simp only [map_mul, map_inv]
  rw [hπ, hπ, hπ, hπ] at key
  have e : ((p'⁻¹ * x' * g' : H) : GL (Fin n) F) = p⁻¹ * x * gal t n p := rfl
  rw [e] at key
  have htl : tlG a (gal t n p) = gal t a (tlG a p) := by
    subst hn
    unfold tlG
    rw [coe_gal, tl_map, toG_map _ _ (BlockPar.units_of_par p hp).1]
  have hbr : brG a b (gal t n p) = gal t b (brG a b p) := by
    subst hn
    unfold brG
    rw [coe_gal, br_map, toG_map _ _ (BlockPar.units_of_par p hp).2]
  simp only [Prod.ext_iff, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at key
  rw [← htl, ← hbr]
  exact key

end GlobalTheory.Shin.BlocksTwist
