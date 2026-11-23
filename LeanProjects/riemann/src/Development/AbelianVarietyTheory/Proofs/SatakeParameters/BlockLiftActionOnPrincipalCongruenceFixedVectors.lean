import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Val

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem val_lt_one_of_norm_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => z ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have h2 : Filter.Tendsto (fun n : ℕ => e z ^ n) Filter.atTop (nhds 0) := by
    have := ((he.tendsto 0).comp h1)
    simpa [Function.comp_def, map_pow] using this
  have h3 : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  obtain ⟨n, hn⟩ := (h2.eventually h3).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation F (e z ^ n) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hn (not_lt.2 this)

theorem val_natCast_le_one (c : ℕ) : valuation F (c : F) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact (valuation F).map_add_le ih (by simp)

theorem val_le_one_of_norm_le_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ ≤ 1) :
    valuation F (e z) ≤ 1 := by
  let zi : ℤ_[g] := ⟨z, hz⟩
  have hm := PadicInt.sub_zmodRepr_mem zi
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hm
  have hm' : ‖z - (zi.zmodRepr : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at hm
    exact hm
  have h1 := val_lt_one_of_norm_lt_one e he hm'
  have hz' : e z = e (z - (zi.zmodRepr : ℚ_[g])) + (zi.zmodRepr : F) := by
    rw [map_sub, map_natCast]; ring
  rw [hz']
  exact (valuation F).map_add_le h1.le (val_natCast_le_one _)

theorem norm_lt_one_of_val_lt_one (e : ℚ_[g] ≃+* F) (he : Continuous e) {y : ℚ_[g]}
    (hy : valuation F (e y) < 1) : ‖y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hy0 : y ≠ 0 := by rintro rfl; simp at hc; exact absurd hc (by norm_num)
  have h1 : ‖y⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hc
  have h2 := val_le_one_of_norm_le_one e he h1
  have h3 : valuation F (e y) * valuation F (e y⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
  have h4 : valuation F (e y) * valuation F (e y⁻¹) ≤ valuation F (e y) * 1 := by gcongr
  rw [h3, mul_one] at h4
  exact absurd hy (not_lt.2 h4)

theorem entry_of_val (e : ℚ_[g] ≃+* F) (he : Continuous e) (x : F) (c : ℕ) (hx : valuation F (x - c) < 1) :
    ∃ hA : ‖e.symm x‖ ≤ 1, PadicInt.toZMod (⟨e.symm x, hA⟩ : ℤ_[g]) = c := by
  have h1 : ‖e.symm x - c‖ < 1 :=
    norm_lt_one_of_val_lt_one e he (by rwa [map_sub, map_natCast, e.apply_symm_apply])
  have hc : ‖(c : ℚ_[g])‖ ≤ 1 := by
    have := PadicInt.norm_le_one (c : ℤ_[g])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  have hA : ‖e.symm x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (e.symm x - c) (c : ℚ_[g])
    rw [sub_add_cancel] at this
    exact this.trans (max_le h1.le hc)
  refine ⟨hA, ?_⟩
  let zi : ℤ_[g] := ⟨e.symm x, hA⟩
  have hm : zi - (c : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def]
    simpa using h1
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hm
  exact hm

end Val

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

section Mat

variable {g : ℕ} [Fact g.Prime]

def bm (r t : ℕ) (h : Gn g r) : Mt g (r + t) := fun i j =>
  if (i : ℕ) < r ∧ (j : ℕ) < r then entN (h : Mt g r) i j
  else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then entN ((1 : Gn g t) : Mt g t) (i - r) (j - r) else 0

theorem bm_isUnit (r t : ℕ) (h : Gn g r) : IsUnit (bm r t h) := by
  set M := bm r t h with hM
  have h0 : InPar r M := fun i j hj hi => by
    rw [hM]; show bm r t h i j = 0; unfold bm; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = h := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, entN, hM, bm, hi, hj]
  have h2 : br r t M = 1 := by
    ext i j
    simp [br, entN, hM, bm]
  have hd := LabelDet.det_inPar r t M h0
  rw [h1, h2, Matrix.det_one, mul_one] at hd
  rw [Matrix.isUnit_iff_isUnit_det, hd]
  exact Matrix.isUnits_det_units h

theorem blk_val (r t : ℕ) (h : Gn g r) : ((blk r t (r + t) h 1 : Gn g (r + t)) : Mt g (r + t)) = bm r t h := by
  show ((toG (bm r t h) : Gn g (r + t)) : Mt g (r + t)) = bm r t h
  unfold toG
  rw [dif_pos (bm_isUnit r t h)]
  exact IsUnit.unit_spec _

theorem bm_apply (r t : ℕ) (h : Gn g r) (a b : Fin (r + t)) : bm r t h a b =
    if hab : (a : ℕ) < r ∧ (b : ℕ) < r then (h : Mt g r) ⟨a, hab.1⟩ ⟨b, hab.2⟩ else if a = b then 1 else 0 := by
  unfold bm
  by_cases hab : (a : ℕ) < r ∧ (b : ℕ) < r
  · rw [if_pos hab, dif_pos hab]; simp [entN, hab]
  · rw [if_neg hab, dif_neg hab]
    by_cases h2 : r ≤ (a : ℕ) ∧ r ≤ (b : ℕ)
    · rw [if_pos h2]
      have ha : (a : ℕ) - r < t := by omega
      have hb : (b : ℕ) - r < t := by omega
      simp only [entN, dif_pos (And.intro ha hb), Units.val_one, Matrix.one_apply, Fin.ext_iff]
      congr 1
      apply propext
      omega
    · rw [if_neg h2, if_neg]
      intro e; subst e; omega

end Mat

end GlobalTheory.SerSys.BlockLift

namespace GlobalTheory.SerSys.BlockLift

open ValuativeRel Formalism.MainNotions.ArithmeticCylinders

theorem blockLift_act (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (r t : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V)
    (hu : u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) (h : GL (Fin r) (ZMod g))
    (h' : GL (Fin (r + t)) F) (hl : GlobalTheory.PendOf.IsLiftN h h') :
    ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  classical
  have hent : ∀ a b : Fin (r + t), ∃ hA : ‖e.symm (h'.val a b)‖ ≤ 1,
      PadicInt.toZMod (⟨e.symm (h'.val a b), hA⟩ : ℤ_[g]) = bm r t h a b := by
    intro a b
    have hab := hl a b
    rw [bm_apply]
    by_cases hc : (a : ℕ) < r ∧ (b : ℕ) < r
    · rw [dif_pos hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he _ _ hab
      exact ⟨hA, by rw [hA', ZMod.natCast_zmod_val]⟩
    · rw [dif_neg hc] at hab ⊢
      obtain ⟨hA, hA'⟩ := entry_of_val e he (h'.val a b) (if a = b then 1 else 0)
        (by rw [hab]; split_ifs <;> simp)
      exact ⟨hA, by rw [hA']; split_ifs <;> simp⟩
  choose hA hA' using hent
  let A : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g] := fun a b => ⟨e.symm (h'.val a b), hA a b⟩
  have hmap : (PadicInt.toZMod (p := g)).mapMatrix A = bm r t h := by
    ext a b
    exact hA' a b
  have hdet : IsUnit A.det := by
    by_contra hn
    have h1 : A.det ∈ IsLocalRing.maximalIdeal ℤ_[g] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, RingHom.map_det, hmap] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (bm_isUnit r t h)).ne_zero h1
  let A' : GL (Fin (r + t)) ℤ_[g] := Matrix.GeneralLinearGroup.mk'' A hdet
  have hred : red g (r + t) A' = blk r t (r + t) h 1 := by
    ext a b
    rw [blk_val]
    exact hA' a b
  have hh' : Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) A') = h' := by
    ext a b
    show e (algebraMap ℤ_[g] ℚ_[g] (A a b)) = h'.val a b
    rw [PadicInt.algebraMap_apply]
    exact e.apply_symm_apply _
  have hx0 : red g (r + t) (Function.invFun (red g (r + t)) (blk r t (r + t) h 1)) = blk r t (r + t) h 1 :=
    Function.invFun_eq ⟨A', hred⟩
  have hk : red g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A') = 1 := by
    rw [map_mul, map_inv, hx0, hred, inv_mul_cancel]
  have hfix := (Submodule.mem_iInf _).1 hu ⟨_, hk⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hfix
  have hsplit : h' = Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1)) *
      Matrix.GeneralLinearGroup.map e.toRingHom
        (inc g (r + t) ((Function.invFun (red g (r + t)) (blk r t (r + t) h 1))⁻¹ * A')) := by
    rw [← hh', lift, ← map_mul, ← map_mul, mul_inv_cancel_left]
  rw [hsplit, map_mul, Module.End.mul_apply]
  congr 1

end GlobalTheory.SerSys.BlockLift
