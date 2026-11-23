import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

noncomputable section

namespace GlobalTheory.ParRead

open ValuativeRel Matrix

variable {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

theorem lt_one_mem_nhds : {x : F | valuation F x < 1} ∈ nhds (0 : F) :=
  (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, by simp⟩

theorem val_lt_one {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℚ_[g]} (hz : ‖z‖ < 1) :
    valuation F (e z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (e z) ^ n) Filter.atTop (nhds 0) := by
    have := (he.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)
    rw [map_zero] at this
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨n, hn⟩ := (h1.eventually lt_one_mem_nhds).exists
  rw [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

theorem val_lt_one_of_red {e : ℚ_[g] ≃+* F} (he : Continuous e) {z : ℤ_[g]}
    (hz : PadicInt.toZMod z = 0) : valuation F (e z) < 1 := by
  have : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
  exact val_lt_one he this

theorem val_le_one {e : ℚ_[g] ≃+* F} (he : Continuous e) (z : ℤ_[g]) : valuation F (e z) ≤ 1 := by
  set m : ℕ := (PadicInt.toZMod z).val
  have hm : PadicInt.toZMod (z - (m : ℤ_[g])) = 0 := by
    rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  have e1 : e (z : ℚ_[g]) = (m : F) + e ((z - (m : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast]; ring
  rw [e1]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (val_lt_one_of_red he hm).le)
  clear e1 hm
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

def intHom {e : ℚ_[g] ≃+* F} (he : Continuous e) : ℤ_[g] →+* 𝒪[F] :=
  (e.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])).codRestrict 𝒪[F] fun z => by
    rw [Valuation.mem_integer_iff]; exact val_le_one he z

theorem map_inc_mem_KO {e : ℚ_[g] ≃+* F} (he : Continuous e) {n : ℕ} (k : GL (Fin n) ℤ_[g]) :
    Matrix.GeneralLinearGroup.map e.toRingHom (inc g n k) ∈ GlobalTheory.SplitWeil.KO F (Fin n) := by
  refine ⟨Matrix.GeneralLinearGroup.map (intHom he) k, ?_⟩
  ext i j
  simp [inc, intHom]
  rfl

theorem act_inc {e : ℚ_[g] ≃+* F} (he : Continuous e) {ξ : Fˣ →* ℂˣ} {χ : (ZMod g)ˣ →* ℂˣ}
    (hT : TamePart (ξ.comp (Units.map e.toMonoidHom)) χ) {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin (r + t)) F) V} {u : V} (hu : GlobalTheory.SplitRead.IsBlockVec ξ ρ u)
    (k : GL (Fin (r + t)) ℤ_[g]) (h0 : InPar r (red g (r + t) k : Mt g (r + t)))
    (h1 : tl r (red g (r + t) k : Mt g (r + t)) = 1) (c : (ZMod g)ˣ)
    (hc : (c : ZMod g) = (br r t (red g (r + t) k : Mt g (r + t))).det) :
    ρ (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)) u = ((χ c : ℂˣ) : ℂ) • u := by
  have hred : ∀ i j, (red g (r + t) k : Mt g (r + t)) i j = PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j) :=
    fun i j => by simp [red]
  have hent : ∀ i j, (Matrix.GeneralLinearGroup.map e.toRingHom (inc g (r + t) k)).val i j =
      e ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) i j : ℚ_[g]) := fun i j => by simp [inc]
  set d : ℤ_[g] := ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)).det with hd
  have hbr : br r t (red g (r + t) k : Mt g (r + t)) =
      (PadicInt.toZMod (p := g)).mapMatrix ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]).submatrix (Fin.natAdd r) (Fin.natAdd r)) := by
    ext i j
    have hi : r + (i : ℕ) < r + t := by omega
    have hj : r + (j : ℕ) < r + t := by omega
    simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), hred]
    rfl
  have hdc : PadicInt.toZMod d = c := by rw [hc, hbr, hd, RingHom.map_det]
  have hdu : IsUnit d := by
    by_contra h
    have : d ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, hdc] at this
    exact c.ne_zero this
  refine (hu _ (map_inc_mem_KO he k) ?_ ?_
    (Units.map e.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom hdu.unit)) ?_).trans ?_
  · intro i j
    rw [hent]
    apply val_lt_one_of_red he
    rw [← hred]
    exact h0 _ _ (by simp) (by simp)
  · intro i j
    rw [hent]
    have hij : (red g (r + t) k : Mt g (r + t)) (Fin.castAdd t i) (Fin.castAdd t j) = (1 : Mt g r) i j := by
      rw [← h1]
      have hi : (i : ℕ) < r + t := by omega
      have hj : (j : ℕ) < r + t := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj)]
      rfl
    have h2 : PadicInt.toZMod ((k : Matrix (Fin (r + t)) (Fin (r + t)) ℤ_[g]) (Fin.castAdd t i) (Fin.castAdd t j) -
        if i = j then 1 else 0) = 0 := by
      rw [map_sub, ← hred, hij, Matrix.one_apply]
      split_ifs <;> simp
    have := val_lt_one_of_red he h2
    convert this using 2
    split_ifs <;> simp
  · simp [hd, RingHom.map_det]
    congr 1
  · have h2 := hT hdu.unit
    have h3 : Units.map (PadicInt.toZMod (p := g)).toMonoidHom hdu.unit = c := Units.ext (by simpa using hdc)
    rw [h3, MonoidHom.comp_apply] at h2
    rw [h2]

theorem inPar_one {r n : ℕ} : InPar r (1 : Mt g n) := fun i j hj hi => by
  rw [Matrix.one_apply_ne]
  intro h; rw [h] at hi; omega

theorem tl_one {r t : ℕ} : tl r (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : (i : ℕ) < r + t := by omega
  have hj : (j : ℕ) < r + t := by omega
  simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]

theorem br_one {r t : ℕ} : br r t (1 : Mt g (r + t)) = 1 := by
  ext i j
  have hi : r + (i : ℕ) < r + t := by omega
  have hj : r + (j : ℕ) < r + t := by omega
  simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, dif_pos (And.intro hi hj), Matrix.one_apply, Fin.ext_iff]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · rw [if_neg (by omega), if_neg h]

theorem blk_parts {r t : ℕ} (y : Gn g t) :
    InPar r (blk r t (r + t) 1 y : Mt g (r + t)) ∧ tl r (blk r t (r + t) 1 y : Mt g (r + t)) = 1 ∧
      br r t (blk r t (r + t) 1 y : Mt g (r + t)) = (y : Mt g t) := by
  set M : Mt g (r + t) := fun i j : Fin (r + t) =>
    if (i : ℕ) < r ∧ (j : ℕ) < r then Formalism.MainNotions.ArithmeticCylinders.entN ((1 : Gn g r) : Mt g r) i j
    else if r ≤ (i : ℕ) ∧ r ≤ (j : ℕ) then Formalism.MainNotions.ArithmeticCylinders.entN (y : Mt g t) (i - r) (j - r) else 0 with hM
  have h0 : InPar r M := fun i j hj hi => by rw [hM]; dsimp only; rw [if_neg (by omega), if_neg (by omega)]
  have h1 : tl r M = 1 := by
    ext i j
    have hi : (i : ℕ) < r + t := by omega
    have hj : (j : ℕ) < r + t := by omega
    simp [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hM, hi, hj]
  have h2 : br r t M = y := by
    ext i j
    simp [br, Formalism.MainNotions.ArithmeticCylinders.entN, hM]
  have hu : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, LabelDet.det_inPar r t M h0, h1, h2, Matrix.det_one, one_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have hb : (blk r t (r + t) 1 y : Mt g (r + t)) = M := by
    show ((toG M : Gn g (r + t)) : Mt g (r + t)) = M
    rw [toG, dif_pos hu]; rfl
  rw [hb]; exact ⟨h0, h1, h2⟩

theorem isParVec_of_isBlockVec : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (ξ : Fˣ →* ℂˣ) (χ : (ZMod g)ˣ →* ℂˣ),
    TamePart (ξ.comp (Units.map e.toMonoidHom)) χ → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), GlobalTheory.SplitRead.IsBlockVec ξ ρ u →
    IsParVec (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) r t χ u := by
  intro g _ F _ _ _ _ e he ξ χ hT r t V _ _ ρ u hu
  have hsurj : ∀ x : Gn g (r + t), red g (r + t) (Function.invFun (red g (r + t)) x) = x :=
    fun x => Function.invFun_eq (Model.red_surjective _ x)
  refine ⟨?_, ?_, ?_⟩
  · rw [Model.mem_principalCongruenceFixedVectors_iff]
    intro k hk
    have := act_inc he hT hu k (by rw [hk, Units.val_one]; exact inPar_one) (by rw [hk, Units.val_one]; exact tl_one) 1
      (by rw [hk, Units.val_one, Units.val_one, br_one, Matrix.det_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro x h0 h1 h2
    have := act_inc he hT hu (Function.invFun (red g (r + t)) x) (by rw [hsurj]; exact h0) (by rw [hsurj]; exact h1) 1
      (by rw [hsurj, h2, Matrix.det_one, Units.val_one])
    rw [map_one, Units.val_one, one_smul] at this
    exact this
  · intro y
    obtain ⟨h0, h1, h2⟩ := blk_parts (r := r) y
    have := act_inc he hT hu (Function.invFun (red g (r + t)) (blk r t (r + t) 1 y)) (by rw [hsurj]; exact h0)
      (by rw [hsurj]; exact h1) (Matrix.GeneralLinearGroup.det y)
      (by rw [hsurj, h2, Matrix.GeneralLinearGroup.val_det_apply])
    exact this

end GlobalTheory.ParRead
