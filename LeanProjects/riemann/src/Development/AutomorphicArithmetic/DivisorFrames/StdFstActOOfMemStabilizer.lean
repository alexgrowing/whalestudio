import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.standardActionStabilizer

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

private theorem isIntM_mul {b a c : ℕ} {N : Matrix (Fin b) (Fin a) (Lev.EAf D)} {κ : Matrix (Fin a) (Fin c) (Lev.EAf D)}
    (hN : IsIntM N) (hκ : IsIntM κ) : IsIntM (N * κ) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun l _ => mul_mem (hN i l) (hκ l j)

private theorem inId_mul {b a c : ℕ} {I : Ideal (𝓞 D.host.E)} {N : Matrix (Fin b) (Fin a) (Lev.EAf D)}
    {κ : Matrix (Fin a) (Fin c) (Lev.EAf D)} (hκ : IsIntM κ) (i : Fin b) (hN : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i l))
    (j : Fin c) : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * κ) i j) := by
  have hm : (N * κ) i j ∈ OO := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => mul_mem (hN l).1 (hκ l j)
  refine ⟨hm, ?_⟩
  have e : (⟨(N * κ) i j, hm⟩ : OO) = ∑ l, (⟨N i l, (hN l).1⟩ : OO) * ⟨κ l j, hκ l j⟩ := Subtype.ext (by
    show (N * κ) i j = _
    rw [Matrix.mul_apply]
    push_cast
    rfl)
  rw [e]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hN l).2

private theorem topL_mul {b a : ℕ} (N : Matrix (Fin b) (Fin a) (Lev.EAf D)) (κ : Matrix (Fin a) (Fin a) (Lev.EAf D)) :
    topL a (N * κ) = topL a N * κ := by
  ext i j
  simp only [topL, Matrix.mul_apply]
  by_cases hi : i.1 < b
  · simp [hi]
  · simp [hi]

private theorem det_int {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : N.det ∈ OO := by
  let A : Matrix (Fin k) (Fin k) OO := fun i j => ⟨N i j, hN i j⟩
  have eA : N.det = ((A.det : OO) : Lev.EAf D) := by
    rw [show N = (OO).subtype.mapMatrix A from rfl]
    exact (RingHom.map_det (OO).subtype A).symm
  rw [eA]
  exact A.det.2

private theorem isUnitDet_unique {e : AE D} {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x x' : (AE D)ˣ}
    (h : IsUnitDet e N x) (h' : IsUnitDet e N x') : x = x' :=
  Units.ext (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.eq_of_parts (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm))

private theorem idem_mul {R : Type} [CommRing R] {ε a b : R} (hε : ε * ε = ε) :
    (1 - ε + ε * a) * (1 - ε + ε * b) = 1 - ε + ε * (a * b) := by
  linear_combination (a * b - a - b + 1) * hε

private theorem succ_mul_succ_sub_one_div_succ {R : Type} [CommRing R] {ε z y yi a b : R} (hε : ε * ε = ε) (hz : z = 1 - ε + ε * (a * b))
    (hy : y = 1 - ε + ε * b) (hyy : y * yi = 1) : z * yi = 1 - ε + ε * a := by
  subst hz hy
  linear_combination (1 - ε + ε * a) * hyy - (a * b - a - b + 1) * yi * hε

private theorem isUnitDet_mul {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)} {x y : (AE D)ˣ} (hx : IsUnitDet e L x) (hy : IsUnitDet e κ y) :
    IsUnitDet e (L * κ) (x * y) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hx.1, hy.1, mul_one]
  · rw [Units.val_mul, map_mul, hx.2.1, hy.2.1, Matrix.det_mul, idem_mul hε]
  · rw [_root_.mul_inv_rev, Units.val_mul, map_mul]
    exact mul_mem hy.2.2 hx.2.2

set_option maxHeartbeats 1000000 in
private theorem isUnitDet_div {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hκ : IsIntM κ) {z y : (AE D)ˣ} (hz : IsUnitDet e (L * κ) z)
    (hy : IsUnitDet e κ y) : IsUnitDet e L (z * y⁻¹) := by
  have hε : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hyy : toEAf D (y : AE D) * toEAf D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hinv : infPart D ((y⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (infPart D) (Units.mul_inv y)
    rwa [map_mul, hy.1, one_mul, map_one] at this
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, hz.1, hinv, mul_one]
  · rw [Units.val_mul, map_mul]
    exact succ_mul_succ_sub_one_div_succ hε (hz.2.1.trans (by rw [Matrix.det_mul])) hy.2.1 hyy
  · have e0 : (z * y⁻¹)⁻¹ = y * z⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    rw [e0]
    rw [Units.val_mul]
    rw [map_mul]
    refine mul_mem ?_ hz.2.2
    rw [hy.2.1]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE (det_int hκ))

private theorem unitChar_mul (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {k : ℕ} (L κ : Matrix (Fin k) (Fin k) (Lev.EAf D)) (hκ : IsIntM κ) {y : (AE D)ˣ} (hy : IsUnitDet e κ y) :
    unitChar ν e (L * κ) = (((ν y)⁻¹ : Circle) : ℂ) * unitChar ν e L := by
  unfold unitChar
  by_cases hL : ∃ x, IsUnitDet e L x
  · have hLκ : ∃ x, IsUnitDet e (L * κ) x := ⟨_, isUnitDet_mul he hL.choose_spec hy⟩
    rw [dif_pos hL, dif_pos hLκ, isUnitDet_unique hLκ.choose_spec (isUnitDet_mul he hL.choose_spec hy), map_mul,
      _root_.mul_inv_rev, Circle.coe_mul]
  · have hLκ : ¬ ∃ x, IsUnitDet e (L * κ) x := fun ⟨z, hz⟩ => hL ⟨_, isUnitDet_div he hκ hz hy⟩
    rw [dif_neg hL, dif_neg hLκ, mul_zero]

private theorem half_act {e : AE D} (S T : HSp D) (g : GA D S) {x : WO S T} (h : IsHalf e x) :
    IsHalf e (actO S T g 1 x) := fun i j => by
  unfold actO
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_assoc, mul_left_comm, h m l]

private theorem act_act (S T : HSp D) (g : GA D S) (x : WO S T) :
    actO S T g⁻¹ 1 (actO S T g 1 x) = x := by
  have h1 : ∀ V : HSp D, Formalism.L2.Theta.mt V 1 = 1 := fun V => by simp [Formalism.L2.Theta.mt]
  have h2 : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    rw [← h1 S, ← inv_mul_cancel g]; simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_inv, h1, Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem st_int {n : ℕ} {β k : GL (Fin n) (Lev.EAf D)} (h : k ∈ Formalism.L2.DIV.St β) :
    IsIntM (β⁻¹ * k * β : GL (Fin n) (Lev.EAf D)).val := by
  obtain ⟨y, rfl⟩ := h
  have e : (β⁻¹ * Formalism.L2.DIV.frGL β y * β : GL (Fin n) (Lev.EAf D)) = Formalism.L2.DIV.intGL _ _ n y := by
    show β⁻¹ * (β * Formalism.L2.DIV.intGL _ _ n y * β⁻¹) * β = _
    group
  rw [e]
  exact fun i j => (y.val i j).2

end UpperTheory.standardActionStabilizer

open UpperTheory.standardActionStabilizer in
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 4000000 in
theorem UpperTheory.stdFst_actO_of_mem_stabilizer :
    ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      IsIdemSum e Z → ∀ g : GA D S, Lev.finE S g ∈ Formalism.L2.DIV.St βS → ∀ y : (AE D)ˣ,
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)).val y →
      ∀ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT (actO S T g 1 x) = ((ν y : Circle) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x := by
  intro D S T βS βT ν e Z I he g hg y hy x
  have hκ' := st_int hg
  have hκ := st_int ((Formalism.L2.DIV.St βS).inv_mem hg)
  have einv : (βS⁻¹ * (Lev.finE S g)⁻¹ * βS : GL (Fin S.rank) (Lev.EAf D)) = (βS⁻¹ * Lev.finE S g * βS)⁻¹ := by group
  rw [einv] at hκ
  have hfr := GlobalTheory.T.frameMatrix_weilPairAction_left_inv D S T βS βT g x
  generalize (βS⁻¹ * Lev.finE S g * βS : GL (Fin S.rank) (Lev.EAf D)) = γ at hy hκ hκ' hfr
  have hkk : (γ⁻¹).val * γ.val = 1 := Units.inv_mul γ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [hfr]
  generalize frMapO S T βS βT x = N
  have hH : IsHalf e (actO S T g 1 x) ↔ IsHalf e x :=
    ⟨fun h => by have := half_act S T g⁻¹ h; rwa [act_act] at this, half_act S T g⟩
  have hI : IsIntM (N * (γ⁻¹).val) ↔ IsIntM N := by
    refine ⟨fun h => ?_, fun h => isIntM_mul h hκ⟩
    have := isIntM_mul h hκ'
    rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
  have hR : (∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((N * (γ⁻¹).val) i j)) ↔
      ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j) := by
    refine ⟨fun h i j hi => ?_, fun h i j hi => inId_mul hκ i (fun l => h i l hi) j⟩
    have := inId_mul hκ' i (fun l => h i l hi) j
    rwa [Matrix.mul_assoc, hkk, Matrix.mul_one] at this
  have hU := unitChar_mul ν he (topL S.rank N * (γ⁻¹).val) γ.val hκ' hy
  rw [Matrix.mul_assoc, hkk, Matrix.mul_one] at hU
  by_cases hc : IsHalf e x ∧ IsIntM N ∧ ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j)
  · rw [if_pos hc, if_pos ⟨hH.2 hc.1, hI.2 hc.2.1, hR.2 hc.2.2⟩, topL_mul, hU, ← mul_assoc, ← Circle.coe_mul,
      mul_inv_cancel, Circle.coe_one, one_mul]
  · rw [if_neg hc, if_neg fun h => hc ⟨hH.1 h.1, hI.1 h.2.1, hR.1 h.2.2⟩, mul_zero]
