import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleCharRestrictLocalUnitsResidueChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_eq_zero_of_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (a : AE D) (ha : toEAf D a = 0) : q.pr a = 0 := by
  have h0 : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) he).1
  have h1 : finPart D a = 0 :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective (by
      rw [map_zero]; exact ha)
  have h2 : q.e * a = 0 := GlobalTheory.LatVac.eq_zero_of_parts _ (by rw [map_mul, h0, zero_mul]) (by rw [map_mul, h1, mul_zero])
  rw [← q.pr_sec (q.pr a), q.sec_pr, h2, map_zero]

def prF (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) : EAf D →+* k :=
  (RingHom.liftOfSurjective (toEAf D) (fun s => GlobalTheory.ResLoc.toEAf_surj s))
    ⟨q.pr, fun a ha => (RingHom.mem_ker).2 (q.pr_eq_zero_of_toEAf he a ((RingHom.mem_ker).1 ha))⟩

theorem prF_toEAf (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (a : AE D) :
    q.prF he (toEAf D a) = q.pr a :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem pr_mem_iff (q : SplitPt D k) (a : AE D) :
    q.pr a ∈ 𝒪[k] ↔ toEAf D q.e * toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [q.int_iff, q.sec_pr, ← map_mul]
  exact ⟨GlobalTheory.IdemRes.toEAf_mem_of_finPart, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf⟩

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_iff_val_lt (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔
      valuation k (q.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D)) < 1 := by
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  rw [e1, prF_toEAf]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, Submodule.zero_mem, true_iff]
    simp
  have hx' : (x : D.host.E) ≠ 0 := fun h => hx (RingOfIntegers.coe_eq_zero_iff.1 h)
  set y := q.pr (incA D (x : D.host.E)) with hy
  have hy0 : y ≠ 0 := fun h => by
    have : (q.pr.comp (incA D)) (x : D.host.E) = 0 := h
    exact hx' ((map_eq_zero_iff _ (q.pr.comp (incA D)).injective).1 this)
  have hinv : q.pr (incA D ((x : D.host.E)⁻¹)) = y⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  rw [he.2 x hx, ← q.sec_pr, ← q.int_iff, hinv]
  change ¬ valuation k y⁻¹ ≤ 1 ↔ _
  rw [not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy0), inv_inv]

theorem val_lt_of_mem_idS (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) :
    valuation k (q.prF he s.1) < 1 := by
  have hint : ∀ c : Formalism.L2.Herm.intAf D.host.F D.host.E, valuation k (q.prF he c.1) ≤ 1 := fun c => by
    obtain ⟨a, ha⟩ := GlobalTheory.ResLoc.toEAf_surj c.1
    have := (q.pr_mem_iff a).2 (by rw [ha]; exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1 c.2)
    rw [← ha, prF_toEAf]; exact this
  refine Submodule.span_induction (p := fun s _ => valuation k (q.prF he s.1) < 1) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact (q.mem_iff_val_lt he a).1 ha
  · simp
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hint c) zero_le').trans_lt (by rwa [one_mul])

theorem resS_eq_zero_of_mem {PP : Formalism.L2.DIV.Pl D.host.E} {s : Formalism.L2.Herm.intAf D.host.F D.host.E}
    (hs : s ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal) : Formalism.L2.DIV.resS D.host.F PP s = 0 := by
  have : Formalism.L2.DIV.idS D.host.F PP.asIdeal ≤ RingHom.ker (Formalism.L2.DIV.resS D.host.F PP) :=
    Ideal.map_le_iff_le_comap.2 fun b hb => Ideal.mem_comap.2 ((RingHom.mem_ker).2 (by
      rw [Formalism.L2.DIV.resS_oToS]; exact Ideal.Quotient.eq_zero_iff_mem.2 hb))
  exact (RingHom.mem_ker).1 (this hs)

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prF_mem_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    q.prF he z ∈ 𝒪[k] ↔ toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨a, rfl⟩ := GlobalTheory.ResLoc.toEAf_surj z
  rw [prF_toEAf]; exact q.pr_mem_iff a

theorem resS_eq_zero_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP s = 0 ↔ valuation k (q.prF he s.1) < 1 := by
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h1 : Formalism.L2.DIV.resS D.host.F PP s = Ideal.Quotient.mk PP.asIdeal a := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) PP a, ← sub_eq_zero, ← map_sub]
    exact resS_eq_zero_of_mem ha
  have h2 := q.val_lt_of_mem_idS he ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub] at h2
  rw [h1, Ideal.Quotient.eq_zero_iff_mem, q.mem_iff_val_lt he]
  constructor
  · intro h; simpa using Valuation.map_add_lt _ h2 h
  · intro h; simpa using Valuation.map_sub_lt _ h h2

theorem mem_intAf_iff (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (z : EAf D) :
    z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ q.prF he z ∈ 𝒪[k] := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  rw [q.prF_mem_iff he]
  constructor
  · intro hz
    exact ⟨mul_mem (sub_mem (one_mem _) hint) hz, mul_mem hint hz⟩
  · rintro ⟨h1, h2⟩
    have : z = (1 - toEAf D q.e) * z + toEAf D q.e * z := by
      rw [sub_mul, one_mul, sub_add_cancel]
    rw [this]; exact add_mem h1 h2

set_option maxHeartbeats 1000000 in
theorem resS_off (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (PP' : Formalism.L2.DIV.Pl D.host.E) (hne : PP' ≠ PP) (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have h0 : Formalism.L2.DIV.resS D.host.F PP' ⟨toEAf D q.e, hint⟩ = 0 := by
    obtain ⟨a, h1, h2⟩ := GlobalTheory.FunObj.Comparison₂.exists_resS_eq PP' ⟨toEAf D q.e, hint⟩
    rw [h1, GlobalTheory.FunObj.Comparison₂.mk_eq_zero_iff]
    rw [GlobalTheory.FunObj.Comparison₂.cptO_apply PP' ⟨toEAf D q.e, hint⟩] at h2
    change Valued.v (GlobalTheory.StdFrames.cpt PP' (toEAf D q.e) - _) < 1 at h2
    rw [(GlobalTheory.StdFrames.cpt_of_isIdemAt he).2 PP' hne, zero_sub, Valuation.map_neg] at h2
    exact h2
  have e1 : (⟨(1 - toEAf D q.e) * z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (1 - ⟨toEAf D q.e, hint⟩) * ⟨z, hz⟩ :=
    Subtype.ext (by rw [Subring.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one])
  refine (congrArg (Formalism.L2.DIV.resS D.host.F PP') e1).trans ?_
  rw [map_mul, map_sub, map_one, h0, sub_zero, one_mul]

end GlobalTheory.FinPl.SplitPt

namespace GlobalTheory.FinPl.SplitPt

theorem exists_lift_isRed : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∃ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) ∧ GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ∧ (∀ z : EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) ∧ ∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP' ≠ PP → ∀ (z : EAf D) (hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hz' : (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.resS D.host.F PP' ⟨(1 - toEAf D q.e) * z, hz'⟩ = Formalism.L2.DIV.resS D.host.F PP' ⟨z, hz⟩ := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  refine ⟨q.prF he, q.prF_toEAf he, ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal,
    fun s => (q.prF_mem_iff he s.1).2 (mul_mem hint s.2), fun s => q.resS_eq_zero_iff he s⟩,
    q.mem_intAf_iff he, fun PP' hne z hz hz' => q.resS_off he PP' hne z hz hz'⟩

end GlobalTheory.FinPl.SplitPt

end
