import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField IsDedekindDomain GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_unif (q : Unif k) {x : k} (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
  have hx' : x ∈ 𝒪[k] := hx.le
  have hm : (⟨x, hx'⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
    rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have h : x = (c : k) * ((q.1 : 𝒪[k]) : k) := by
    have := congrArg (fun z : 𝒪[k] => (z : k)) hc
    simpa using this.symm
  rw [h, Valuation.map_mul]
  have hc1 : valuation k (c : k) ≤ 1 := c.2
  exact (mul_le_mul_of_nonneg_right hc1 zero_le').trans_eq (one_mul _)

theorem val_unif_lt_one (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 q.2.not_isUnit

theorem val_unif_pos (q : Unif k) : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
  rw [zero_lt_iff, Valuation.ne_zero_iff]
  exact fun h => q.2.ne_zero (Subtype.ext h)

variable {D : D7}

theorem val_prF_le_one (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : Formalism.L2.Herm.intAf D.host.F D.host.E) : valuation k (p.prF he c.1) ≤ 1 :=
  (p.prF_mem_iff he c.1).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he).1 c.2)

theorem val_lt_of_mem_idS_of_forall (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt p.e PP) {I : Ideal (𝓞 D.host.E)} {γ : ValueGroupWithZero k} (hγ : 0 < γ)
    (hI : ∀ a ∈ I, valuation k (p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E a : EAf D)) < γ)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    valuation k (p.prF he s.1) < γ := by
  refine Submodule.span_induction (p := fun s _ => valuation k (p.prF he s.1) < γ) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · simpa using hγ
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (p.val_prF_le_one he c) zero_le').trans_lt (by rwa [one_mul])

theorem val_eq_unif_and_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  intro D k _ _ _ _ p PP he t t' ht ht2 ht'
  let f : 𝓞 D.host.E →+* k :=
    (p.prF he).comp ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.comp (Formalism.L2.DIV.oToS D.host.F D.host.E))
  have hf : ∀ x : 𝓞 D.host.E, f x = p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D) := fun _ => rfl
  have hf' : ∀ x : 𝓞 D.host.E, p.pr (incA D (x : D.host.E)) = f x := fun x =>
    (p.prF_toEAf he (incA D (x : D.host.E))).symm
  have hle : ∀ x, valuation k (f x) ≤ 1 := fun x => p.val_prF_le_one he _
  have hlt : ∀ x, x ∈ PP.asIdeal ↔ valuation k (f x) < 1 := fun x => p.mem_iff_val_lt he x
  rw [hf', hf']
  refine ⟨?_, le_antisymm (hle _) (not_lt.1 fun h => ht' ((hlt _).2 h))⟩
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  refine ⟨q, le_antisymm (val_le_unif q ((hlt _).1 ht)) (not_lt.1 fun hlt' => ?_)⟩
  set γ := valuation k ((q.1 : 𝒪[k]) : k) with hγ
  have hγ0 : 0 < γ := val_unif_pos q

  have hPP : Ideal.span {t} ⊔ PP.asIdeal ^ 2 = PP.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := PP.asIdeal) (I := Ideal.span {t} ⊔ PP.asIdeal ^ 2) (i := 1)
      PP.ne_bot (lt_of_le_of_ne le_sup_right fun h => ht2 (by
        rw [show (2 : ℕ) = 1 + 1 from rfl, h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)))
      (by
        rw [pow_one]
        exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero))
    rwa [pow_one] at h
  have hsq : ∀ a ∈ PP.asIdeal ^ 2, valuation k (f a) < γ := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, Valuation.map_mul]
      calc _ ≤ valuation k (f x) * γ := mul_le_mul_of_nonneg_left (val_le_unif q ((hlt _).1 hy)) zero_le'
        _ < 1 * γ := mul_lt_mul_of_pos_right ((hlt _).1 hx) hγ0
        _ = γ := one_mul _
    · rw [map_add]; exact Valuation.map_add_lt _ hx hy
  have hall : ∀ a ∈ PP.asIdeal, valuation k (f a) < γ := by
    intro a ha
    rw [← hPP] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_add]
    refine Valuation.map_add_lt _ ?_ (hsq y hy)
    rw [map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hle c) zero_le').trans_lt (by rwa [one_mul])

  have hs : toEAf D (p.sec ((q.1 : 𝒪[k]) : k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart ((p.int_iff _).1 q.1.2)
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, hs⟩
  have hsv : p.prF he s.1 = ((q.1 : 𝒪[k]) : k) := (p.prF_toEAf he _).trans (p.pr_sec _)
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h2 := val_lt_of_mem_idS_of_forall p he hγ0 hall ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub, hsv, ← hf] at h2
  have hγ1 : γ < 1 := val_unif_lt_one q
  have haP : a ∈ PP.asIdeal := (hlt a).2 (by simpa using Valuation.map_sub_lt _ hγ1 (h2.trans hγ1))
  have h3 := Valuation.map_add_lt _ h2 (hall a haP)
  rw [sub_add_cancel] at h3
  exact lt_irrefl _ h3

end GlobalTheory.FinPl.SplitPt

end
