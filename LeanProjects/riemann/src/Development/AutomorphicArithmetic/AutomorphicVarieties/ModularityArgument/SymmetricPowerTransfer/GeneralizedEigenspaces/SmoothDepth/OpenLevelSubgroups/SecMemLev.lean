import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.HkEqUOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem away_one {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl)

private theorem finOrb (w : Plc L) (x : GL (Fin n) (Kw w)) :
    UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) x :=
  ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).1 x

private theorem sec_mem_lev {U : Subgroup (UA L n)} {S : Finset (Plc L)} (hP : Places (S : Set (Plc L)))
    (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {j : GL (Fin n) (Kw w)}
    (hj : j ∈ (iw w).J n) : secW n w j ∈ lev U S iw := by
  obtain ⟨h1, h2, -, -⟩ := secSpec L n w (hP.split w (Finset.mem_coe.2 hw))
  have hK : secW n w j ∈ Kall L n := ((factor L n w).2.2.2.2.1 _ (h1 j)).2 (by
    have hKO : GlobalTheory.SplitWeil.KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w n := GlobalTheory.SmGL.SphCompletion.KO_completion w n
    rw [h2, ← hKO]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hj)
  refine Subgroup.mem_inf.2 ⟨hS w hw ⟨h1 j, hK⟩, ?_⟩
  refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
  rw [Subgroup.mem_comap]
  by_cases e : w' = w
  · subst e
    rw [h2]
    exact hj
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h =>
      e (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h.symm)
    rw [away_one ((factor L n w').2.2.1 w hne (h1 j))]
    exact one_mem _

private theorem op_inSpan {w : Plc L} (hw : IsSplitAt w) (d : Fin n → (Kw w)ˣ) (φ : UA L n → V) :
    InSpan w φ (op w (iw w) d φ) := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  simp only [InSpan, op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span
    ⟨secW n w (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out, (secSpec L n w hw).1 _, rfl⟩

private theorem fix_of_AF {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := fun j hj =>
  funext fun g => hφ.level _ (sec_mem_lev hP hS hw hj) g

private theorem hk_val {w : Plc L} (x : GL (Fin n) (Kw w))
    (v : UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n)) :
    (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) x v : UA L n → V) =
      UpperTheory.V.Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) ((iw w).J n) x v :=
  (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ _ _ _ x (finOrb w x)).1 v

private theorem op_keep {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    IsAF R (lev U S iw) (op w (iw w) d φ) := by
  have hsp := hP.split w (Finset.mem_coe.2 hw)
  obtain ⟨-, hc, hsec, -⟩ := secSpec L n w hsp
  have hA : IsAF R (lev U S iw ⊓ away n w) φ :=
    ⟨hφ.left, hφ.inf, fun u hu g => hφ.level u hu.1 g⟩
  have hB := (spanKeep L n V w φ _ (op_inSpan hsp d φ)).2.1 R _ inf_le_right hA
  have hfix : op w (iw w) d φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := by
    have h := (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) (Sig.dg d)
      ⟨φ, fix_of_AF hP hS hw hφ⟩).2
    rwa [hk_val] at h
  refine ⟨hB.left, hB.inf, fun a ha g => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L n w).2.1 a
  have hxJ : cLoc w x ∈ (iw w).J n := by
    have h : cLoc w (x * y) ∈ (iw w).J n :=
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ha.2 w) hw)
    rwa [map_mul, away_one hy, mul_one] at h
  have hxA : x ∈ lev U S iw := by
    have h := sec_mem_lev hP hS hw hxJ
    rwa [hsec x hx] at h
  have hyA : y ∈ lev U S iw ⊓ away n w :=
    ⟨by simpa using mul_mem (inv_mem hxA) ha, hy⟩
  rw [← mul_assoc, hB.level y hyA]
  have h := congrFun (hfix _ hxJ) g
  rw [← hsec x hx]
  exact h

private theorem op_comm {w w' : Plc L} (hw : IsSplitAt w) (hw' : IsSplitAt w')
    (hne : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (d : Fin n → (Kw w)ˣ) (d' : Fin n → (Kw w')ˣ) :
    Commute (op (V := V) w (iw w) d) (op (V := V) w' (iw w') d') := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  haveI : Finite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n)) :=
    finOrb w' _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n))
  simp only [op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype]
  refine Commute.sum_left _ _ _ fun q _ => Commute.sum_right _ _ _ fun q' _ => ?_
  have hc := (factor L n w).1 _ ((secSpec L n w hw).1 (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out) _
    ((factor L n w).2.2.1 w' hne ((secSpec L n w' hw').1 (q' : GL (Fin n) (Kw w') ⧸ (iw w').J n).out))
  show _ * _ = _ * _
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, hc]

private theorem op_unit {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) (hd : ∀ i, d i ∈ UpperTheory.V.Hi.Uo (Kw w))
    {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) : op w (iw w) d φ = φ := by
  have hmem : Sig.dg d ∈ (iw w).J n :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨d, fun i _ => hd i, rfl⟩))
  have hf : UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) (1 : GL (Fin n) (Kw w)) := finOrb w 1
  set ρ := (rightReg ℂ (UA L n) V).comp (secW n w) with hρ
  have e1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.2 (Sig.dg d) hmem 1 (one_mem _)
  have e2 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.1 {1}
    (fun y hy => by
      rw [Finset.mem_singleton.1 hy]
      exact MulAction.mem_orbit_self _)
    (fun q hq => by
      obtain ⟨a, rfl⟩ := hq
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
      exact (QuotientGroup.eq.2 (by simpa using a.2))) ⟨φ, fix_of_AF hP hS hw hφ⟩
  have e3 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ (Sig.dg d) (finOrb w _)).1 ⟨φ, fix_of_AF hP hS hw hφ⟩
  rw [mul_one, mul_one] at e1
  rw [e1, e2] at e3
  simpa using e3.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Sym.Al.afOps :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), U ≤ Kall L n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
        ∃ u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)),
          (∀ w ∈ S, ∀ d, AlgebraTools.Dom d → ∀ φ, ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ) ∧
          (∀ w ∈ S, ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → u w (d * d') = u w d * u w d') ∧
          (∀ w ∈ S, ∀ d, (∀ i, d i ∈ Hi.Uo (Kw w)) → u w d = 1) ∧
          ∀ w ∈ S, ∀ w' ∈ S, w ≠ w' → ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → Commute (u w d) (u w' d') := by
  intro L _ _ _ n V _ _ R U _ S hP hS
  classical
  let u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)) := fun w d =>
    if hw : w ∈ S then (op w (iw w) d).restrict (fun _ hφ => op_keep hP hS hw d hφ) else 0
  have hu : ∀ w, w ∈ S → ∀ d (φ : AF R (lev U S iw)),
      ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ := by
    intro w hw d φ
    simp only [u, dif_pos hw]
    rfl
  refine ⟨u, fun w hw d _ φ => hu w hw d φ, fun w hw d d' hd hd' => ?_, fun w hw d hd => ?_,
    fun w hw w' hw' hne d d' _ _ => ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw, Module.End.mul_apply, hu w hw, hu w hw]
    have h := congrArg Subtype.val (LinearMap.congr_fun
      ((Sig.hkMul (Kw w) (iw w) n (UA L n → V) ((rightReg ℂ (UA L n) V).comp (secW n w))).1 d d' hd hd')
      ⟨φ.1, fix_of_AF hP hS hw φ.2⟩)
    rw [Module.End.mul_apply, hk_val, hk_val, hk_val] at h
    exact h.symm
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw]
    exact op_unit hP hS hw d hd φ.2
  · have hne' : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := fun h =>
      hne (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h).symm
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hu w hw, hu w' hw', hu w' hw', hu w hw]
    exact LinearMap.congr_fun (op_comm (hP.split w (Finset.mem_coe.2 hw)) (hP.split w' (Finset.mem_coe.2 hw')) hne' d d') _
