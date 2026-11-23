import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorTestFamilyPreservesLevelForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexProd
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.HSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_cLoc_val (hE : Unr E) (w : Pl E) (x : finU E n) :
    ((toSub (UL n w) (cLoc w (x : UA E n)) : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  unfold toSub
  rw [dif_pos (cLoc_mem_UL E hE n w x)]

theorem factor_ne_zero (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (hK : ∀ᶠ w in cofinite, K' w = KL n w)
    (f : ∀ w : Pl E, UL n w → ℂ) (hf : ∀ᶠ w in cofinite, f w = (KL n w : Set (UL n w)).indicator 1)
    (x : finU E n) (hx : globFn S f x ≠ 0) :
    ∀ w ∈ S, f w (toSub (UL n w) (cLoc w (x : UA E n))) ≠ 0 := by
  set g : Pl E → ℂ := fun w => f w (toSub (UL n w) (cLoc w (x : UA E n))) with hg
  have hB : {w | ¬ (f w = (KL n w : Set (UL n w)).indicator 1 ∧
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ KL n w)}.Finite :=
    Filter.eventually_cofinite.1 (hf.and (RegVan.eventually_toSub_mem (n := n) x))
  have hfin : (S ∩ Function.mulSupport g).Finite := by
    refine hB.subset fun w hw => ?_
    intro hc
    apply hw.2
    change f w _ = 1
    rw [hc.1]
    exact Set.indicator_of_mem hc.2 _
  intro w hwS
  by_cases hm : w ∈ Function.mulSupport g
  · have hx' : ∏ᶠ w ∈ S, g w ≠ 0 := hx
    rw [← finprod_mem_inter_mulSupport, finprod_mem_eq_finite_toFinset_prod _ hfin] at hx'
    exact Finset.prod_ne_zero_iff.1 hx' w (hfin.mem_toFinset.2 ⟨hwS, hm⟩)
  · rw [Function.notMem_mulSupport] at hm
    change g w ≠ 0
    rw [hm]
    exact one_ne_zero

end GlobalTheory.BCT.HSupp

open GlobalTheory.BCT.HSupp in

theorem GlobalTheory.BCT.finite_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → {q : finU E n ⧸ globLev S K' | globFn S f q.out ≠ 0}.Finite := by
  intro E _ _ _ hE n S K' hK f hf
  set F : Set (Pl E) := {w | ¬ (K' w = KL n w ∧ f w = (KL n w : Set (UL n w)).indicator 1)} with hF
  have hFfin : F.Finite := Filter.eventually_cofinite.1 (hK.2.and hf.2)
  have key := factor_ne_zero S K' hK.2 f hf.2
  have inK : ∀ x : finU E n, globFn S f x ≠ 0 → ∀ w ∈ S, w ∉ F →
      toSub (UL n w) (cLoc w (x : UA E n)) ∈ K' w := by
    intro x hx w hwS hwF
    simp only [hF, Set.mem_setOf_eq, not_not] at hwF
    have h := key x hx w hwS
    rw [hwF.2] at h
    rw [hwF.1]
    by_contra hc
    exact h (Set.indicator_of_notMem hc _)
  haveI : Finite ↥(F ∩ S) := (hFfin.inter_of_left S).to_subtype
  let Φ : finU E n ⧸ globLev S K' → ∀ w : ↥(F ∩ S), UL n w.1 ⧸ K' w.1 := fun q w =>
    (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)) : UL n w.1 ⧸ K' w.1)
  refine Set.Finite.of_injOn (f := Φ)
    (t := Set.pi Set.univ fun w : ↥(F ∩ S) => {c : UL n w.1 ⧸ K' w.1 | f w.1 c.out ≠ 0}) ?_ ?_
    (Set.Finite.pi fun w => LevOpTmul.finite_supp (hK.1 w.1).1 (hf.1 w.1).1)
  · intro q hq w _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K' w.1) (toSub (UL n w.1) (cLoc w.1 (q.out : UA E n)))
    change f w.1 (QuotientGroup.mk _ : UL n w.1 ⧸ K' w.1).out ≠ 0
    rw [hh, ((hf.1 w.1).2 h h.2 _).2]
    exact key _ hq w.1 w.2.2
  · intro q₁ hq₁ q₂ hq₂ he
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    refine QuotientGroup.eq.2 ((mem_globLev_iff S K' _).2 fun w hwS => ?_)
    refine ⟨(toSub (UL n w) (cLoc w (q₁.out : UA E n)))⁻¹ * toSub (UL n w) (cLoc w (q₂.out : UA E n)), ?_, ?_⟩
    · by_cases hwF : w ∈ F
      · have := congrFun he ⟨w, hwF, hwS⟩
        exact QuotientGroup.eq.1 this
      · exact mul_mem (inv_mem (inK _ hq₁ w hwS hwF)) (inK _ hq₂ w hwS hwF)
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, toSub_cLoc_val hE, toSub_cLoc_val hE, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv]
