import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschOfLocalCoverOfInf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.DividedPowerChartLift

private theorem iso_incl (E : Spc) {a : Act} (Q : Pred a) (h : ∀ A x, Q.P A x) : IsIso (Sp.map E (incl Q)) := by
  refine UpperTheory.isIso_stackProductMap_of_bijective E (incl Q) (fun A => ⟨?_, ?_⟩) (fun _ => Function.bijective_id)
  · intro x y hxy
    exact Subtype.ext hxy
  · intro y
    exact ⟨⟨y, h A y⟩, rfl⟩

private theorem le_unit {N : ℕ} (i : Fin N) {Q : Pred (XC N)} (h : Q.Le (spanOn ((({i} : Finset (Fin N))) : Set (Fin N)))) :
    Q.Le (unitAt i) := by
  intro A x hx
  have h1 := h A x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_singleton, Set.image_singleton] at h1
  exact Ideal.span_singleton_eq_top.mp h1

private theorem loc_step {N : ℕ} (i : Fin N) (F' : Finset (Fin N)) (hi : i ∉ F') (Q : Pred (XC N))
    (hQ : Q.Le (spanOn ((Finset.cons i F' hi : Finset (Fin N)) : Set (Fin N))))
    (T : Scheme.{0}) (x : (XC N).D.obj Γ(T, ⊤)) (hx : Q.P _ x) :
    Loc T fun V g => (Q.inf (spanOn (F' : Set (Fin N)))).P _ ((XC N).D.map g.appTop x) ∨
      (Q.inf (unitAt i)).P _ ((XC N).D.map g.appTop x) := by
  have hs := hQ _ x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_cons, Set.image_insert_eq] at hs
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert] at hs
  obtain ⟨a, s, hsF, h1⟩ := hs
  let w : Fin 2 → Γ(T, ⊤) := ![x.1 i, s]
  have hw : Ideal.span (Set.range w) = ⊤ := by
    rw [Ideal.eq_top_iff_one, h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ a (Ideal.subset_span ⟨0, rfl⟩)) (Ideal.subset_span ⟨1, rfl⟩)
  obtain ⟨S, hS, hSP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T w hw
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨k, hk⟩ := hSP V g hg
  have hQx : Q.P _ ((XC N).D.map g.appTop x) := Q.map _ _ hx
  fin_cases k
  · right
    exact ⟨hQx, hk⟩
  · left
    refine ⟨hQx, ?_⟩
    apply Ideal.eq_top_of_isUnit_mem _ _ hk
    have hm := Ideal.mem_map_of_mem g.appTop.hom hsF
    rw [Ideal.map_span, ← Set.image_comp] at hm
    exact hm

private theorem all_of_units (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (hE : Inv q E) {c : Act} (π : Act.Hom c (XC N)) {m : ℕ}
    (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
    (H : ∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q)
    {F : Finset (Fin N)} (hF : F.Nonempty) :
    ∀ Q : Pred (XC N), Q.Le (spanOn (F : Set (Fin N))) → LHQ q E π d e cl Q := by
  induction hF using Finset.Nonempty.cons_induction with
  | singleton j =>
    intro Q hQ
    exact H j Q (le_unit j hQ)
  | cons j F' hj hF' ih =>
    intro Q hQ
    refine UpperTheory.leraHirsch_of_local_cover_of_inf q E hE π d e cl Q (Q.inf (spanOn (F' : Set (Fin N)))) (Q.inf (unitAt j))
      (fun A x hx => hx.1) (fun A x hx => hx.1) ?_ ?_ ?_ ?_
    · intro T x hx
      exact loc_step j F' hj Q hQ T x hx
    · exact ih _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2.2)

end UpperTheory.DividedPowerChartLift

theorem UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), 1 ≤ N → Inv q E → ∀ {c : Act} (π : Act.Hom c (XC N)) {m : ℕ} (d e : Fin m → ℤ)
        (cl : ∀ j, Ht q (Sp E c) (d j) (e j)), (∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q) → LH q (Sp.map E π) d e cl := by
  intro q _ N E hN hE c π m d e cl H
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  have hT := UpperTheory.DividedPowerChartLift.all_of_units q N E hE π d e cl H hne (Pred.top _) (fun A x _ => by
    show Ideal.span _ = ⊤
    rw [Finset.coe_univ, Set.image_univ]
    exact x.2)
  have hsq : Sp.map E (π.sub (Pred.top _)) ≫ Sp.map E (incl (Pred.top (XC N))) =
      Sp.map E (incl (Pred.comap π (Pred.top _))) ≫ Sp.map E π := rfl
  haveI : IsIso (Sp.map E (incl (Pred.comap π (Pred.top (XC N))))) :=
    UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  haveI : IsIso (Sp.map E (incl (Pred.top (XC N)))) := UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  have h2 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub (Pred.top _))) (Sp.map E π)
    (inv (Sp.map E (incl (Pred.comap π (Pred.top (XC N)))))) (inv (Sp.map E (incl (Pred.top (XC N)))))
    (by rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, hsq]) d e _ hT
  convert h2 using 1
  funext j
  rw [← GlobalTheory.EtC.pull_comp, IsIso.inv_hom_id, GlobalTheory.EtC.pull_id]
