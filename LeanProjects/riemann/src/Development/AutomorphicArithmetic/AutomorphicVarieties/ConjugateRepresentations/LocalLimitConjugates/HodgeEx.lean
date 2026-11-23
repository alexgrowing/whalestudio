import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.AppFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ResExact
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ExactLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem co_ext {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {α β : Co Ξ q} (h : ∀ X i, cmp i (α X) = cmp i (β X)) : α = β := by
  refine AlternatingMap.ext fun X => ?_
  rw [← sum_cmp (α X), ← sum_cmp (β X)]
  exact Finset.sum_congr rfl fun i _ => by rw [h X i]

private theorem app_zero' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    (T : Module.End ℂ (Sm E a)) : app T (0 : Co Ξ q) = 0 :=
  AlternatingMap.ext fun X => by
    rw [app_apply, AlternatingMap.zero_apply, map_zero]

private theorem hasLev_of {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : ∀ u ∈ U, act (.fin u) φ = φ) : HasLev φ := by
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun x => k⁻¹ * x) ⁻¹' U, fun x hx => ?_,
    hU.preimage (continuous_const.mul continuous_id), by simp⟩
  have e1 : finRep E a (k⁻¹ * x) φ = φ := h _ hx
  have e2 : finRep E a k φ = φ := hk
  change finRep E a x φ = φ
  have e3 : x = k * (k⁻¹ * x) := by simp
  rw [e3, map_mul, Module.End.mul_apply, e1, e2]

private theorem locLim_sub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim f φ) : LocLim (fun k => f k - φ) 0 := by
  intro C hC
  have := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at this ⊢
  intro ε hε
  filter_upwards [this ε hε] with k hk x hx
  have e := hk x hx
  change dist (0 : ℂ) ((f k).1 x - φ.1 x) < ε
  rwa [dist_comm, dist_zero_right, ← dist_eq_norm, dist_comm]

theorem UpperTheory.V.Cj.H.hodgeEx :
    UpperTheory.V.Cj.H.HodgeEx := by
  intro E _ _ _ a ha n e he U hUo hUc Ξ r hr q α hα hd hs
  obtain ⟨c, hc⟩ := casB E a n e he Ξ r
  obtain ⟨N, P, Q, S, hN, hR⟩ := fnProj E a ha r n e he c
  obtain ⟨l1, -, l3, l4⟩ := levLin E a U Ξ q
  have l2 := (levLin E a U Ξ q).2.1
  have sub_eq : ∀ {p : ℕ} (x y : Co Ξ p), x - y = (1 : ℂ) • x + (-1 : ℂ) • y := fun x y => by
    refine AlternatingMap.ext fun X => ?_
    change x X - y X = (1 : ℂ) • x X + (-1 : ℂ) • y X
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  have lsub : ∀ x y : Co Ξ q, IsLev U Ξ x → IsLev U Ξ y → IsLev U Ξ (x - y) := fun x y hx hy => by
    rw [sub_eq]; exact l1 x y _ _ hx hy
  have dsub : ∀ x y : Co Ξ q, dCo (smLie Ξ) x = 0 → dCo (smLie Ξ) y = 0 → dCo (smLie Ξ) (x - y) = 0 := fun x y hx hy => by
    rw [sub_eq, l2, hx, hy, smul_zero, smul_zero, add_zero]
  have hV : Val N α := fun X i => by
    obtain ⟨p1, p2, p3⟩ := l3 α hα X i
    obtain ⟨R, hR'⟩ := hs
    refine hN.cpt _ p1 (hasLev_of hUo p2) (p3 r hr) ⟨R, fun g hg => ?_⟩
    rw [Pf.cmp_ev, hR' X g hg]; rfl
  have key : ∀ T, IsOp N T → IsLev U Ξ (app T α) ∧ Val N (app T α) ∧ Val (sqSub E a r) (app T α) ∧
      dCo (smLie Ξ) (app T α) = 0 := fun T hT => by
    obtain ⟨p1, p2, p3, p4⟩ := appFacts E a U Ξ r hr N hN T hT q α hα hV
    exact ⟨p1, p2, p3, by rw [p4, hd, app_zero']⟩
  obtain ⟨h1, h2, h3, h4⟩ := key P hR.opP
  refine ⟨app P α, h1, h4, (resExact E a ha n e he U Ξ r c hc q _ h1 h4).2 h3 (co_ext fun X i => ?_), h3,
    fun X i => hN.grow _ (h2 X i), ?_⟩
  · rw [l4, l4, hR.ker _ (hV X i), AlternatingMap.zero_apply, map_zero]
  · refine exactLim E a ha U hUc Ξ q _ (fun k => app (Q k) α - app P α) (lsub _ _ hα h1) (dsub _ _ hd h4)
      (fun k => lsub _ _ (key _ (hR.opQ k)).1 h1) (fun k => dsub _ _ (key _ (hR.opQ k)).2.2.2 h4) (fun X i => ?_) fun k => ?_
    · have := locLim_sub (hR.lim _ (hV X i))
      simpa only [AlternatingMap.sub_apply, map_sub, l4] using this
    · obtain ⟨s1, -, -, s4⟩ := key _ (hR.opS k)
      have e1 : α - app P α - (app (Q k) α - app P α) = app (casA r c e) (app (S k) α) := by
        rw [sub_sub_sub_cancel_right]
        refine co_ext fun X i => ?_
        rw [AlternatingMap.sub_apply, map_sub, l4, l4, l4, hR.res k _ (hV X i)]
      rw [e1]
      exact (resExact E a ha n e he U Ξ r c hc q _ s1 s4).1
