import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem finsum_restrictedFamily_eq_prod_finsum : ∀ (V W : Type) [Fintype W] (C : V → Type) [∀ v, One (C v)] (X : ∀ v, Set (C v)) (Y : W → Type) [∀ w, Finite (Y w)], (∀ v, (X v).Finite) → ∀ (o : ∀ v, X v → ℂ) (oa : ∀ w, Y w → ℂ), (∀ᶠ v in cofinite, (1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) → (Function.support fun p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1} => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)).Finite ∧ ∑ᶠ p : {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}, (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = (∏ᶠ v, ∑ᶠ q : X v, o v q) * ∏ w, ∑ᶠ q : Y w, oa w q := by
  intro V W _ C _ X Y _ hX o oa hev
  classical
  have hfin := Filter.eventually_cofinite.1 hev
  set S : Finset V := hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → ((1 : C v) ∈ X v ∧ ∀ q : X v, (q.1 = 1 → o v q = 1) ∧ (q.1 ≠ 1 → o v q = 0)) := by
    intro v hv
    by_contra h
    exact hv (by simpa [hSdef] using h)
  haveI : ∀ v, Fintype (X v) := fun v => (hX v).fintype
  haveI : ∀ w, Fintype (Y w) := fun w => Fintype.ofFinite _
  let Sub := {p : (∀ v, X v) × (∀ w, Y w) // ∀ᶠ v in cofinite, (p.1 v).1 = 1}
  let F : Sub → ℂ := fun p => (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w)
  let emb : (∀ v : S, X v) × (∀ w, Y w) → Sub := fun t =>
    ⟨(fun v => if h : v ∈ S then t.1 ⟨v, h⟩ else ⟨1, (hS v h).1⟩, t.2), by
      refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      simp [dif_neg (show v ∉ S from h)] at hv⟩
  have hmul : ∀ p : Sub, (Function.mulSupport fun v => o v (p.1.1 v)).Finite := by
    intro p
    refine (S.finite_toSet.union (Filter.eventually_cofinite.1 p.2)).subset ?_
    intro v hv
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    exact hv (((hS v h.1).2 _).1 h.2)
  have hsupp : Function.support F ⊆ Set.range emb := by
    intro p hp
    have h1 : ∀ v, v ∉ S → (p.1.1 v).1 = 1 := by
      intro v hv
      by_contra hne
      apply hp
      show (∏ᶠ v, o v (p.1.1 v)) * ∏ w, oa w (p.1.2 w) = 0
      rw [finprod_eq_zero _ v (((hS v hv).2 _).2 hne) (hmul p), zero_mul]
    refine ⟨(fun v => p.1.1 v, p.1.2), ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · funext v
      by_cases hv : v ∈ S
      · simp only [emb, dif_pos hv]
      · simp only [emb, dif_neg hv]
        exact Subtype.ext (h1 v hv).symm
    · rfl
  have hinj : Function.Injective emb := by
    intro t t' h
    have h' := congrArg (fun p : Sub => p.1) h
    simp only [emb, Prod.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    refine Prod.ext (funext fun v => ?_) h2
    have := congrFun h1 v.1
    simpa only [dif_pos v.2] using this
  have hval : ∀ t, F (emb t) = (∏ v : S, o v (t.1 v)) * ∏ w, oa w (t.2 w) := by
    intro t
    show (∏ᶠ v, o v ((emb t).1.1 v)) * ∏ w, oa w (t.2 w) = _
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      simp only [emb, dif_pos v.2]
    · intro v hv
      by_contra h
      apply hv
      simp only [emb, dif_neg (show v ∉ S from h)]
      exact ((hS v h).2 _).1 rfl
  have hsupp' : Function.support F ⊆ ↑(Finset.univ.image emb) := by
    intro p hp
    obtain ⟨t, rfl⟩ := hsupp hp
    simp
  refine ⟨(Finset.univ.image emb).finite_toSet.subset hsupp', ?_⟩
  show ∑ᶠ p, F p = _
  rw [finsum_eq_sum_of_support_subset _ hsupp', Finset.sum_image (fun a _ b _ h => hinj h)]
  simp only [hval]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Fintype.sum_mul_sum, ← Fintype.prod_sum, ← Fintype.prod_sum]
  congr 1
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [finsum_eq_sum_of_fintype]
    · intro v hv
      by_contra h
      apply hv
      show ∑ᶠ q : X v, o v q = 1
      rw [finsum_eq_single _ ⟨1, (hS v h).1⟩]
      · exact ((hS v h).2 _).1 rfl
      · intro q hq
        exact ((hS v h).2 q).2 (fun e => hq (Subtype.ext e))
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [finsum_eq_sum_of_fintype]

end GlobalTheory.TrEll
