import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AddIff
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EvalExact

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private lemma sec_nat {P : C ⥤ Type} {K : Coef C} (c : Sec P K) {A B : C} (φ : A ⟶ B)
    (y : P.obj A) : (K.map φ).hom (c.1 A y) = c.1 B (P.map φ y) :=
  c.2 φ y

private lemma sum_transport {Q : C ⥤ Type} {K : Coef C} (c : Sec Q K) {I : Type} [Fintype I]
    (g : I → (Q ⟶ Q)) {A B : C} (φ : A ⟶ B) (w : Q.obj A) :
    (K.map φ).hom (∑ i, c.1 A ((g i).app A w)) =
      ((Finset.univ.val.map fun i => (g i).app B (Q.map φ w)).map (c.1 B)).sum := by
  rw [map_sum, Multiset.map_map]
  change _ = ∑ i, c.1 B ((g i).app B (Q.map φ w))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sec_nat c φ, FunctorToTypes.naturality]

private lemma avg_indep (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) {A : C}
    {w w' : Q.obj A} (hw : p.app A w = p.app A w') :
    ∑ i, c.1 A ((g i).app A w) = ∑ i, c.1 A ((g i).app A w') := by
  obtain ⟨S, hS, hm⟩ := h.2.2 A w w' hw
  apply (hK A S hS).1
  funext s
  change (K.map (S.f s)).hom _ = (K.map (S.f s)).hom _
  rw [sum_transport, sum_transport, hm s]

private def lift (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) : Q.obj A :=
  Classical.choose ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private lemma lift_spec (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) :
    p.app A (lift Pa h A y) = y :=
  Classical.choose_spec ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private def avg (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) : Sec P K :=
  ⟨fun A y => ∑ i, c.1 A ((g i).app A (lift Pa h A y)), by
    intro A B φ y
    have hw : p.app B (Q.map φ (lift Pa h A y)) = p.app B (lift Pa h B (P.map φ y)) := by
      rw [lift_spec, FunctorToTypes.naturality, lift_spec]
    change (K.map φ).hom (∑ i, c.1 A ((g i).app A (lift Pa h A y))) =
      ∑ i, c.1 B ((g i).app B (lift Pa h B (P.map φ y)))
    rw [← avg_indep Pa hK h c hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_nat c φ, FunctorToTypes.naturality]⟩

private lemma avg_apply (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) (A : C)
    (y : P.obj A) :
    (avg Pa hK h c).1 A y = ∑ i, c.1 A ((g i).app A (lift Pa h A y)) := rfl

private lemma avg_pull (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (s : Sec P K) (c : Sec Q K)
    (hc : ∀ (A : C) (q : Q.obj A), c.1 A q = s.1 A (p.app A q)) :
    avg Pa hK h c = Fintype.card I • s := by
  apply Subtype.ext
  funext A y
  have hg : ∀ (i : I) (w : Q.obj A), p.app A ((g i).app A w) = p.app A w := fun i w => by
    have hgi : g i ≫ p = p := (show ∀ i, g i ≫ p = p from h.1) i
    have : (g i ≫ p).app A w = p.app A w := by rw [hgi]
    exact this
  rw [avg_apply]
  simp only [hc, hg, lift_spec]
  simp

private lemma avg_map (Pa : Parts C) {K L : Coef C} (hK : Pa.Add K) (hL : Pa.Add L)
    {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g)
    (α : K ⟶ L) (c : Sec Q K) (c' : Sec Q L)
    (hc : ∀ (A : C) (q : Q.obj A), c'.1 A q = (α.app A).hom (c.1 A q)) (A : C) (y : P.obj A) :
    (avg Pa hL h c').1 A y = (α.app A).hom ((avg Pa hK h c).1 A y) := by
  rw [avg_apply, avg_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hc _ _

private lemma zero_case (Pa : Parts C) (T : Theory C) {K L : Coef C} (hK : Pa.Add K)
    (hL : Pa.Add L) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)}
    (h : Pa.LocTrans p g) (π : K ⟶ L) (x' : T.H P L 0) (k : T.H Q K 0)
    (hk : T.map Q π 0 k = T.pull p L 0 x') :
    Fintype.card I • x' ∈ Set.range (T.map P π 0) := by
  refine ⟨(T.zero P K).symm (avg Pa hK h (T.zero Q K k)), ?_⟩
  apply (T.zero P L).injective
  apply Subtype.ext
  funext A y
  have e1 : avg Pa hL h (T.zero Q L (T.pull p L 0 x')) = Fintype.card I • T.zero P L x' :=
    avg_pull Pa hL h _ _ fun A q => T.zero_pull p L x' A q
  have e2 := avg_map Pa hK hL h π (T.zero Q K k) (T.zero Q L (T.map Q π 0 k))
    (fun A q => T.zero_map Q π k A q) A y
  rw [T.zero_map, map_nsmul, ← e1, ← hk, e2, AddEquiv.apply_symm_apply]

private lemma step (Pa : Parts C) (T : Theory C) {Q P : C ⥤ Type} (p : Q ⟶ P) (n : ℕ)
    (S : ShortComplex (Coef C)) (hS : S.ShortExact) (hK : Injective S.X₂) (j : ℕ)
    (hr : ∀ (x' : T.H P S.X₃ j) (k : T.H Q S.X₂ j), T.map Q S.g j k = T.pull p S.X₃ j x' →
      n • x' ∈ Set.range (T.map P S.g j))
    (x : T.H P S.X₁ (j + 1)) (hx : T.pull p S.X₁ (j + 1) x = 0) : n • x = 0 := by
  have h0 : T.map P S.f (j + 1) x = 0 := (T.inj P S.X₂ hK j).elim _ _
  obtain ⟨x', rfl⟩ := (T.ex₁ P S hS j x).1 h0
  have hpull : T.δ Q S hS j (T.pull p S.X₃ j x') = 0 := by
    rw [← T.pull_δ]
    exact hx
  obtain ⟨k, hk⟩ := (T.ex₃ Q S hS j _).1 hpull
  obtain ⟨k', hk'⟩ := hr x' k hk
  rw [← map_nsmul, ← hk']
  exact (T.ex₃ P S hS j _).2 ⟨k', rfl⟩

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.locAvg :
    UpperTheory.Ru.crystallineComparison.LocAvg := by
  intro C _ Pa T F hF Q P p I _ g h j
  induction j generalizing F with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by
      apply (T.zero P F).injective
      rw [map_zero]
      apply Subtype.ext
      funext A y
      obtain ⟨w, rfl⟩ := h.2.1 A y
      rw [← T.zero_pull p F x A w, hx, map_zero]
      rfl
    rw [hx0, smul_zero]
  | succ j ih =>
    intro x hx
    obtain ⟨K, ι, hm, hi, hK⟩ := emb C Pa F hF
    have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstance }
    have hL : Pa.Add (cokernel ι) := quotAdd C Pa _ hS hF hK
    refine step Pa T p _ _ hS hi j ?_ x hx
    intro x' k hk
    cases j with
    | zero =>
      exact zero_case Pa T hK hL h _ x' k hk
    | succ j =>
      have hk0 : k = 0 := (T.inj Q K hi j).elim _ _
      rw [hk0, map_zero] at hk
      exact ⟨0, by rw [map_zero, ih _ hL x' hk.symm]⟩
