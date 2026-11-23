import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityLatticeDescendsIntegralExt

set_option autoImplicit false

noncomputable section

open GlobalTheory.RingChain GlobalTheory.PerfdLat
open scoped TensorProduct Pointwise

namespace GlobalTheory.RingChain

theorem exists_presentation_equiv {A X : Type} [CommRing A] [AddCommGroup X] [Module A X] (P Q : Submodule A X) {m r : ℕ}
    (u : Fin m → P) (R : Matrix (Fin m) (Fin r) A) (hs : ∀ p : P, ∃ x : Fin m → A, ∑ i, x i • u i = p)
    (hk : ∀ x : Fin m → A, ((∑ i, x i • u i : P) : X) ∈ Q ↔ ∃ c, R.mulVec c = x) :
    ∃ e : ((Fin m → A) ⧸ LinearMap.range (Matrix.mulVecLin R)) ≃ₗ[A] Qt P Q,
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (∑ i, x i • u i) := by
  let F : (Fin m → A) →ₗ[A] Qt P Q := (Q.comap P.subtype).mkQ ∘ₗ Fintype.linearCombination A u
  have hF : ∀ x, F x = Submodule.Quotient.mk (∑ i, x i • u i) := fun _ => rfl
  have surj : Function.Surjective F := fun y => by
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, rfl⟩ := hs p
    exact ⟨x, rfl⟩
  have ker : LinearMap.range (Matrix.mulVecLin R) = LinearMap.ker F := by
    ext x
    rw [LinearMap.mem_ker, hF, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, LinearMap.mem_range]
    exact (hk x).symm
  exact ⟨(Submodule.quotEquivOfEq _ _ ker).trans (F.quotKerEquivOfSurjective surj), fun x => rfl⟩

theorem functional_mem_range {A' B : Type} [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B] [IsDomain B]
    (g : A' →+* B) (hi : Function.Injective g) (hg : g.IsIntegral) {h : ℕ} {ϖ : B} (h0 : ϖ ≠ 0) (hϖ : ϖ ∈ Set.range g)
    (P : Submodule B (Fin h → B)) (b : Fin h → P) (hb : ∀ k, (b k).1 = ϖ • Pi.single k 1) (f : P →ₗ[B] B)
    (hf : ∀ k, f (b k) ∈ Set.range g) (y : P) (y' : Fin h → A') (hy : piMap g (Fin h) y' = y.1) : f y ∈ Set.range g := by
  obtain ⟨a, rfl⟩ := hϖ
  choose z hz using hf
  have ha : a ≠ 0 := fun e => h0 (by rw [e, map_zero])
  have h1 : g a • y = ∑ k, g (y' k) • b k := Subtype.ext (funext fun j => by
    rw [Submodule.coe_smul, ← hy, Submodule.coe_sum, Finset.sum_apply]
    simp [hb, Pi.single_apply, mul_comm])
  have h2 : g (∑ k, y' k * z k) = g a * f y := by
    rw [← smul_eq_mul, ← map_smul, h1, map_sum, map_sum]
    simp [hz]
  obtain ⟨w, hw⟩ := (dvd_descends_of_isIntegral A' B g hi hg).1 a _ ha ⟨_, h2⟩
  rw [hw, map_mul] at h2
  exact ⟨w, mul_left_cancel₀ h0 h2⟩

theorem exists_presentation_descends (B : Type) [CommRing B] [IsDomain B] (h : ℕ) (ϖ : B) (P Q : Submodule B (Fin h → B))
    [Module.Finite B P] [Module.Projective B P] [Module.Finite B Q] [Module.Projective B Q] (h0 : ϖ ≠ 0)
    (hQ : baseOf ϖ h ≤ Q) (hQP : Q ≤ P) :
    ∃ (m₁ r₁ : ℕ) (u : Fin m₁ → P) (R₁ : Matrix (Fin m₁) (Fin r₁) B)
      (e : ((Fin m₁ → B) ⧸ LinearMap.range (Matrix.mulVecLin R₁)) ≃ₗ[B] Qt P Q) (T : Set B),
      (∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (∑ i, x i • u i)) ∧ T.Finite ∧
      ∀ (A' : Type) [CommRing A'] [IsDomain A'] [IsIntegrallyClosed A'] (g : A' →+* B), Function.Injective g →
        g.IsIntegral → T ⊆ Set.range g → ∀ P' Q' : Submodule A' (Fin h → A'), (∀ x, x ∈ P' ↔ piMap g (Fin h) x ∈ P) →
        (∀ x, x ∈ Q' ↔ piMap g (Fin h) x ∈ Q) →
        ∃ (u' : Fin m₁ → P') (R₁' : Matrix (Fin m₁) (Fin r₁) A')
          (e' : ((Fin m₁ → A') ⧸ LinearMap.range (Matrix.mulVecLin R₁')) ≃ₗ[A'] Qt P' Q'),
          (∀ i, piMap g (Fin h) (u' i).1 = (u i).1) ∧ R₁'.map g = R₁ ∧
          ∀ x, e' (Submodule.Quotient.mk x) = Submodule.Quotient.mk (∑ i, x i • u' i) := by
  obtain ⟨m, f, s, -, -, hfs⟩ := Module.Finite.exists_comp_eq_id_of_projective B P
  obtain ⟨n, f', s', -, -, hfs'⟩ := Module.Finite.exists_comp_eq_id_of_projective B Q
  have e1 : ∀ p, f (s p) = p := fun p => LinearMap.congr_fun hfs p
  have e2 : ∀ p, f' (s' p) = p := fun p => LinearMap.congr_fun hfs' p
  obtain ⟨u, hu⟩ : ∃ u : Fin m → P, ∀ x, ∑ i, x i • u i = f x :=
    ⟨fun i => f (Pi.single i 1), fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ f x]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      exact congrArg f (funext fun j => by simp [Pi.single_apply, eq_comm])⟩
  obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin m) (Fin (m + n)) B, ∀ a c, R.mulVec (Sum.elim a c ∘ finSumFinEquiv.symm) =
      a - s (f a) + s (Submodule.inclusion hQP (f' c)) :=
    ⟨(Matrix.fromCols (LinearMap.toMatrix' (LinearMap.id - s ∘ₗ f))
      (LinearMap.toMatrix' (s ∘ₗ Submodule.inclusion hQP ∘ₗ f'))).submatrix id finSumFinEquiv.symm, fun a c => by
        rw [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.symm_symm, Equiv.symm_comp_self, Function.comp_id,
          Function.comp_id, Matrix.fromCols_mulVec_sumElim, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
        rfl⟩
  have k1 : ∀ x (hx : (f x).1 ∈ Q), R.mulVec (Sum.elim x (s' ⟨_, hx⟩) ∘ finSumFinEquiv.symm) = x := fun x hx => by
    rw [hR, e2]
    exact sub_add_cancel _ _
  have k2 : ∀ c, (f (R.mulVec c)).1 ∈ Q := fun c => by
    have : c = Sum.elim (c ∘ finSumFinEquiv ∘ Sum.inl) (c ∘ finSumFinEquiv ∘ Sum.inr) ∘ finSumFinEquiv.symm := by
      ext j
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
      rw [Function.comp_apply, Equiv.symm_apply_apply]
      cases j <;> rfl
    rw [this, hR, map_add, map_sub, e1, e1, sub_self, zero_add]
    exact (f' _).2
  obtain ⟨e, he⟩ := exists_presentation_equiv P Q u R (fun p => ⟨s p, by rw [hu, e1]⟩) fun x => by
    rw [hu]
    exact ⟨fun hx => ⟨_, k1 x hx⟩, fun ⟨c, hc⟩ => hc ▸ k2 c⟩
  let b : Fin h → Q := fun k => ⟨ϖ • Pi.single k 1, hQ (Submodule.smul_mem_pointwise_smul _ _ _ trivial)⟩
  refine ⟨m, m + n, u, R, e, {ϖ} ∪ Set.range (fun ij : Fin m × Fin h => (u ij.1).1 ij.2) ∪
    Set.range (fun ij : Fin m × Fin (m + n) => R ij.1 ij.2) ∪
    Set.range (fun ij : Fin m × Fin h => s (Submodule.inclusion hQP (b ij.2)) ij.1) ∪
    Set.range (fun ij : Fin n × Fin h => s' (b ij.2) ij.1), he, ?_, ?_⟩
  · exact ((((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_range _)
  intro A' _ _ _ g hi hg hT P' Q' hP' hQ'
  simp only [Set.union_subset_iff, Set.singleton_subset_iff, Set.range_subset_iff, Prod.forall] at hT
  obtain ⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩ := hT
  choose v hv using t2
  choose R' hR' using t3
  have hv' : ∀ i, piMap g (Fin h) (v i) = (u i).1 := fun i => funext (hv i)
  let u' : Fin m → P' := fun i => ⟨v i, (hP' _).2 (hv' i ▸ (u i).2)⟩
  have hRm : (Matrix.of R').map g = R := by ext i j; exact hR' i j
  have hsum : ∀ x : Fin m → A', piMap g (Fin h) (∑ i, x i • u' i : P').1 = (f (g ∘ x)).1 := fun x => by
    rw [← hu, Submodule.coe_sum, Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Submodule.coe_smul, map_smulₛₗ, hv']
    rfl
  have hmv : ∀ c, g ∘ (Matrix.of R').mulVec c = R.mulVec (g ∘ c) := fun c => by
    ext i
    rw [← hRm, Function.comp_apply, RingHom.map_mulVec]
  obtain ⟨e', he'⟩ := exists_presentation_equiv P' Q' u' (Matrix.of R') (fun p => by
    have := fun i => functional_mem_range g hi hg h0 t1 P (fun k => Submodule.inclusion hQP (b k)) (fun _ => rfl)
      (LinearMap.proj i ∘ₗ s) (t4 i) ⟨_, (hP' _).1 p.2⟩ p.1 rfl
    choose x hx using this
    refine ⟨x, Subtype.ext (funext fun j => hi ?_)⟩
    have h3 : g ∘ x = s ⟨_, (hP' _).1 p.2⟩ := funext hx
    have h4 := hsum x
    rw [h3, e1] at h4
    exact congrFun h4 j) fun x => by
    rw [hQ', hsum]
    refine ⟨fun hx => ?_, fun ⟨c, hc⟩ => by rw [← hc, hmv]; exact k2 _⟩
    have := fun i => functional_mem_range g hi hg h0 t1 Q b (fun _ => rfl)
      (LinearMap.proj i ∘ₗ s') (t5 i) ⟨_, hx⟩ _ (hsum x)
    choose c hc using this
    refine ⟨Sum.elim x c ∘ finSumFinEquiv.symm, funext fun j => hi ?_⟩
    have h3 : g ∘ c = s' ⟨_, hx⟩ := funext hc
    have h4 := hmv (Sum.elim x c ∘ finSumFinEquiv.symm)
    rw [← Function.comp_assoc g, Sum.comp_elim, h3, k1] at h4
    exact congrFun h4 j
  exact ⟨u', Matrix.of R', e', hv', hRm, he'⟩

end GlobalTheory.RingChain

end
