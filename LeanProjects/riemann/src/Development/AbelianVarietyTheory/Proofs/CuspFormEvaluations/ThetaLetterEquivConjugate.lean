import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortHarmonicFamilyLinear
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

open MvPolynomial NumberField

namespace GlobalTheory.Harm

section Abstract

variable {ι : Type} {σ : ι → ι} {Ψ : ι → Prop} {dim : ι → ℕ} {p q : ℕ}
  (hσ : Function.Involutive σ) (hΨ : ∀ τ, ¬ Ψ τ ↔ Ψ (σ τ))
  (hp : ∀ τ, Ψ τ → dim τ = p) (hq : ∀ τ, Ψ τ → dim (σ τ) = q) (n : ℕ)

theorem halfRowEquiv_of_mem {τ : ι} (h : Ψ τ) (i : Fin (dim τ)) :
    halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = (⟨τ, h⟩, Sum.inl (i.cast (hp _ h))) := by
  unfold halfRowEquiv
  simp only [Equiv.coe_fn_mk, dif_pos h]

theorem halfRowEquiv_invol {τ : ι} (h : Ψ τ) (i : Fin (dim (σ τ))) :
    halfRowEquiv hσ hΨ hp hq ⟨σ τ, i⟩ = (⟨τ, h⟩, Sum.inr (i.cast (hq _ h))) := by
  have hn : ¬ Ψ (σ τ) := fun h' => (hΨ τ).2 h' h
  unfold halfRowEquiv
  simp only [Equiv.coe_fn_mk, dif_neg hn]
  exact Prod.ext (Subtype.ext (hσ τ)) rfl

noncomputable def typeLetterEquiv : Formalism.L2.Pj.Letter ι dim n ≃ Var {τ // Ψ τ} p q (Fin n) :=
  ((⟨fun x => (⟨x.1, x.2.1⟩, x.2.2), fun y => ⟨y.1.1, y.1.2, y.2⟩, fun _ => rfl, fun _ => rfl⟩ :
    Formalism.L2.Pj.Letter ι dim n ≃ (Σ τ : ι, Fin (dim τ)) × Fin n).trans
    ((halfRowEquiv hσ hΨ hp hq).prodCongr (Equiv.refl _))).trans (Equiv.prodAssoc _ _ _)

variable {n}

theorem typeLetterEquiv_apply {τ : ι} {i : Fin (dim τ)} {t : {τ // Ψ τ}} {r : Fin p ⊕ Fin q}
    (h : halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = (t, r)) (b : Fin n) :
    typeLetterEquiv hσ hΨ hp hq n ⟨τ, i, b⟩ = (t, r, b) := by
  show Equiv.prodAssoc _ _ _ (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩, b) = (t, r, b)
  rw [h]
  rfl

include hσ hΨ in

theorem half_cases (τ : ι) : Ψ τ ∨ ∃ τ', Ψ τ' ∧ τ = σ τ' := by
  by_cases h : Ψ τ
  · exact Or.inl h
  · exact Or.inr ⟨σ τ, (hΨ τ).1 h, (hσ τ).symm⟩

variable {K : Type} [Field K]

theorem rename_lap_one {τ : ι} (h : Ψ τ) (i : Fin (dim τ)) (j : Fin (dim (σ τ)))
    (P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K) :
    rename (typeLetterEquiv hσ hΨ hp hq n) (Formalism.L2.Pj.lap dim n K 1 τ (σ τ) i j P) =
      laplacian ⟨τ, h⟩ (i.cast (hp _ h)) (j.cast (hq _ h))
        (rename (typeLetterEquiv hσ hΨ hp hq n) P) := by
  have ex : ∀ b, typeLetterEquiv hσ hΨ hp hq n ⟨τ, i, b⟩ = xVar ⟨τ, h⟩ (i.cast (hp _ h)) b :=
    fun b => typeLetterEquiv_apply hσ hΨ hp hq (halfRowEquiv_of_mem hσ hΨ hp hq h i) b
  have ey : ∀ b, typeLetterEquiv hσ hΨ hp hq n ⟨σ τ, j, b⟩ = yVar ⟨τ, h⟩ (j.cast (hq _ h)) b :=
    fun b => typeLetterEquiv_apply hσ hΨ hp hq (halfRowEquiv_invol hσ hΨ hp hq h j) b
  rw [laplacian_apply]
  simp only [Formalism.L2.Pj.lap, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, Derivation.coeFn_coe, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← ex b, ← ey b, pderiv_rename (typeLetterEquiv hσ hΨ hp hq n).injective,
    pderiv_rename (typeLetterEquiv hσ hΨ hp hq n).injective]

theorem rename_rowShift {τ : ι} {i i' : Fin (dim τ)} {t : {τ // Ψ τ}} {r r' : Fin p ⊕ Fin q}
    (h : halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = (t, r')) (h' : halfRowEquiv hσ hΨ hp hq ⟨τ, i'⟩ = (t, r))
    (s : K) (P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K) :
    rename (typeLetterEquiv hσ hΨ hp hq n) (Formalism.L2.Pj.rowShift dim n K τ i i' s P) =
      rowAdd t r r' s (rename (typeLetterEquiv hσ hΨ hp hq n) P) := by
  classical
  have key : (rename (typeLetterEquiv hσ hΨ hp hq n)).comp (Formalism.L2.Pj.rowShift dim n K τ i i' s) =
      (rowAdd t r r' s).comp (rename (typeLetterEquiv hσ hΨ hp hq n)) := by
    refine MvPolynomial.algHom_ext fun ℓ => ?_
    simp only [AlgHom.comp_apply, rename_X, Formalism.L2.Pj.rowShift, aeval_X]
    split_ifs with hl
    · obtain ⟨b, rfl⟩ := hl
      simp only [map_add, map_mul, rename_C, rename_X]
      rw [typeLetterEquiv_apply hσ hΨ hp hq h b, typeLetterEquiv_apply hσ hΨ hp hq h' b,
        rowAdd_X_self]
    · rw [rename_X]
      rcases hx : typeLetterEquiv hσ hΨ hp hq n ℓ with ⟨t0, r0, k0⟩
      refine (rowAdd_X_of_ne r s k0 fun ⟨h1, h2⟩ => hl ⟨k0, ?_⟩).symm
      apply (typeLetterEquiv hσ hΨ hp hq n).injective
      rw [hx, typeLetterEquiv_apply hσ hΨ hp hq h k0, h1, h2]
  exact DFunLike.congr_fun key P

theorem rowDeg_iff_rename {τ : ι} {i : Fin (dim τ)} {t : {τ // Ψ τ}} {r : Fin p ⊕ Fin q}
    (h : halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = (t, r))
    (P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K) (d : ℕ) :
    (∀ m ∈ P.support, ∑ b : Fin n, m ⟨τ, i, b⟩ = d) ↔
      IsWeightedHomogeneous (rowInd t r) (rename (typeLetterEquiv hσ hΨ hp hq n) P) d := by
  classical
  rw [isWeightedHomogeneous_rowInd_iff,
    support_rename_of_injective (typeLetterEquiv hσ hΨ hp hq n).injective]
  simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun m _ => ?_
  have hk : ∀ k : Fin n, (Finsupp.mapDomain (typeLetterEquiv hσ hΨ hp hq n) m) (t, r, k) =
      m ⟨τ, i, k⟩ := fun k => by
    rw [← typeLetterEquiv_apply hσ hΨ hp hq h k,
      Finsupp.mapDomain_apply (typeLetterEquiv hσ hΨ hp hq n).injective]
  simp only [hk]

theorem mem_HHa_iff_rename [CharZero K] (a : ι → ℕ → ℕ)
    (P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K) :
    P ∈ Formalism.L2.Pj.HHa dim n K σ Ψ a ↔ IsHarmonic (rename (typeLetterEquiv hσ hΨ hp hq n) P) ∧
      (∀ t r, IsWeightedHomogeneous (rowInd t r) (rename (typeLetterEquiv hσ hΨ hp hq n) P)
        (Sum.elim (fun i : Fin p => a t.1 i) (fun j : Fin q => a (σ t.1) j) r)) ∧
      ∀ t r r', RowLT r r' → ∀ s : ℤ, rowAdd t r r' (s : K)
        (rename (typeLetterEquiv hσ hΨ hp hq n) P) = rename (typeLetterEquiv hσ hΨ hp hq n) P := by
  classical
  have inj := rename_injective (R := K) _ (typeLetterEquiv hσ hΨ hp hq n).injective
  have key : ∀ τ (i : Fin (dim τ)),
      Sum.elim (fun x : Fin p => a (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩).1.1 x)
        (fun y : Fin q => a (σ (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩).1.1) y)
        (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩).2 = a τ i := by
    intro τ i
    rcases half_cases hσ hΨ τ with h | ⟨τ', h', rfl⟩
    · rw [halfRowEquiv_of_mem hσ hΨ hp hq h]
      simp
    · rw [halfRowEquiv_invol hσ hΨ hp hq h']
      simp
  have step : ∀ {τ : ι} {i i' : Fin (dim τ)} {t : {τ // Ψ τ}} {r r' : Fin p ⊕ Fin q},
      halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = (t, r') → halfRowEquiv hσ hΨ hp hq ⟨τ, i'⟩ = (t, r) →
      ∀ s : K, (Formalism.L2.Pj.rowShift dim n K τ i i' s P = P ↔
        rowAdd t r r' s (rename (typeLetterEquiv hσ hΨ hp hq n) P) =
          rename (typeLetterEquiv hσ hΨ hp hq n) P) := by
    intro τ i i' t r r' h h' s
    rw [← rename_rowShift hσ hΨ hp hq h h' s P]
    exact inj.eq_iff.symm
  simp only [Formalism.L2.Pj.HHa, Set.mem_setOf_eq, Formalism.L2.Pj.harmK, Formalism.L2.Pj.RowInv, Formalism.L2.Pj.RowDeg,
    Submodule.mem_iInf, LinearMap.mem_ker]
  refine and_congr ?_ (and_comm.trans (and_congr ?_ ?_))
  · constructor
    · rintro hP ⟨τ, h⟩ x y
      have := rename_lap_one hσ hΨ hp hq h (x.cast (hp _ h).symm) (y.cast (hq _ h).symm) P
      rw [hP τ h, map_zero] at this
      simpa using this.symm
    · intro hQ τ h i j
      apply inj
      rw [rename_lap_one hσ hΨ hp hq h, map_zero]
      exact hQ _ _ _
  · constructor
    · intro hd t r
      obtain ⟨⟨τ, i⟩, hx⟩ := (halfRowEquiv hσ hΨ hp hq).surjective (t, r)
      have := (rowDeg_iff_rename hσ hΨ hp hq hx P (a τ i)).1 fun m hm => hd m hm τ i
      have k := key τ i
      simp only [hx] at k
      rw [k]
      exact this
    · intro hQ m hm τ i
      have h2 := hQ (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩).1 (halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩).2
      rw [key τ i] at h2
      exact (rowDeg_iff_rename hσ hΨ hp hq (rfl : halfRowEquiv hσ hΨ hp hq ⟨τ, i⟩ = _) P (a τ i)).2
        h2 m hm
  · constructor
    · intro hP t r r' hrr s
      cases r with
      | inl x =>
        cases r' with
        | inl y =>
          have hxy : x < y := hrr
          have h1 := halfRowEquiv_of_mem hσ hΨ hp hq t.2 (y.cast (hp _ t.2).symm)
          have h2 := halfRowEquiv_of_mem hσ hΨ hp hq t.2 (x.cast (hp _ t.2).symm)
          simp only [Fin.cast_cast, Fin.cast_eq_self, Subtype.coe_eta] at h1 h2
          exact (step h1 h2 s).1 (hP _ _ _ (by simpa using hxy) s)
        | inr y => exact (hrr : False).elim
      | inr x =>
        cases r' with
        | inl y => exact (hrr : False).elim
        | inr y =>
          have hxy : x < y := hrr
          have h1 := halfRowEquiv_invol hσ hΨ hp hq t.2 (y.cast (hq _ t.2).symm)
          have h2 := halfRowEquiv_invol hσ hΨ hp hq t.2 (x.cast (hq _ t.2).symm)
          simp only [Fin.cast_cast, Fin.cast_eq_self, Subtype.coe_eta] at h1 h2
          exact (step h1 h2 s).1 (hP _ _ _ (by simpa using hxy) s)
    · intro hQ τ i i' hlt s
      rcases half_cases hσ hΨ τ with h | ⟨τ', h', rfl⟩
      · refine (step (halfRowEquiv_of_mem hσ hΨ hp hq h i)
          (halfRowEquiv_of_mem hσ hΨ hp hq h i') s).2 ?_
        exact rowAdd_eq_self_of_forall_int
          (hQ ⟨τ, h⟩ (Sum.inl (i'.cast (hp _ h))) (Sum.inl (i.cast (hp _ h)))
            (show i'.cast (hp _ h) < i.cast (hp _ h) by simpa using hlt)) s
      · refine (step (halfRowEquiv_invol hσ hΨ hp hq h' i)
          (halfRowEquiv_invol hσ hΨ hp hq h' i') s).2 ?_
        exact rowAdd_eq_self_of_forall_int
          (hQ ⟨τ', h'⟩ (Sum.inr (i'.cast (hq _ h'))) (Sum.inr (i.cast (hq _ h')))
            (show i'.cast (hq _ h') < i.cast (hq _ h') by simpa using hlt)) s

private theorem X_mul_pderiv_mem_restrictTotalDegree {S' F' : Type*} [Field F'] [DecidableEq S'] {N : ℕ}
    (v u : S') {Q : MvPolynomial S' F'} (hQ : Q ∈ restrictTotalDegree S' F' N) :
    X v * pderiv u Q ∈ restrictTotalDegree S' F' N := by
  rw [Q.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hu : m u = 0
  · simp [hu]
  · rw [mem_restrictTotalDegree] at hQ ⊢
    rw [X, monomial_mul, one_mul]
    have hle : Finsupp.single u 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hu)
    have hdeg : Finsupp.degree (Finsupp.single v 1 + (m - Finsupp.single u 1)) =
        Finsupp.degree m := by
      conv_rhs => rw [← add_tsub_cancel_of_le hle]
      simp only [map_add, Finsupp.degree_single]
    calc _ ≤ _ := totalDegree_monomial_le _ _
      _ = Finsupp.degree m := hdeg
      _ ≤ Q.totalDegree := le_totalDegree hm
      _ ≤ N := hQ

theorem HHa_eq_zero_or_rowHighest [CharZero K] [Fintype ι] [Fintype {τ // Ψ τ}] (a : ι → ℕ → ℕ) :
    (∀ P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K, P ∈ Formalism.L2.Pj.HHa dim n K σ Ψ a → P = 0) ∨
      ∃ (k : {τ // Ψ τ} → Fin p → ℕ) (k' : {τ // Ψ τ} → Fin q → ℕ),
        typeDegree k k' = ∑ τ, ∑ i : Fin (dim τ), a τ i ∧
        ∀ P : MvPolynomial (Formalism.L2.Pj.Letter ι dim n) K, P ∈ Formalism.L2.Pj.HHa dim n K σ Ψ a ↔
          rename (typeLetterEquiv hσ hΨ hp hq n) P ∈ rowHighest K k k' := by
  classical
  by_cases hA : ∀ τ, Antitone fun i : Fin (dim τ) => a τ i
  · right
    have hx : ∀ t : {τ // Ψ τ}, partOf (diffOf fun x : Fin p => a t.1 x) = fun x : Fin p => a t.1 x :=
      fun t => partOf_diffOf fun x y hxy =>
        hA t.1 (show x.cast (hp _ t.2).symm ≤ y.cast (hp _ t.2).symm from hxy)
    have hy : ∀ t : {τ // Ψ τ},
        partOf (diffOf fun y : Fin q => a (σ t.1) y) = fun y : Fin q => a (σ t.1) y :=
      fun t => partOf_diffOf fun x y hxy =>
        hA (σ t.1) (show x.cast (hq _ t.2).symm ≤ y.cast (hq _ t.2).symm from hxy)
    refine ⟨fun t => diffOf fun x : Fin p => a t.1 x, fun t => diffOf fun y : Fin q => a (σ t.1) y,
      ?_, fun P => ?_⟩
    · have hg : ∀ τ (m : ℕ) (hm : dim τ = m), ∑ x : Fin m, a τ x = ∑ i : Fin (dim τ), a τ i := by
        intro τ m hm
        subst hm
        rfl
      simp only [typeDegree, ← sum_partOf, hx, hy]
      rw [Finset.sum_congr rfl fun t _ => by rw [hg t.1 p (hp _ t.2), hg (σ t.1) q (hq _ t.2)],
        Finset.sum_add_distrib, ← Fintype.sum_subtype_add_sum_subtype Ψ]
      congr 1
      · exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl
      · refine Fintype.sum_equiv
          ⟨fun t => ⟨σ t.1, (hΨ (σ t.1)).2 ((hσ t.1).symm ▸ t.2)⟩, fun u => ⟨σ u.1, (hΨ u.1).1 u.2⟩,
            fun t => Subtype.ext (hσ t.1), fun u => Subtype.ext (hσ u.1)⟩ _ _ fun t => rfl
    · rw [mem_HHa_iff_rename hσ hΨ hp hq a P, mem_rowHighest_iff_rowAdd]
      simp only [hx, hy]
  · left
    intro P hP
    by_contra hP0
    apply hA
    intro τ
    have : Fintype (Formalism.L2.Pj.Letter ι dim n) :=
      inferInstanceAs (Fintype (Σ τ : ι, Fin (dim τ) × Fin n))
    simp only [Formalism.L2.Pj.HHa, Set.mem_setOf_eq, Formalism.L2.Pj.RowInv, Formalism.L2.Pj.RowDeg] at hP
    obtain ⟨-, hinv, hdeg⟩ := hP
    have hz : Function.Injective
        (fun x : Fin (dim τ) × Fin n => (⟨τ, x⟩ : Formalism.L2.Pj.Letter ι dim n)) :=
      fun x y h => eq_of_heq (Sigma.mk.inj h).2
    have hv : ∀ i j : Fin (dim τ), i < j →
        Capelli.rowOp K (fun x : Fin (dim τ) × Fin n => (⟨τ, x⟩ : Formalism.L2.Pj.Letter ι dim n)) i j P = 0 := by
      intro i j hij
      have hfun : ∀ t : K, (fun s => X s + ∑ k : Fin n,
          if s = (⟨τ, (j, k)⟩ : Formalism.L2.Pj.Letter ι dim n) then
            C t * X (⟨τ, (i, k)⟩ : Formalism.L2.Pj.Letter ι dim n) else 0) =
          (fun ℓ : Formalism.L2.Pj.Letter ι dim n =>
            if ∃ b, ℓ = ⟨τ, (j, b)⟩ then X ℓ + C t * X ⟨τ, (i, ℓ.2.2)⟩ else X ℓ) := by
        intro t
        funext ℓ
        split_ifs with hl
        · obtain ⟨b, rfl⟩ := hl
          rw [Finset.sum_eq_single b]
          · simp
          · intro k _ hk
            rw [if_neg]
            intro h
            exact hk (congrArg (fun x : Formalism.L2.Pj.Letter ι dim n => x.2.2) h).symm
          · simp
        · rw [Finset.sum_eq_zero, add_zero]
          intro k _
          rw [if_neg]
          intro h
          exact hl ⟨k, h⟩
      have hall : ∀ t : K, bind₁ (fun s => X s + ∑ k : Fin n,
          if s = (⟨τ, (j, k)⟩ : Formalism.L2.Pj.Letter ι dim n) then
            C t * X (⟨τ, (i, k)⟩ : Formalism.L2.Pj.Letter ι dim n) else 0) P = P := by
        intro t
        rw [hfun t]
        exact hinv τ j i hij t
      have hw : Function.Injective fun k : Fin n => (⟨τ, (j, k)⟩ : Formalism.L2.Pj.Letter ι dim n) :=
        fun k k' h => congrArg (fun x : Formalism.L2.Pj.Letter ι dim n => x.2.2) h
      have huw : ∀ k l : Fin n, (⟨τ, (i, k)⟩ : Formalism.L2.Pj.Letter ι dim n) ≠ ⟨τ, (j, l)⟩ :=
        fun k l h => hij.ne (Fin.ext (congrArg (fun x : Formalism.L2.Pj.Letter ι dim n => (x.2.1 : ℕ)) h))
      rw [Capelli.rowOp_apply]
      exact ((rowAdd_invariant_iff (fun k : Fin n => (⟨τ, (i, k)⟩ : Formalism.L2.Pj.Letter ι dim n))
        (fun k : Fin n => (⟨τ, (j, k)⟩ : Formalism.L2.Pj.Letter ι dim n)) hw huw P).out 1 2).1 hall
    have hκ : ∀ i : Fin (dim τ),
        Capelli.rowOp K (fun x : Fin (dim τ) × Fin n => (⟨τ, x⟩ : Formalism.L2.Pj.Letter ι dim n)) i i P =
          (((a τ i : ℕ) : ℤ) : K) • P :=
      fun i => HighestUnique.rowOp_self _ fun m hm => hdeg m hm τ i
    have hW : ∀ i j : Fin (dim τ), ∀ w ∈ restrictTotalDegree (Formalism.L2.Pj.Letter ι dim n) K P.totalDegree,
        Capelli.rowOp K (fun x : Fin (dim τ) × Fin n => (⟨τ, x⟩ : Formalism.L2.Pj.Letter ι dim n)) i j w ∈
          restrictTotalDegree (Formalism.L2.Pj.Letter ι dim n) K P.totalDegree := by
      intro i j w hw
      rw [Capelli.rowOp_apply]
      exact Submodule.sum_mem _ fun k _ => X_mul_pderiv_mem_restrictTotalDegree _ _ hw
    have hant := highest_weight_antitone (K := K) _ (Capelli.rowOp_lie _ hz)
      (restrictTotalDegree (Formalism.L2.Pj.Letter ι dim n) K P.totalDegree) hW P
      (by simp [mem_restrictTotalDegree]) hP0 (fun i => ((a τ i : ℕ) : ℤ)) hv hκ
    intro x y hxy
    have h5 := hant hxy
    dsimp only at h5 ⊢
    exact_mod_cast h5

end Abstract

section Datum

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
  {l : Level H} (c : Coeff l) (n : ℕ)

noncomputable def thetaLetterEquiv : LtN Dw n ≃ Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n) :=
  typeLetterEquiv (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
    (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) n

variable {n}

theorem thetaLetterEquiv_of_mem {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin (Dw.mult τ)) (k : Fin n) :
    thetaLetterEquiv Dw n ⟨τ, i, k⟩ = xVar ⟨τ, h⟩ (i.cast (mult_of_mem Dw h)) k := by
  unfold thetaLetterEquiv
  exact typeLetterEquiv_apply _ _ _ _ (halfRowEquiv_of_mem _ _ _ _ h i) k

theorem thetaLetterEquiv_conjugate {τ : E →+* ℂ} (h : InPsi H τ)
    (i : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) (k : Fin n) :
    thetaLetterEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i, k⟩ =
      yVar ⟨τ, h⟩ (i.cast (mult_conjEmb_of_mem Dw h)) k := by
  unfold thetaLetterEquiv
  exact typeLetterEquiv_apply _ _ _ _ (halfRowEquiv_invol _ _ _ _ h i) k

theorem rename_letB_of_mem {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin (Dw.mult τ)) (v : Fin n → E) :
    rename (thetaLetterEquiv Dw n) (letB c τ i v) =
      xForm ⟨τ, h⟩ (i.cast (mult_of_mem Dw h)) fun k => embF c τ (v k) := by
  rw [xForm_apply]
  simp only [Formalism.L2.Pj.letB, map_sum, map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw h]

theorem rename_letB_conjugate {τ : E →+* ℂ} (h : InPsi H τ)
    (i : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) (v : Fin n → E) :
    rename (thetaLetterEquiv Dw n) (letB c (ComplexEmbedding.conjugate τ) i v) =
      yForm ⟨τ, h⟩ (i.cast (mult_conjEmb_of_mem Dw h)) fun k => embF c τ (FD.cc (v k)) := by
  rw [yForm_apply]
  simp only [Formalism.L2.Pj.letB, map_sum, map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw h]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  apply Subtype.ext
  show (ComplexEmbedding.conjugate τ) (v k) = τ (FD.cc (v k))
  rw [ComplexEmbedding.conjugate_coe_eq]
  unfold FD.cc
  exact (IsCMField.complexEmbedding_complexConj E τ (v k)).symm

theorem mem_symO_iff_rename (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) :
    P ∈ Formalism.L2.Pj.symO c Λ ↔ rename (thetaLetterEquiv Dw n) P ∈
      GlobalTheory.Harm.symO Dw.p Dw.q (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La := by
  classical
  have back : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      rename (thetaLetterEquiv Dw n).symm (rename (thetaLetterEquiv Dw n) Q) = Q := fun Q => by
    rw [rename_rename, Equiv.symm_comp_self]
    simp
  constructor
  · intro hP
    have hle : Formalism.L2.Pj.symO c Λ ≤ (GlobalTheory.Harm.symO Dw.p Dw.q
        (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La).toSubring.comap
          (rename (R := c.F) (thetaLetterEquiv Dw n)).toRingHom := by
      unfold Formalism.L2.Pj.symO
      rw [Subring.closure_le]
      rintro x (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
      · show rename (thetaLetterEquiv Dw n) (C (o : c.F)) ∈ GlobalTheory.Harm.symO Dw.p Dw.q
          (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La
        rw [rename_C]
        have := Subalgebra.algebraMap_mem (GlobalTheory.Harm.symO Dw.p Dw.q
          (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La) (⟨(o : c.F), o.2⟩ : 𝓞 c.F)
        exact this
      · show rename (thetaLetterEquiv Dw n) (letB c σ i b) ∈ GlobalTheory.Harm.symO Dw.p Dw.q
          (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La
        rcases half_cases (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H) σ with
          h | ⟨τ, h, rfl⟩
        · rw [rename_letB_of_mem Dw c h]
          exact Algebra.subset_adjoin (Or.inl ⟨⟨σ, h⟩, _, b, hb, rfl⟩)
        · rw [rename_letB_conjugate Dw c h]
          exact Algebra.subset_adjoin (Or.inr ⟨⟨τ, h⟩, _, b, hb, rfl⟩)
    exact hle hP
  · intro hP
    have hle : (GlobalTheory.Harm.symO Dw.p Dw.q
        (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La).toSubring ≤
          (Formalism.L2.Pj.symO c Λ).comap (rename (R := c.F) (thetaLetterEquiv Dw n).symm).toRingHom := by
      rw [GlobalTheory.Harm.symO, Algebra.adjoin_eq_ring_closure, Subring.closure_le]
      rintro x (⟨o, rfl⟩ | ⟨t, a, v, hv, rfl⟩ | ⟨t, b, v, hv, rfl⟩)
      · show rename (thetaLetterEquiv Dw n).symm (C (o : c.F)) ∈ Formalism.L2.Pj.symO c Λ
        rw [rename_C]
        exact Subring.subset_closure (Or.inl ⟨⟨(o : c.F), RingOfIntegers.isIntegral_coe o⟩, rfl⟩)
      · show rename (thetaLetterEquiv Dw n).symm (xForm t a fun k => embF c t.1 (v k)) ∈
          Formalism.L2.Pj.symO c Λ
        have := rename_letB_of_mem Dw c t.2 (a.cast (mult_of_mem Dw t.2).symm) v
        simp only [Fin.cast_cast, Fin.cast_eq_self, Subtype.coe_eta] at this
        rw [← this, back]
        exact Subring.subset_closure (Or.inr ⟨t.1, _, v, hv, rfl⟩)
      · show rename (thetaLetterEquiv Dw n).symm
          (yForm t b fun k => embF c t.1 (FD.cc (v k))) ∈ Formalism.L2.Pj.symO c Λ
        have := rename_letB_conjugate Dw c t.2 (b.cast (mult_conjEmb_of_mem Dw t.2).symm) v
        simp only [Subtype.coe_eta] at this
        have h4 : rename (thetaLetterEquiv Dw n).symm (yForm t b fun k => embF c t.1 (FD.cc (v k))) =
            letB c (ComplexEmbedding.conjugate t.1) (b.cast (mult_conjEmb_of_mem Dw t.2).symm) v := by
          rw [← back (letB c (ComplexEmbedding.conjugate t.1)
            (b.cast (mult_conjEmb_of_mem Dw t.2).symm) v), this]
          all_goals rfl
        rw [h4]
        exact Subring.subset_closure (Or.inr ⟨_, _, v, hv, rfl⟩)
    have h3 : rename (thetaLetterEquiv Dw n).symm (rename (thetaLetterEquiv Dw n) P) ∈
        Formalism.L2.Pj.symO c Λ := hle hP
    rwa [back] at h3

end Datum

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj in

theorem theta_letter_dictionary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (c : Coeff l) (n : ℕ) [Fintype {τ : E →+* ℂ // InPsi H τ}],
      ∃ e : LtN Dw n ≃ GlobalTheory.Harm.Var {τ : E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n),
        (∀ (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F), P ∈ Formalism.L2.Pj.symO c Λ ↔
          MvPolynomial.rename e P ∈ GlobalTheory.Harm.symO Dw.p Dw.q
            (fun t : {τ : E →+* ℂ // InPsi H τ} => embF c t.1) Λ.La) ∧
        ∀ (a : (E →+* ℂ) × ℕ → ℕ),
          (∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate
            (InPsi H) (fun τ i => a (τ, i)) → P = 0) ∨
          ∃ (k : {τ : E →+* ℂ // InPsi H τ} → Fin Dw.p → ℕ)
            (k' : {τ : E →+* ℂ // InPsi H τ} → Fin Dw.q → ℕ),
            GlobalTheory.Harm.typeDegree k k' = DF Dw a ∧
            ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate
              (InPsi H) (fun τ i => a (τ, i)) ↔
              MvPolynomial.rename e P ∈ GlobalTheory.Harm.rowHighest c.F k k' := by
  intro E _ _ _ H Dw l c n _
  refine ⟨thetaLetterEquiv Dw n, fun Λ P => mem_symO_iff_rename Dw c Λ P, fun a => ?_⟩
  exact HHa_eq_zero_or_rowHighest (n := n) (K := c.F) (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
    (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) (fun τ i => a (τ, i))

end GlobalTheory.Harm
