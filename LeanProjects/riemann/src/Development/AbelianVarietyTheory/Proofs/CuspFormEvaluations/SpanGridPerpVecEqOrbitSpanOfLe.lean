import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.FormPartialDerivatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMinorProdEqSmulColActBasePoly

open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.TB (perpVec hMat)
open ReciprocityTheory.ChartRestriction.G.FD (cc)

namespace GlobalTheory.Harm

section Perp

variable {R S : Type} [CommRing R] [CommRing S] {p n : ℕ}

variable (R n) in

def dotPairing : (Fin n → R) →ₗ[R] ((Fin n → R) → R) where
  toFun x y := x ⬝ᵥ y
  map_add' x x' := funext fun y => add_dotProduct x x' y
  map_smul' r x := funext fun y => smul_dotProduct r x y

@[simp] theorem dotPairing_apply (x y : Fin n → R) : dotPairing R n x y = x ⬝ᵥ y := rfl

theorem map_perpVec_apply (f : R →+* S) (h : (Fin n → R) →ₗ[R] ((Fin n → R) → R))
    (h' : (Fin n → S) →ₗ[S] ((Fin n → S) → S)) (e e' : Fin p → Fin n → R) (g : Fin n → R)
    (ε ε' : Fin p → Fin n → S) (γ : Fin n → S) (he' : ∀ a k, f (e' a k) = ε' a k)
    (hg : ∀ k, f (g k) = γ k) (hM : ∀ a' a, f (h (e' a') (e a)) = h' (ε' a') (ε a))
    (hge : ∀ a, f (h g (e a)) = h' γ (ε a)) (k : Fin n) :
    f (perpVec h e e' g k) = perpVec h' ε ε' γ k := by
  have hm : f.mapMatrix (hMat h e e') = hMat h' ε ε' := by
    ext a' a; exact hM a' a
  have hadj (a a') : f ((hMat h e e').adjugate a a') = (hMat h' ε ε').adjugate a a' := by
    rw [← hm, ← RingHom.map_adjugate]; rfl
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_sub, map_mul,
    map_sum, RingHom.map_det, hm, hadj, hg, hge, he']

theorem map_perpVec_dotPairing (f : R →+* S) (ε ε' : Fin p → Fin n → R) (γ : Fin n → R) :
    f ∘ perpVec (dotPairing R n) ε ε' γ =
      perpVec (dotPairing S n) (fun a => f ∘ ε a) (fun a => f ∘ ε' a) (f ∘ γ) :=
  funext fun k => map_perpVec_apply f _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => by simp [dotProduct]) (fun _ => by simp [dotProduct]) k

theorem adjugate_isHomogeneous {σ : Type*} (M : Matrix (Fin p) (Fin p) (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ a b, (M a b).IsHomogeneous d) (a b : Fin p) :
    (M.adjugate a b).IsHomogeneous ((p - 1) * d) := by
  rw [adjugate_apply]
  have := det_isWeightedHomogeneous (1 : σ → ℕ) (M.updateRow b (Pi.single a 1))
    (fun i => if i = b then 0 else d) (fun i j => by
      by_cases hi : i = b
      · subst hi
        rw [updateRow_self, if_pos rfl, Pi.single_apply]
        split_ifs
        · exact isWeightedHomogeneous_one _ _
        · exact isWeightedHomogeneous_zero _ _ _
      · rw [updateRow_ne hi, if_neg hi]; exact hM i j)
  change IsWeightedHomogeneous 1 _ _
  convert this using 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem perpVec_dotPairing_isHomogeneous {σ : Type} (ε ε' : Fin p → Fin n → MvPolynomial σ R)
    (γ : Fin n → MvPolynomial σ R) (hε : ∀ a k, (ε a k).IsHomogeneous 1)
    (hε' : ∀ a k, (ε' a k).IsHomogeneous 1) (hγ : ∀ k, (γ k).IsHomogeneous 1) (k : Fin n) :
    (perpVec (dotPairing _ n) ε ε' γ k).IsHomogeneous (2 * p + 1) := by
  have hM (a' a) : (hMat (dotPairing _ n) ε ε' a' a).IsHomogeneous 2 :=
    show (∑ k, ε' a' k * ε a k).IsHomogeneous 2 from
      IsHomogeneous.sum _ _ _ fun k _ => (hε' a' k).mul (hε a k)
  have hge (a) : (dotPairing _ n γ (ε a)).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun k _ => (hγ k).mul (hε a k)
  have hdet : (hMat (dotPairing _ n) ε ε').det.IsHomogeneous (2 * p) := by
    have := det_isWeightedHomogeneous (1 : σ → ℕ) _ (fun _ => 2) hM
    simpa [mul_comm, IsHomogeneous] using this
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (hdet.mul (hγ k)).sub (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _
    fun a' _ => ?_)
  have := ((adjugate_isHomogeneous _ 2 hM a a').mul (hge a)).mul (hε' a' k)
  have hp := a.pos
  rwa [show (p - 1) * 2 + 2 + 1 = 2 * p + 1 by omega] at this

end Perp

section Param

variable {K : Type*} [CommRing K] {σ ω T κ : Type*} {p q : ℕ}

noncomputable def swapVars : MvPolynomial ω (MvPolynomial σ K) →+* MvPolynomial σ (MvPolynomial ω K) :=
  eval₂Hom (MvPolynomial.map C) fun v => C (X v)

theorem eval_swapVars (x : σ → K) (F : MvPolynomial ω (MvPolynomial σ K)) :
    eval (fun i => C (x i)) (swapVars F) = MvPolynomial.map (eval x) F := by
  have : (eval fun i => (C (x i) : MvPolynomial ω K)).comp swapVars = MvPolynomial.map (eval x) := by
    ext1
    · ext1
      · ext1 r; simp [swapVars]
      · simp [swapVars]
    · simp [swapVars]
  exact DFunLike.congr_fun this F

variable [Fintype κ]

theorem swapVars_rowForm_isHomogeneous (t : T) (r : Fin p ⊕ Fin q) (u : κ → MvPolynomial σ K)
    {d : ℕ} (hu : ∀ k, (u k).IsHomogeneous d) : (swapVars (rowForm t r u)).IsHomogeneous d := by
  rw [rowForm_apply, map_sum]
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  simp only [swapVars, map_mul, eval₂Hom_C, eval₂Hom_X']
  simpa using ((hu k).map C).mul (isHomogeneous_C σ (X (t, r, k) : Poly K T p q κ))

theorem swapVars_minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → MvPolynomial σ K) (φ : T → Fin q → κ → MvPolynomial σ K) {d d' : ℕ}
    (hε : ∀ t a k, (ε t a k).IsHomogeneous d) (hφ : ∀ t b k, (φ t b k).IsHomogeneous d') :
    (swapVars (minorProd c c' ε φ)).IsHomogeneous
      (∑ t, (d * partSize (c t) + d' * partSize (c' t))) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine IsHomogeneous.prod _ _ _ fun t _ => IsHomogeneous.mul ?_ ?_
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [xMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (xForm t (lead i a) (ε t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d) fun a b => swapVars_rowForm_isHomogeneous t _ _ (hε t _)
    simpa [mul_comm, IsHomogeneous] using this
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [yMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (yForm t (lead i a) (φ t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d') fun a b => swapVars_rowForm_isHomogeneous t _ _ (hφ t _)
    simpa [mul_comm, IsHomogeneous] using this

end Param

section Field

variable {R S : Type} [CommRing R] [CommRing S] {T : Type*} [Fintype T] {ι : Type} [Fintype ι]
  {p q n : ℕ}

noncomputable def coordProd (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (w w' : T → ι → Fin n → R)
    (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) : Poly R T p q (Fin n) :=
  minorProd c c' (fun t a k => ∑ i, x (Sum.inl a, i) * w' t i k)
    fun t b => perpVec (dotPairing R n) (fun a k => ∑ i, x (Sum.inl a, i) * w' t i k)
      (fun a k => ∑ i, x (Sum.inr (Sum.inl a), i) * w t i k)
      fun k => ∑ i, x (Sum.inr (Sum.inr b), i) * w t i k

theorem map_coordProd (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) :
    MvPolynomial.map f (coordProd c c' w w' x) =
      coordProd c c' (fun t i k => f (w t i k)) (fun t i k => f (w' t i k)) fun j => f (x j) := by
  simp only [coordProd, map_minorProd, map_perpVec_dotPairing]
  simp only [Function.comp_def, map_sum, map_mul]

variable {K : Type} [Field K]

theorem coordProd_mem_orbitSpan (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
    coordProd c c' w w' x ∈ orbitSpan K hpq c c' :=
  minorProd_mem_orbitSpan hpq c c' fun _ a _ => by
    rw [dotProduct_comm]; exact perpendicular_vector_exists K _ p (dotPairing K n) _ _ _ a

theorem span_range_coordProd (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K)
    (hw : ∀ y y' : T → Fin n → K, ∃ x : ι → K,
      (∀ t k, ∑ i, x i * w t i k = y t k) ∧ ∀ t k, ∑ i, x i * w' t i k = y' t k) :
    Submodule.span K (Set.range (coordProd c c' w w')) = orbitSpan K hpq c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact coordProd_mem_orbitSpan hpq c c' w w' x
  rw [orbitSpan_eq_span_linearIndependent]
  refine Submodule.span_mono ?_
  rintro _ ⟨ε, φ, hε, -, hperp, rfl⟩
  choose ε' hε' using fun t a => surjective_mulVecLin_of (hε t) (Pi.single a 1)
  choose x₁ _ hx₁ using fun a => hw 0 fun t => ε t a
  choose x₂ hx₂ _ using fun a => hw (fun t => ε' t a) 0
  choose x₃ hx₃ _ using fun b => hw (fun t => φ t b) 0
  refine ⟨fun j => Sum.elim x₁ (Sum.elim x₂ x₃) j.1 j.2, ?_⟩
  simp only [coordProd, Sum.elim_inl, Sum.elim_inr, hx₁, hx₂, hx₃]
  congr 1
  funext t b
  have hM : hMat (dotPairing K n) (ε t) (ε' t) = 1 := by
    ext a' a
    have := congrFun (hε' t a') a
    rw [one_eq_pi_single, ← this]
    exact dotProduct_comm (ε' t a') (ε t a)
  have := perpendicular_vector_perp K _ p (dotPairing K n) (ε t) (ε' t) (φ t b) fun a => by
    rw [dotPairing_apply, dotProduct_comm]; exact hperp t a b
  rw [hM, det_one, one_smul] at this
  exact this

theorem span_grid_coordProd [CharZero K] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) {dg : ℕ} (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K ((fun x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → ℕ =>
      coordProd c c' w w' fun j => (x j : K)) '' {x | ∀ j, x j ≤ dg}) =
      Submodule.span K (Set.range (coordProd c c' w w')) := by
  let F : MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) (Poly K T p q (Fin n)) :=
    swapVars (coordProd c c' (fun t i k => C (w t i k)) (fun t i k => C (w' t i k)) X)
  have hlin (r : Fin p ⊕ Fin p ⊕ Fin q) (u : ι → K) :
      (∑ i, X (r, i) * C (u i) : MvPolynomial _ K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X K (r, i)).mul (isHomogeneous_C _ (u i))
  have hF : F.IsHomogeneous _ := swapVars_minorProd_isHomogeneous c c' _ _ (d := 1)
    (d' := 2 * p + 1) (fun t a k => hlin _ _) fun t b k =>
      perpVec_dotPairing_isHomogeneous _ _ _ (fun a k => hlin _ _) (fun a k => hlin _ _)
        (fun k => hlin _ _) k
  have hdeg : F.totalDegree ≤ dg := by
    refine hF.totalDegree_le.trans (le_trans ?_ hdg)
    rw [typeDegree, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hev (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
      eval (fun j => C (x j)) F = coordProd c c' w w' x := by
    rw [eval_swapVars, map_coordProd]; simp only [eval_C, eval_X]
  have := span_grid_eval_eq_span_range (A := K) (K := K) dg F
    fun j => (degreeOf_le_totalDegree F j).trans hdeg
  simp only [Algebra.algebraMap_self, RingHom.id_apply, algebraMap_eq, hev] at this
  rw [← this]
  congr 2
  funext x
  rw [← hev]; simp only [map_natCast]

end Field

section Embeddings

theorem exists_sum_mul_embedding_eq {E K J κ ι : Type*} [Field E] [CharZero E] [Field K]
    [Finite J] [Finite κ] [Fintype ι] (σ : J → E →+* K) (hσ : Function.Injective σ)
    (v : ι → κ → E) (hv : Submodule.span ℚ (Set.range v) = ⊤) (y : J → κ → K) :
    ∃ x : ι → K, ∀ j k, ∑ i, x i * σ j (v i k) = y j k := by
  classical
  have := Fintype.ofFinite J
  have := Fintype.ofFinite κ
  let u : (κ → E) → J × κ → K := fun z s => σ s.1 (z s.2)
  let U : Submodule K (J × κ → K) := Submodule.span K (Set.range fun i => u (v i))
  have hU (z : κ → E) : u z ∈ U := by
    have hz : z ∈ Submodule.span ℚ (Set.range v) := hv ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => convert U.zero_mem; ext s; simp [u]
    | add z z' _ _ h h' => convert U.add_mem h h'; ext s; simp [u]
    | smul r z _ h => convert U.smul_mem (r : K) h; ext s; simp [u, Rat.smul_def]
  have hind : LinearIndependent K fun j => (σ j : E → K) :=
    (linearIndependent_monoidHom E K).comp (fun j => (σ j : E →* K)) fun j j' e =>
      hσ (RingHom.ext fun a => DFunLike.congr_fun e a)
  have hy : (fun s : J × κ => y s.1 s.2) ∈ U := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
    intro l hl
    have h0 (j k) : l (Pi.single (j, k) 1) = 0 := by
      refine Fintype.linearIndependent_iff.1 hind (fun j => l (Pi.single (j, k) 1)) ?_ j
      funext a
      have h1 := (Submodule.mem_dualAnnihilator l).1 hl _ (hU (Pi.single k a))
      have h2 : u (Pi.single k a) = ∑ j, σ j a • Pi.single (j, k) 1 := by
        ext ⟨j', k'⟩
        by_cases hk : k' = k <;> simp [u, Finset.sum_apply, Pi.single_apply, hk]
      rw [h2, map_sum] at h1
      simpa [mul_comm] using h1
    rw [← Finset.univ_sum_single (fun s : J × κ => y s.1 s.2), map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_one (y s.1 s.2), ← smul_eq_mul, Pi.single_smul', map_smul, h0, smul_zero]
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  exact ⟨x, fun j k => by simpa [u] using congrFun hx (j, k)⟩

end Embeddings

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] [CharZero K]
  {T : Type*} [Fintype T] {ι : Type} [Fintype ι] {p q n : ℕ}

theorem span_grid_perpVec_eq_orbitSpan_of_le (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' := by
  let γ : E →+* E := (IsCMField.complexConj E : E ≃ₐ[_] E)
  have hγ (x) : cc x = γ x := rfl
  let σ : T × Bool → E →+* K := fun s => if s.2 then (τ s.1).comp γ else τ s.1
  have hσ : Function.Injective σ := fun s s' e => hτ (funext fun x => by
    have := DFunLike.congr_fun e x
    obtain ⟨t, _ | _⟩ := s <;> obtain ⟨t', _ | _⟩ := s' <;> exact this)
  rw [← span_range_coordProd hpq c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
    fun y y' => by
      obtain ⟨x, hx⟩ := exists_sum_mul_embedding_eq σ hσ v hv fun s => if s.2 then y' s.1 else y s.1
      exact ⟨x, fun t => hx (t, false), fun t => hx (t, true)⟩,
    ← span_grid_coordProd c c' _ _ hdg]
  have key (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ) :
      minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        (fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)) =
      coordProd c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
        fun j => ((Sum.elim A (Sum.elim A' B) j.1 j.2 : ℕ) : K) := by
    rw [coordProd]
    congr 1
    · funext t a k
      simp [hγ]
    · funext t b k
      refine map_perpVec_apply _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ k
      all_goals intros; simp [hγ, hh, dotProduct]
  congr 1
  ext P
  constructor
  · rintro ⟨A, A', B, hA, hA', hB, rfl⟩
    refine ⟨fun j => Sum.elim A (Sum.elim A' B) j.1 j.2, ?_, (key A A' B).symm⟩
    rintro ⟨a | a | b, i⟩
    exacts [hA a i, hA' a i, hB b i]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a i => x (Sum.inl a, i), fun a i => x (Sum.inr (Sum.inl a), i),
      fun b i => x (Sum.inr (Sum.inr b), i), fun _ _ => hx _, fun _ _ => hx _, fun _ _ => hx _, ?_⟩
    rw [key]
    congr 1
    funext j
    obtain ⟨a | a | b, i⟩ := j <;> rfl

theorem span_grid_perpVec_eq_orbitSpan (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * (p + q) + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' :=
  span_grid_perpVec_eq_orbitSpan_of_le τ hτ hpq h hh v hv c c'
    ((Nat.mul_le_mul_right _ (by omega)).trans hdg)

end CM

end GlobalTheory.Harm
