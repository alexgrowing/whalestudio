import Development.WeilBound.CoreStatements.VolumeEquality.DegPushVal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumBaseChange

noncomputable section

namespace SheetDecomposition.Fib

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal pointConeMap intNum)

theorem ker_map {σ τ : Type} (k : Type) [Field k] [Algebra ℚ k] (g : σ → MvPolynomial τ ℚ) :
    RingHom.ker (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) =
      (RingHom.ker (aeval g : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ)).map (map (algebraMap ℚ k)) := by
  classical
  have hc : ∀ f : MvPolynomial σ ℚ, (aeval (fun s => map (algebraMap ℚ k) (g s)) : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
      (map (algebraMap ℚ k) f) = map (algebraMap ℚ k) (aeval g f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [algebraMap_eq]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]
  refine le_antisymm (fun f hf => ?_) (Ideal.map_le_iff_le_comap.2 fun f hf => ?_)
  · let b := Module.Basis.ofVectorSpace ℚ k
    let T : Finset _ := f.support.biUnion fun m => (b.repr (coeff m f)).support
    let F : _ → MvPolynomial σ ℚ := fun i => ∑ m ∈ f.support, monomial m (b.repr (coeff m f) i)
    have hf' : f = ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (F i) := by
      conv_lhs => rw [f.as_sum]
      simp only [F, map_sum, Finset.mul_sum, map_monomial, C_mul_monomial]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [← map_sum (monomial m)]
      congr 1
      conv_lhs => rw [← b.linearCombination_repr (coeff m f), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m f)).support) hm)
          (fun i a => a • b i) (fun _ _ => zero_smul _ _)]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    have h0 : ∑ i ∈ T, C (b i) * map (algebraMap ℚ k) (aeval g (F i)) = 0 := by
      rw [RingHom.mem_ker, hf'] at hf
      simpa only [map_sum, map_mul, hc, aeval_C, algebraMap_eq] using hf
    have h1 : ∀ i ∈ T, aeval g (F i) = 0 := fun i hi => by
      ext m
      have := congrArg (coeff m) h0
      simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_zero] at this
      refine linearIndependent_iff'.1 b.linearIndependent T (fun i => coeff m (aeval g (F i))) ?_ i hi
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    rw [hf']
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h1 i hi))
  · rw [Ideal.mem_comap, RingHom.mem_ker, hc, (RingHom.mem_ker.1 hf : aeval g f = 0), map_zero]

variable {S : Type} {r : S → ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

abbrev Ent (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

def genU (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s)) (MvPolynomial (Ent r) ℚ) := fun l m =>
  if h : m < l then X ⟨s, ⟨(l, m), h⟩⟩ else if l = m then 1 else 0

def genMinor (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial (Ent r) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin (x.1.2 + 1) => genU r x.1.1 (x.2 a) (Fin.castLE x.1.2.2 b))

def genCone (r : S → ℕ) (x : Σ b : (Σ s, Fin (r s)), PlIx r b) : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) ℚ :=
  rename Sum.inr (genMinor r x) * X (Sum.inl x.1)

def uNum (r : S → ℕ) {n : ℕ} (a : Fin n → (Σ s, Fin (r s)) → ℤ) : ℤ :=
  @intNum _ (fun _ _ => Classical.propDecidable _) (PlIx r) ℚ _
    (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)) n a

theorem plPt_eq [Algebra ℚ Ω] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (x) :
    plPt u x = aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genMinor r x) := by
  have e : ∀ s l m, aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) (genU r s l m) = u s l m := fun s l m => by
    unfold genU
    split_ifs with h h'
    · simp
    · subst h'; simp [h1]
    · rw [map_zero, h0 s l m (lt_of_le_of_ne (not_lt.1 h) h')]
  unfold plPt genMinor
  rw [AlgHom.map_det]
  congr 1
  ext a b
  exact (e _ _ _).symm

theorem pointIdeal_plPt [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    pointIdeal k (plPt u) =
      (RingHom.ker (aeval (genCone r) : MvPolynomial _ ℚ →ₐ[ℚ] MvPolynomial _ ℚ)).map (map (algebraMap ℚ k)) := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  let φ : MvPolynomial (Ent r) k →ₐ[k] Ω := aeval fun q : Ent r => u q.1 q.2.1.1 q.2.1.2
  have hφ : Function.Injective φ := h.2.2.1
  let Θ : MvPolynomial ((Σ s, Fin (r s)) ⊕ Ent r) k →+* MvPolynomial (Σ s, Fin (r s)) Ω :=
    (map φ.toRingHom).comp (sumAlgEquiv k _ _).toRingHom
  have hΘ : Function.Injective Θ := (map_injective _ hφ).comp (sumAlgEquiv k _ _).injective
  have hr : ∀ f : MvPolynomial (Ent r) ℚ, Θ (map (algebraMap ℚ k) (rename Sum.inr f)) =
      C (aeval (fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) f) := fun f => by
    induction f using MvPolynomial.induction_on with
    | C a => simp [Θ, φ]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f i hf => simp only [map_mul, hf]; simp [Θ, φ]
  have key : (pointConeMap k (plPt u) : MvPolynomial _ k →+* MvPolynomial _ Ω) = Θ.comp
      (aeval (fun s => map (algebraMap ℚ k) (genCone r s)) : MvPolynomial _ k →ₐ[k] MvPolynomial _ k).toRingHom := by
    refine ringHom_ext (fun a => ?_) fun x => ?_
    · simp [pointConeMap, Θ, φ, algebraMap_eq]
    · simp only [pointConeMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, RingHom.comp_apply, genCone, map_mul, hr, plPt_eq u h.1 h.2.1]
      simp [Θ]
  rw [← ker_map]
  ext f
  rw [pointIdeal, RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff Θ hΘ]
  exact (RingHom.congr_fun key f).congr_left

theorem inum_plPt [Fintype S] [CharZero k] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) {n : ℕ}
    (a : Fin n → (Σ s, Fin (r s)) → ℤ) : inum k (plPt u) a = uNum r a := by
  unfold inum uNum
  rw [pointIdeal_plPt u h]
  exact (@GroundTheory.Heights₂.Heights.FieldNumbers.IntNumBaseChange.intersectionNumber_baseChange.1 ℚ _ k _ _ _ _ (fun _ _ => Classical.propDecidable _)
    (PlIx r) _ _).2 n a

def rowIx {n : ℕ} (m l : Fin n) : Fin (m + 1) → Fin n := fun a => if a = Fin.last m then l else Fin.castLE m.2 a

theorem plPt_row (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (s : S) (m l : Fin (r s)) : plPt u ⟨⟨s, m⟩, rowIx m l⟩ = u s l m := by
  unfold plPt
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · simp only [Matrix.of_apply, rowIx, if_true]
      rfl
    · intro a _
      simp only [Matrix.of_apply, rowIx, if_neg (Fin.castSucc_lt_last a).ne, h1]
  · intro a b hab
    have hab' : a < b := hab
    simp only [Matrix.of_apply, rowIx, if_neg (hab'.trans_le (Fin.le_last b)).ne]
    exact h0 _ _ _ hab'

theorem plPt_ne (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) (b) : ∃ i, plPt u ⟨b, i⟩ ≠ 0 :=
  ⟨rowIx b.2 b.2, by rw [show b = ⟨b.1, b.2⟩ from rfl, plPt_row u h1 h0, h1]; exact one_ne_zero⟩

theorem fnField_plPt [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (h1 : ∀ s m, u s m m = 1)
    (h0 : ∀ s l m, l < m → u s l m = 0) : fnField k (plPt u) =
      IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin_le_iff.2 ?_)
  · have : ∀ x, plPt u x ∈ IntermediateField.adjoin k
        (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) := fun x => by
      unfold plPt
      rw [Matrix.det_apply']
      exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun a _ =>
        IntermediateField.subset_adjoin _ _ ⟨⟨_, _, _⟩, rfl⟩)
    rintro _ ⟨p, q, -, rfl⟩
    exact div_mem (this p) (this q)
  · rintro _ ⟨⟨s, l, m⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨⟨⟨s, m⟩, rowIx m l⟩, ⟨⟨s, m⟩, rowIx m m⟩, rfl, ?_⟩
    rw [plPt_row u h1 h0, plPt_row u h1 h0, h1, div_one]

theorem vdeg_plDeg [Fintype S] (O : ValuationSubring Ω) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (b : Σ s, Fin (r s)) :
    vdeg O (plPt u) (plDeg b) = (Finset.univ.sup fun i => O.valuation (plPt u ⟨b, i⟩))⁻¹ := by
  unfold vdeg
  rw [Finset.prod_eq_single b (fun b' _ h => by simp [plDeg, h]) (by simp)]
  simp [plDeg]

theorem trdeg_eq [Fintype S] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) {d : ℕ} (h : IsGenU k u d) :
    Algebra.trdeg k Ω = Nat.card (Ent r) := by
  obtain ⟨h1, h0, hi, hd, hf⟩ := h
  have e : IntermediateField.adjoin k (Set.range fun q : Σ s, Fin (r s) × Fin (r s) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin k (Set.range fun q : Ent r => u q.1 q.2.1.1 q.2.1.2) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro _ ⟨⟨s, l, m⟩, rfl⟩
      rcases lt_trichotomy l m with h | h | h
      · simp only [h0 s l m h]; exact zero_mem _
      · subst h; simp only [h1]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (l, m), h⟩, rfl⟩
    · rintro _ ⟨⟨s, ⟨l, m⟩, h⟩, rfl⟩
      exact ⟨⟨s, l, m⟩, rfl⟩
  rw [e] at hf
  have := Module.finite_of_finrank_pos (hf ▸ hd)
  have hb : IsTranscendenceBasis k fun q : Ent r => u q.1 q.2.1.1 q.2.1.2 :=
    hi.isTranscendenceBasis_iff_isAlgebraic.2 (IntermediateField.isAlgebraic_adjoin_iff_top.1 inferInstance)
  rw [← hb.cardinalMk_eq_trdeg]
  exact (Nat.cast_card).symm

end SheetDecomposition.Fib
