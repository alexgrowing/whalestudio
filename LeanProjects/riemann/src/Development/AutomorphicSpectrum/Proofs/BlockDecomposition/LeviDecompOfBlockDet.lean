import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf

noncomputable section

open Matrix PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisLevi

variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_stab_univ {g : GL (ι ⊕ ι) R} :
    g ∈ stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) ↔
      ∀ r c : ι, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr r) (Sum.inl c) = 0 ∧
        ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr r) (Sum.inl c) = 0 := by
  constructor
  · intro h r c
    exact h (Sum.inr r) (by simp) (Sum.inl c) (by simp)
  · intro h r hr c hc
    obtain ⟨c', -, rfl⟩ := hc
    rcases r with r | r
    · exact absurd ⟨r, trivial, rfl⟩ hr
    · exact h r c'

theorem blk_mul (x y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (hy : ∀ r c, y (Sum.inr r) (Sum.inl c) = 0) :
    (x * y).toBlocks₁₁ = x.toBlocks₁₁ * y.toBlocks₁₁ := by
  ext r c
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, hy]

theorem blk_one : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ = 1 := by
  ext r c
  simp [Matrix.toBlocks₁₁, Matrix.one_apply]

def piP : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) →* GL ι R where
  toFun q := ⟨(q.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁, ((q.1⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁,
    by rw [← blk_mul _ _ (fun r c => (mem_stab_univ.1 q.2 r c).2), Units.mul_inv, blk_one],
    by rw [← blk_mul _ _ (fun r c => (mem_stab_univ.1 q.2 r c).1), Units.inv_mul, blk_one]⟩
  map_one' := Units.ext (by simp [blk_one])
  map_mul' a b := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk]
    exact blk_mul _ _ (fun r c => (mem_stab_univ.1 b.2 r c).1))

theorem dual_mul (σ : R →+* R) (a b : Matrix ι ι R) : (aᵀ.map σ) * (bᵀ.map σ) = ((b * a)ᵀ).map σ := by
  rw [Matrix.transpose_mul, Matrix.map_mul]

def jG (σ : R →+* R) : GL ι R →* GL (ι ⊕ ι) R where
  toFun m := ⟨fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map σ),
    fromBlocks ((m⁻¹ : GL ι R) : Matrix ι ι R) 0 0 ((m : Matrix ι ι R)ᵀ.map σ),
    by
      rw [Matrix.fromBlocks_multiply, dual_mul]
      simp [Matrix.map_one _ (map_zero σ) (map_one σ)],
    by
      rw [Matrix.fromBlocks_multiply, dual_mul]
      simp [Matrix.map_one _ (map_zero σ) (map_one σ)]⟩
  map_one' := Units.ext (by simp [Matrix.map_one _ (map_zero σ) (map_one σ)])
  map_mul' a b := Units.ext (by
    simp only [Units.val_mul, Units.val_mk, Matrix.fromBlocks_multiply, _root_.mul_inv_rev]
    simp [Matrix.transpose_mul, Matrix.map_mul])

theorem jG_val (σ : R →+* R) (m : GL ι R) : ((jG σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map σ) := rfl

theorem jG_inv_val (σ : R →+* R) (m : GL ι R) : (((jG σ m)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    fromBlocks ((m⁻¹ : GL ι R) : Matrix ι ι R) 0 0 ((m : Matrix ι ι R)ᵀ.map σ) := rfl

theorem jG_mem_stab (σ : R →+* R) (m : GL ι R) : jG σ m ∈ stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) :=
  mem_stab_univ.2 fun r c => by rw [jG_val, jG_inv_val]; simp

theorem jG_mem_uSub (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (m : GL ι R) : jG A.σ m ∈ A.uSub ε ι := by
  show ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * Ad.J R ε ι * ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map A.σ = Ad.J R ε ι
  have hmm : ((((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ).map A.σ) = ((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ := by
    ext r c; simp [h]
  have h1 : (m : Matrix ι ι R)ᵀ * ((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  have h2 : (((m⁻¹ : GL ι R) : Matrix ι ι R).map A.σ) * ((m : Matrix ι ι R).map A.σ) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ)ᵀ = ((m⁻¹ : GL ι R) : Matrix ι ι R).map A.σ := by
    ext r c; simp
  rw [jG_val, Ad.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, hmm, h3]
  simp [-Matrix.coe_units_inv, h1, h2, Matrix.mul_assoc]

section Alg

variable (A : Ad E R) (ε : ℤˣ)

def piQ : A.uQ ε (Set.univ : Set ι) →* GL ι R where
  toFun q := piP ⟨q.1.1, Subgroup.mem_subgroupOf.1 q.2⟩
  map_one' := map_one piP
  map_mul' a b := map_mul piP ⟨a.1.1, Subgroup.mem_subgroupOf.1 a.2⟩ ⟨b.1.1, Subgroup.mem_subgroupOf.1 b.2⟩

def jQ (h : ∀ x, A.σ (A.σ x) = x) : GL ι R →* A.uQ ε (Set.univ : Set ι) where
  toFun m := ⟨⟨jG A.σ m, jG_mem_uSub A ε h m⟩, Subgroup.mem_subgroupOf.2 (jG_mem_stab _ m)⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (jG A.σ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (jG A.σ) a b))

theorem piQ_jQ (h : ∀ x, A.σ (A.σ x) = x) (m : GL ι R) : piQ A ε (jQ A ε h m) = m :=
  Units.ext (by
    show (fromBlocks (m : Matrix ι ι R) 0 0 (((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ)).toBlocks₁₁ = m
    simp)

end Alg

theorem mem_stab_inl_iff (s : Set ι) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι))) :
    q.1 ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) ↔ piP q ∈ stab R s := by
  constructor
  · intro h r hr c hc
    exact h (Sum.inl r) (by simpa using hr) (Sum.inl c) ⟨c, hc, rfl⟩
  · intro h r hr c hc
    obtain ⟨c', hc', rfl⟩ := hc
    rcases r with r | r
    · exact h r (fun hrs => hr ⟨r, hrs, rfl⟩) c' hc'
    · exact mem_stab_univ.1 q.2 r c'

open Classical in
theorem bdet_congr {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : Set κ) (t : Set κ')
    (e : s ≃ t) (g : GL κ' R) (m : GL κ R)
    (h : ∀ a b : s, (g : Matrix κ' κ' R) (e a).1 (e b).1 = (m : Matrix κ κ R) a.1 b.1) : bdet t g = bdet s m := by
  have hdet : ((g : Matrix κ' κ' R).submatrix (Subtype.val : t → κ') Subtype.val).det =
      ((m : Matrix κ κ R).submatrix (Subtype.val : s → κ) Subtype.val).det := by
    rw [← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext a b
    exact h a b
  unfold bdet
  simp only [hdet]

theorem bdet_inl (s : Set ι) (g : GL (ι ⊕ ι) R) (m : GL ι R)
    (h : ∀ r c, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl r) (Sum.inl c) = (m : Matrix ι ι R) r c) :
    bdet (Sum.inl '' s : Set (ι ⊕ ι)) g = bdet s m :=
  bdet_congr s _ (Equiv.Set.image Sum.inl s Sum.inl_injective) g m fun a b => h a.1 b.1

theorem unit_corner (Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (ι ⊕ ι) ℂ)
    (h0 : ∀ r c, Q (Sum.inr r) (Sum.inl c) = 0) : Q.toBlocks₁₁ ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext r c
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hQ) (Sum.inl r)) (Sum.inl c)
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.star_apply, h0, Matrix.one_apply, Matrix.toBlocks₁₁] using this

theorem piP_mem_kGL (A : Ad E R) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.kGL (ι ⊕ ι)) : piP q ∈ A.kGL ι := by
  refine ⟨fun r c => ⟨(hq.1 _ _).1, (hq.1 _ _).2⟩, fun w => ?_⟩
  have := unit_corner _ (hq.2 w) (fun r c => by
    simp [(mem_stab_univ.1 q.2 r c).1])
  exact this

theorem jG_mem_k (A : Ad E R) (hO : ∀ x ∈ A.O, A.σ x ∈ A.O)
    (hφ : ∀ w x, A.φ w (A.σ x) = (starRingEnd ℂ) (A.φ w x)) (m : GL ι R) (hm : m ∈ A.kGL ι) :
    jG A.σ m ∈ A.kGL (ι ⊕ ι) := by
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · rw [jG_val]
    rcases r with r | r <;> rcases c with c | c
    · exact (hm.1 r c).1
    · exact A.O.zero_mem
    · exact A.O.zero_mem
    · exact hO _ (hm.1 c r).2
  · rw [jG_inv_val]
    rcases r with r | r <;> rcases c with c | c
    · exact (hm.1 r c).2
    · exact A.O.zero_mem
    · exact A.O.zero_mem
    · exact hO _ (hm.1 c r).1
  · set M := (m : Matrix ι ι R).map (A.φ w) with hM
    have hMu := hm.2 w
    have h1 : M * ((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = 1 := by
      rw [hM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : star M * M = 1 := Matrix.mem_unitaryGroup_iff'.1 hMu
    have h3 : ((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w) = star M := by
      rw [← Matrix.one_mul (((m⁻¹ : GL ι R) : Matrix ι ι R).map (A.φ w)), ← h2, Matrix.mul_assoc, h1, Matrix.mul_one]
    have h4 : ((((m⁻¹ : GL ι R) : Matrix ι ι R)ᵀ.map A.σ).map (A.φ w)) = M := by
      ext r c
      have := congrFun (congrFun h3 c) r
      simp only [Matrix.map_apply, Matrix.star_apply] at this
      simp only [Matrix.map_apply, Matrix.transpose_apply, hφ, this]
      simp [hM]
    have h5 : ((jG A.σ m : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map (A.φ w) = fromBlocks M 0 0 M := by
      rw [jG_val, Matrix.fromBlocks_map, h4]
      simp [hM]
    rw [h5, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    have h6 : M * Mᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hMu
    simp [h6]

def tau (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) : E →+* E where
  toFun x := (h x).choose
  map_one' := hi (by rw [← (h 1).choose_spec]; simp)
  map_mul' a b := hi (by rw [← (h (a * b)).choose_spec, map_mul, map_mul, map_mul, ← (h a).choose_spec, ← (h b).choose_spec])
  map_zero' := hi (by rw [← (h 0).choose_spec]; simp)
  map_add' a b := hi (by rw [← (h (a + b)).choose_spec, map_add, map_add, map_add, ← (h a).choose_spec, ← (h b).choose_spec])

theorem i_tau (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (x : E) :
    A.i (tau A hi h x) = A.σ (A.i x) := (h x).choose_spec.symm

theorem piP_mem_ratGL (A : Ad E R) (hi : Function.Injective A.i) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.ratGL (ι ⊕ ι)) : piP q ∈ A.ratGL ι := by
  obtain ⟨x, hx⟩ := hq
  have hxm : ∀ a b, ((Matrix.GeneralLinearGroup.map A.i x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) a b = A.i ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) E) a b) := fun a b => rfl
  have hxi : ∀ a b, (((Matrix.GeneralLinearGroup.map A.i x)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) a b = A.i (((x⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E) a b) := fun a b => by
    rw [← map_inv]; rfl
  have hst : x ∈ stab E (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) := mem_stab_univ.2 fun r c => by
    have h := mem_stab_univ.1 q.2 r c
    rw [← hx, hxm, hxi] at h
    exact ⟨hi (by rw [h.1, map_zero]), hi (by rw [h.2, map_zero])⟩
  refine ⟨piP ⟨x, hst⟩, Units.ext ?_⟩
  ext r c
  show A.i ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) E) (Sum.inl r) (Sum.inl c)) = (q.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl r) (Sum.inl c)
  rw [← hx, hxm]

theorem jG_mem_rat (A : Ad E R) (hi : Function.Injective A.i) (h : ∀ x, ∃ y, A.σ (A.i x) = A.i y) (m : GL ι R)
    (hm : m ∈ A.ratGL ι) : jG A.σ m ∈ A.ratGL (ι ⊕ ι) := by
  obtain ⟨y, rfl⟩ := hm
  refine ⟨jG (tau A hi h) y, Units.ext ?_⟩
  have hinv : ∀ a b, (((Matrix.GeneralLinearGroup.map A.i y)⁻¹ : GL ι R) : Matrix ι ι R) a b = A.i (((y⁻¹ : GL ι E) : Matrix ι ι E) a b) := fun a b => by
    rw [← map_inv]; rfl
  ext r c
  rcases r with r | r <;> rcases c with c | c
  · rfl
  · show A.i 0 = 0
    exact map_zero _
  · show A.i 0 = 0
    exact map_zero _
  · show A.i (tau A hi h (((y⁻¹ : GL ι E) : Matrix ι ι E) c r)) = A.σ ((((Matrix.GeneralLinearGroup.map A.i y)⁻¹ : GL ι R) : Matrix ι ι R) c r)
    rw [i_tau, hinv]

section Top

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_piQ (A : Ad E R) (ε : ℤˣ) : Continuous (piQ A ε (ι := ι)) := by
  have hv : Continuous fun q : A.uQ ε (Set.univ : Set ι) => (q.1.1 : GL (ι ⊕ ι) R) :=
    continuous_subtype_val.comp continuous_subtype_val
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun r c => ?_, continuous_matrix fun r c => ?_⟩
  · exact (Units.continuous_val.comp hv).matrix_elem _ _
  · exact (Units.continuous_val.comp hv.inv).matrix_elem _ _

theorem continuous_jG (σ : R →+* R) (hσ : Continuous σ) : Continuous (jG σ : GL ι R → GL (ι ⊕ ι) R) := by
  have hm : Continuous fun m : GL ι R => (m : Matrix ι ι R) := Units.continuous_val
  have hi : Continuous fun m : GL ι R => ((m⁻¹ : GL ι R) : Matrix ι ι R) := Units.continuous_val.comp continuous_inv
  rw [Units.continuous_iff]
  exact ⟨hm.matrix_fromBlocks continuous_const continuous_const (hi.matrix_transpose.matrix_map hσ),
    hi.matrix_fromBlocks continuous_const continuous_const (hm.matrix_transpose.matrix_map hσ)⟩

theorem continuous_jQ (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (hσ : Continuous A.σ) :
    Continuous (jQ A ε h (ι := ι)) :=
  Continuous.subtype_mk (Continuous.subtype_mk (continuous_jG A.σ hσ) _) _

theorem isClosed_uQ (A : Ad E R) (ε : ℤˣ) (s : Set ι)
    (h : IsClosed (stab R (Sum.inl '' s : Set (ι ⊕ ι)) : Set (GL (ι ⊕ ι) R))) :
    IsClosed (A.uQ ε s : Set (A.U ε ι)) :=
  h.preimage continuous_subtype_val

end Top

theorem mem_uQ_iff (A : Ad E R) (ε : ℤˣ) (s : Set ι) (q : A.uQ ε (Set.univ : Set ι)) :
    q.1 ∈ A.uQ ε s ↔ piQ A ε q ∈ stab R s :=
  Subgroup.mem_subgroupOf.trans (mem_stab_inl_iff s ⟨q.1.1, Subgroup.mem_subgroupOf.1 q.2⟩)

theorem factor (A : Ad E R) (ε : ℤˣ) (h : ∀ x, A.σ (A.σ x) = x) (q : A.uQ ε (Set.univ : Set ι)) (p k : GL ι R)
    (e : piQ A ε q = p * k) : ∃ q' : A.uQ ε (Set.univ : Set ι), piQ A ε q' = p ∧ q.1 = q'.1 * (jQ A ε h k).1 := by
  refine ⟨q * (jQ A ε h k)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, piQ_jQ, e, mul_inv_cancel_right]
  · rw [← Subgroup.coe_mul, inv_mul_cancel_right]

section Main

variable [TopologicalSpace R]

theorem iwa_inf (A : Ad E R) (hA : A.Good) (ε : ℤˣ) (hI : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) (s : Set ι) :
    Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
  intro g
  obtain ⟨q, hq, k, hk, rfl⟩ := hI g
  obtain ⟨p, hp, k', hk', e⟩ := hA.iwa ι s (piQ A ε ⟨q, hq⟩)
  obtain ⟨q', h1, h2⟩ := factor A ε hA.σσ ⟨q, hq⟩ p k' e
  have hjk : ((jQ A ε hA.σσ k').1 : A.U ε ι) ∈ A.uK ε ι :=
    Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ k' hk')
  refine ⟨q'.1, ⟨(mem_uQ_iff A ε s q').2 (h1 ▸ hp), q'.2⟩, (jQ A ε hA.σσ k').1 * k, mul_mem hjk hk, ?_⟩
  rw [← mul_assoc, ← h2]

end Main

section Ext

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R]

theorem ht_GL (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (s : Set ι) (p : GL ι R) (hp : p ∈ stab R s)
    (k : GL ι R) (hk : k ∈ A.kGL ι) : A.htGL s (p * k) = A.lg (bdet s p) := by
  have hb := hB E R A hA.toGoodL ι s
  exact (hE (GL ι R) (A.kGL ι) (A.kGL ι) (stab R s) (fun p => A.lg (bdet s p)) (hA.kcpt ι) hb.1 (hA.iwa ι s)
    (fun p hp q hq => by simp only [hb.2.1 p hp q hq, hA.lgmul]) (hA.lgcont.comp_continuousOn hb.2.2.1)
    (fun p hp hk => hb.2.2.2.2.1 p hp hk) (fun p hp hk => hb.2.2.2.2.1 p hp hk)).2 p hp k hk

theorem ht_U (hB : BdetLaw) (hE : ExtLaw) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) [T2Space (A.U ε ι)]
    (hK : IsCompact (A.uK ε ι : Set (A.U ε ι))) (s : Set ι) (hI : Iwa (A.uQ ε s) (A.uK ε ι))
    (p : A.U ε ι) (hp : p ∈ A.uQ ε s) (k : A.U ε ι) (hk : k ∈ A.uK ε ι) :
    A.uH ε s (p * k) = A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) := by
  have hb := hB E R A hA.toGoodL (ι ⊕ ι) (Sum.inl '' s)
  have hc : ContinuousOn (fun p : A.U ε ι => bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) (A.uQ ε s : Set (A.U ε ι)) :=
    hb.2.2.1.comp continuous_subtype_val.continuousOn fun x hx => hx
  have hv : ∀ p ∈ A.uQ ε s, p ∈ A.uK ε ι → A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1) = 0 :=
    fun p hp hk => hb.2.2.2.2.1 p.1 (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk)
  exact (hE (A.U ε ι) (A.uK ε ι) (A.uK ε ι) (A.uQ ε s) (fun p => A.lg (bdet (Sum.inl '' s : Set (ι ⊕ ι)) p.1)) hK
    (isClosed_uQ A ε s hb.1) hI
    (fun p hp q hq => by
      have := hb.2.1 p.1 (Subgroup.mem_subgroupOf.1 hp) q.1 (Subgroup.mem_subgroupOf.1 hq)
      simp only [Subgroup.coe_mul, this, hA.lgmul])
    (hA.lgcont.comp_continuousOn hc) hv hv).2 p hp k hk

end Ext

theorem leviS : BdetLaw → ExtLaw → GrpTop → LeviS := by
  intro hB hE hT E R _ _ _ _ _ _ _ A hA ι _ _ ε hI
  obtain ⟨-, -, -, hT2, -, -, hK⟩ := hT E R A hA ι ε
  have hbu := hB E R A hA.toGoodL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  refine ⟨piQ A ε, jQ A ε hA.σσ, ?_, ?_, iwa_inf A hA ε hI, ?_⟩
  · exact
      { contπ := continuous_piQ A ε
        contι := continuous_jQ A ε hA.σσ hA.σcont
        sect := piQ_jQ A ε hA.σσ
        par :=
          { closed := isClosed_uQ A ε _ hbu.1
            iwa := hI
            ch :=
              { mul := fun _ _ _ _ => by simp
                norm := fun _ _ => by simp
                rat := fun _ _ _ => rfl
                cont := continuousOn_const } }
        triv := fun _ => rfl
        πK := fun q hq => piP_mem_kGL A _ (Subgroup.mem_subgroupOf.1 hq)
        ιK := fun m hm => Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ m hm)
        πΓ := fun q hq => piP_mem_ratGL A hA.iinj _ (Subgroup.mem_subgroupOf.1 hq)
        ιΓ := fun m hm => Subgroup.mem_subgroupOf.2 (jG_mem_rat A hA.iinj hA.σi m hm) }
  · intro s
    refine ⟨fun g => ⟨fun h => ⟨h.2, (mem_uQ_iff A ε s ⟨g, h.2⟩).1 h.1⟩,
      fun ⟨hg, h⟩ => ⟨(mem_uQ_iff A ε s ⟨g, hg⟩).2 h, hg⟩⟩, fun q _ => ?_⟩
    have h1 : bdet (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) q.1.1 = Matrix.GeneralLinearGroup.det (piQ A ε q) := by
      rw [bdet_inl Set.univ _ (piQ A ε q) (fun _ _ => rfl)]
      exact (hB E R A hA.toGoodL ι Set.univ).2.2.2.2.2 _
    show ((A.χ (bdet (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) q.1.1) : Circle) : ℂ) =
      1 * ((A.χ (Matrix.GeneralLinearGroup.det (piQ A ε q)) : Circle) : ℂ)
    rw [h1, one_mul]
  · intro s q k hk
    have hinf := iwa_inf A hA ε hI s
    have hIs : Iwa (A.uQ ε s) (A.uK ε ι) := fun g => by
      obtain ⟨p, hp, k, hk, e⟩ := hinf g
      exact ⟨p, hp.1, k, hk, e⟩
    obtain ⟨p, hp, k', hk', e⟩ := hA.iwa ι s (piQ A ε q)
    obtain ⟨q', h1, h2⟩ := factor A ε hA.σσ q p k' e
    have hjk : ((jQ A ε hA.σσ k').1 : A.U ε ι) ∈ A.uK ε ι :=
      Subgroup.mem_subgroupOf.2 (jG_mem_k A hA.σO hA.σφ k' hk')
    have hq' : q'.1 ∈ A.uQ ε s := (mem_uQ_iff A ε s q').2 (h1 ▸ hp)
    rw [e, ht_GL hB hE A hA s p hp k' hk', h2, mul_assoc,
      ht_U hB hE A hA ε hK s hIs q'.1 hq' _ (mul_mem hjk hk),
      bdet_inl s _ (piQ A ε q') (fun _ _ => rfl), h1]

end GlobalTheory.CompanionTheory.RgEisLevi
