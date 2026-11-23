import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_ker_ss :
    ∀ {n : ℕ} {k E ι : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[k] Matrix ι ι k), IsSemisimpleRing r.range → ∀ x, x ∈ (Det.ofRep h r).ker ↔ r x = 0 := by
  intro n k E ι _ _ _ _ _ _ h r hss x
  rw [Det.mem_ker]
  constructor
  · intro hx
    obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
      (Ideal.span {(⟨r x, x, rfl⟩ : r.range)})
    have h1 : e ∈ Ideal.span {(⟨r x, x, rfl⟩ : r.range)} := hI ▸ Ideal.subset_span rfl
    have h2 : (⟨r x, x, rfl⟩ : r.range) ∈ Ideal.span {e} := hI ▸ Ideal.subset_span rfl
    obtain ⟨⟨a, u, rfl⟩, ha⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h2
    have ha' : r u * r x = (e : Matrix ι ι k) := congrArg Subtype.val ha
    have hb' : (b : Matrix ι ι k) * (e : Matrix ι ι k) = r x := congrArg Subtype.val hb
    have he' : (e : Matrix ι ι k) * e = e := congrArg Subtype.val he
    have h3 : (Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1)).det = (Det.repS r k 1).det :=
      hx k 1 (1 ⊗ₜ (-u)) 1
    have h4 : Det.repS r k (1 + (1 ⊗ₜ (-u)) * (1 ⊗ₜ x) * 1) = 1 - (e : Matrix ι ι k) := by
      rw [map_add, map_mul, map_mul, map_one, Det.repS_tmul, Det.repS_tmul, ← ha']
      simp [sub_eq_add_neg]
    rw [h4, map_one, Matrix.det_one] at h3
    have h5 : IsUnit (1 - (e : Matrix ι ι k)) := by
      rw [Matrix.isUnit_iff_isUnit_det, h3]; exact isUnit_one
    have h6 : (e : Matrix ι ι k) = 0 := by
      apply h5.mul_left_cancel
      rw [sub_mul, one_mul, he', sub_self, mul_zero]
    rw [← hb', h6, mul_zero]
  · intro hx S _ _ y u v
    show (Det.repS r S (y + u * (1 ⊗ₜ x) * v)).det = (Det.repS r S y).det
    rw [map_add, map_mul, map_mul, Det.repS_tmul, hx]
    simp
