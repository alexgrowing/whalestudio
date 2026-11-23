import ReciprocityTheory.DualLattices.LenIdStatement
import ReciprocityTheory.DualLattices.MemOfSumSingleEqZero

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g m : ℕ}

def inclE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] qE εL i j where
  toFun x := ⟨Sum.elim (0 : Fin g → R) (x : Fin g → R), by
    refine ⟨?_, ?_⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inl ∈ LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)
      exact ⟨0, by funext k; simp⟩
    · show (Sum.elim (0 : Fin g → R) (x : Fin g → R)) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i))
      exact x.2⟩
  map_add' x y := by ext k; rcases k with k | k <;> simp
  map_smul' c x := by ext k; rcases k with k | k <;> simp

def projE (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    qE εL i j →ₗ[R] LinearMap.range (Matrix.mulVecLin (εL j)ᵀ) where
  toFun q := ⟨(q : Fin g ⊕ Fin g → R) ∘ Sum.inl, q.2.1⟩
  map_add' x y := rfl
  map_smul' c x := rfl

abbrev sxE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    Submodule R (qE εL i (π i)) :=
  ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
    (qE εL i (π i)).subtype

abbrev yModE (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  LinearMap.range (Matrix.mulVecLin (εL i)) ⧸ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i))

private theorem fromRows_mulVec_comp_inl (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inl = Ht *ᵥ w := by
  funext k
  rfl

private theorem fromRows_mulVec_comp_inr (Ht Bt : Matrix (Fin g) (Ix g) R) (w : Ix g → R) :
    (fromRows Ht Bt *ᵥ w) ∘ Sum.inr = Bt *ᵥ w := by
  funext k
  rfl

private theorem coe_inclE_eq_elim_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    ((inclE εL i j x : qE εL i j) : Fin g ⊕ Fin g → R) =
      Sum.elim (0 : Fin g → R) (x : Fin g → R) := rfl

private theorem coe_projE_eq_comp_inl (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (q : qE εL i j) :
    ((projE εL i j q : LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)) : Fin g → R) =
      (q : Fin g ⊕ Fin g → R) ∘ Sum.inl := rfl

private theorem projE_inclE_eq_zero (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m)
    (x : LinearMap.range (Matrix.mulVecLin (εL i))) :
    projE εL i j (inclE εL i j x) = 0 := by
  apply Subtype.ext
  funext k
  rfl

private theorem sxE_le_comap_projE (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    sxE Ht Bt εT εL π i ≤
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype).comap (projE εL i (π i)) := by
  intro q hq
  obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hq)
  refine Submodule.mem_comap.mpr (Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨w, hw, ?_⟩))
  rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, ← fromRows_mulVec_comp_inl Ht Bt w]
  rw [Submodule.subtype_apply, Matrix.mulVecLin_apply] at hwq
  rw [hwq]

theorem xModE_len {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hS2 : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (Ht Bt : Matrix (Fin g) (Ix g) R) (εT : Fin m → Matrix (Ix g) (Ix g) R)
    (εL : Fin m → Matrix (Fin g) (Fin g) R) (π : Equiv.Perm (Fin m)) (i : Fin m)
    (hHt : Ht * εT i = (εL (π i))ᵀ * Ht) (hBt : Bt * εT i = εL i * Bt) {y c₂ : NNReal}
    (hy : HasLen v R (yModE Ht Bt εT εL π i) y)
    (hc : HasLen v R (cokE Ht εT εL (π i) i) c₂) :
    HasLen v R (xModE Ht Bt εT εL π i) (y * c₂) := by
  refine hasLen_ext hS2
    (Submodule.mapQ ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i)))
      (sxE Ht Bt εT εL π i) (inclE εL i (π i)) le_rfl)
    (Submodule.mapQ (sxE Ht Bt εT εL π i)
      (((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin Ht)).comap
        (LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)).subtype)
      (projE εL i (π i)) (sxE_le_comap_projE Ht Bt εT εL π i))
    ?_ ?_ ?_ hy hc
  · intro a b hab
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub]
    exact hab
  · intro z
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨Submodule.Quotient.mk ⟨Sum.elim (z : Fin g → R) (0 : Fin g → R), by
      refine ⟨?_, ?_⟩
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inl ∈
          LinearMap.range (Matrix.mulVecLin (εL (π i))ᵀ)
        exact z.2
      · show (Sum.elim (z : Fin g → R) (0 : Fin g → R)) ∘ Sum.inr ∈
          LinearMap.range (Matrix.mulVecLin (εL i))
        exact ⟨0, by funext k; simp⟩⟩, ?_⟩
    rw [Submodule.mapQ_apply]
    exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
  · apply le_antisymm
    · intro x hx
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        projE_inclE_eq_zero]
      exact Submodule.zero_mem _
    · intro x hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨w, hw, hwq⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
      rw [Submodule.subtype_apply, coe_projE_eq_comp_inl, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hwq
      have hB' : Bt *ᵥ (εT i *ᵥ u) ∈ LinearMap.range (Matrix.mulVecLin (εL i)) :=
        ⟨Bt *ᵥ u, by rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBt]⟩
      have hq2 : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr ∈ LinearMap.range (Matrix.mulVecLin (εL i)) := q.2.2
      have hr : (q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u) ∈
          LinearMap.range (Matrix.mulVecLin (εL i)) := Submodule.sub_mem _ hq2 hB'
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hr⟩, ?_⟩
      rw [Submodule.mapQ_apply, eq_comm, Submodule.Quotient.eq]
      refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨(εT i).mulVecLin u, ⟨u, rfl⟩, ?_⟩)
      rw [Submodule.subtype_apply, Submodule.coe_sub, coe_inclE_eq_elim_zero, Matrix.mulVecLin_apply,
        Matrix.mulVecLin_apply]
      funext k
      rcases k with k | k
      · have hF := congrFun (fromRows_mulVec_comp_inl Ht Bt (εT i *ᵥ u)) k
        have hk := congrFun hwq k
        simp only [Function.comp_apply] at hF hk
        rw [Pi.sub_apply, hF, Sum.elim_inl, Pi.zero_apply, sub_zero]
        exact hk
      · have hF := congrFun (fromRows_mulVec_comp_inr Ht Bt (εT i *ᵥ u)) k
        simp only [Function.comp_apply] at hF
        rw [Pi.sub_apply, hF, Sum.elim_inr]
        show _ = _ - (((q : Fin g ⊕ Fin g → R) ∘ Sum.inr - Bt *ᵥ (εT i *ᵥ u)) k)
        rw [Pi.sub_apply, Function.comp_apply, sub_sub_cancel]

def LenIdBStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      ∃ y : NNReal, HasLen v R (yModE Ht Bt εT εL π i) y ∧ y * c₁ = v (algebraMap R C cp) ^ d

theorem lenId_of
    (hS2 : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R),
      HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)))
    (hB : LenIdBStatement) : LenIdStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt hεE i d hd
    c₁ c₂ hc₁ hc₂
  obtain ⟨y, hy, hyc⟩ := hB C v R hv g m Ht Bt E cp hcp hE hform εT εL π hπ hεT hsumT hεL hsumL hHt hBt
    hεE i d hd c₁ hc₁
  refine ⟨y * c₂, xModE_len (hS2 C v R hv) Ht Bt εT εL π i (hHt i) (hBt i) hy hc₂, ?_⟩
  rw [mul_right_comm, hyc]

end ReciprocityTheory.PGsh.Up
