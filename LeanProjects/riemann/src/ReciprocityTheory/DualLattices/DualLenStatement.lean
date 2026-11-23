import ReciprocityTheory.DualLattices.ExistsFromRowsMulVecIff
import ReciprocityTheory.DualLattices.HasLenCokerDet

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def zSub {R : Type} [CommRing R] {d : ℕ} {κ : Type} [Fintype κ] (A : Matrix (Fin d) κ R) (c : R) :
    Submodule R (Fin d → R) where
  carrier := {y | ∃ z, Aᵀ *ᵥ y = c • z}
  add_mem' := by
    rintro y y' ⟨z, hz⟩ ⟨z', hz'⟩
    exact ⟨z + z', by rw [mulVec_add, hz, hz', smul_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a y ⟨z, hz⟩
    exact ⟨a • z, by rw [mulVec_smul, hz, smul_comm]⟩

def DualLenStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (d : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix (Fin d) κ R)
    (c : R), c ≠ 0 → (∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) →
    ∀ c₁ : NNReal, HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ →
      ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d

section Coord

variable {R : Type} [CommRing R] {g d : ℕ} (P : Matrix (Fin g) (Fin g) R) (hP : P * P = P)
  (φ : LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R))

def matU : Matrix (Fin g) (Fin d) R := Matrix.of fun k l => ((φ.symm (Pi.single l 1)) : Fin g → R) k

def matV : Matrix (Fin d) (Fin g) R :=
  Matrix.of fun l k => φ ⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ l

lemma sum_single' {n : ℕ} (y : Fin n → R) : y = ∑ l, y l • (Pi.single l 1 : Fin n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

include hP in
lemma P_fix (x : Fin g → R) (hx : x ∈ LinearMap.range (Matrix.mulVecLin P)) : P *ᵥ x = x := by
  obtain ⟨w, rfl⟩ := hx
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]

lemma matU_mulVec (y : Fin d → R) : matU P φ *ᵥ y = (φ.symm y : Fin g → R) := by
  conv_rhs => rw [sum_single' y]
  rw [map_sum]
  funext k
  simp [matU, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma matV_mulVec (w : Fin g → R) :
    matV P φ *ᵥ w = φ ⟨P *ᵥ w, ⟨_, rfl⟩⟩ := by
  have hw : (⟨P *ᵥ w, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) =
      ∑ k, w k • (⟨P *ᵥ Pi.single k 1, ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    conv_lhs => rw [sum_single' w]
    rw [show P *ᵥ (∑ k, w k • (Pi.single k 1 : Fin g → R)) =
        Matrix.mulVecLin P (∑ k, w k • (Pi.single k 1 : Fin g → R)) from rfl, map_sum]
    simp only [map_smul, Matrix.mulVecLin_apply]
  rw [hw, map_sum]
  simp only [LinearEquiv.map_smul]
  funext l
  simp only [Matrix.mulVec, dotProduct, matV, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

include hP in
lemma matV_matU : matV P φ * matU P φ = 1 := by
  have key : ∀ y, (matV P φ * matU P φ) *ᵥ y = y := by
    intro y
    rw [← Matrix.mulVec_mulVec, matU_mulVec, matV_mulVec]
    have e : (⟨P *ᵥ (φ.symm y : Fin g → R), ⟨_, rfl⟩⟩ : LinearMap.range (Matrix.mulVecLin P)) = φ.symm y :=
      Subtype.ext (P_fix P hP _ (φ.symm y).2)
    rw [e, LinearEquiv.apply_symm_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using this

lemma matU_matV : matU P φ * matV P φ = P := by
  have key : ∀ w, (matU P φ * matV P φ) *ᵥ w = P *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, matV_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply]
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Coord

theorem lenIdB_of (hPL : DualLenStatement) : LenIdBStatement := by
  intro C _ v R _ _ hv g m Ht Bt E cp hcp hE hform εT εL π hπ hTo hTs hLo hLs hHt hBt hadj i d hd
    c₁ hc₁
  haveI : IsDomain R := Function.Injective.isDomain _ hv.hom_inj
  obtain ⟨φ⟩ := hd
  have hP : εL i * εL i = εL i := by rw [hLo, if_pos rfl]
  set U := matU (εL i) φ with hU
  set V := matV (εL i) φ with hV
  have hVU : V * U = 1 := matV_matU (εL i) hP φ
  have hUV : U * V = εL i := matU_matV (εL i) φ
  have hHtT : (εT (π i))ᵀ * Htᵀ = Htᵀ * εL i := by
    have h := congrArg transpose (hHt (π i))
    rw [hπ i, transpose_mul, transpose_mul, transpose_transpose] at h
    exact h
  set A : Matrix (Fin d) (Ix g) R := Uᵀ * Ht * εT (π i) with hA
  have hmemT : ∀ w, Vᵀ *ᵥ w ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
    intro w
    refine ⟨Vᵀ *ᵥ w, ?_⟩
    show (εL i)ᵀ *ᵥ (Vᵀ *ᵥ w) = Vᵀ *ᵥ w
    rw [mulVec_mulVec, ← transpose_mul, ← hUV, ← Matrix.mul_assoc, hVU, Matrix.one_mul]
  have hfixT : ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), (εL i)ᵀ *ᵥ f = f := by
    rintro f ⟨z, rfl⟩
    show (εL i)ᵀ *ᵥ ((εL i)ᵀ *ᵥ z) = (εL i)ᵀ *ᵥ z
    rw [mulVec_mulVec, ← transpose_mul, hP]
  let ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) ≃ₗ[R] (Fin d → R) :=
    { toFun := fun f => Uᵀ *ᵥ (f : Fin g → R)
      invFun := fun y => ⟨Vᵀ *ᵥ y, hmemT y⟩
      map_add' := fun f f' => by simp [mulVec_add]
      map_smul' := fun a f => by simp [mulVec_smul]
      left_inv := fun f => by
        apply Subtype.ext
        show Vᵀ *ᵥ (Uᵀ *ᵥ (f : Fin g → R)) = f
        rw [mulVec_mulVec, ← transpose_mul, hUV, hfixT f f.2]
      right_inv := fun y => by
        show Uᵀ *ᵥ (Vᵀ *ᵥ y) = y
        rw [mulVec_mulVec, ← transpose_mul, hVU, transpose_one, one_mulVec] }
  have hmapC : (((LinearMap.range (Matrix.mulVecLin (εT (π i)))).map (Matrix.mulVecLin Ht)).comap
      (LinearMap.range (Matrix.mulVecLin (εL i)ᵀ)).subtype).map
        (ψ : LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) →ₗ[R] (Fin d → R)) =
      LinearMap.range A.mulVecLin := by
    ext y
    constructor
    · rintro ⟨f, ⟨_, ⟨t, rfl⟩, hft⟩, rfl⟩
      refine ⟨t, ?_⟩
      show A *ᵥ t = Uᵀ *ᵥ (f : Fin g → R)
      have hft' : Ht *ᵥ (εT (π i) *ᵥ t) = (f : Fin g → R) := hft
      rw [← hft']
      show A *ᵥ t = Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t))
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨t, rfl⟩
      have hmem : Ht *ᵥ (εT (π i) *ᵥ t) ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ) := by
        refine ⟨Ht *ᵥ t, ?_⟩
        show (εL i)ᵀ *ᵥ (Ht *ᵥ t) = Ht *ᵥ (εT (π i) *ᵥ t)
        rw [mulVec_mulVec, mulVec_mulVec, hHt (π i), hπ i]
      refine ⟨⟨_, hmem⟩, ⟨_, ⟨t, rfl⟩, rfl⟩, ?_⟩
      show Uᵀ *ᵥ (Ht *ᵥ (εT (π i) *ᵥ t)) = A *ᵥ t
      rw [hA, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hcA : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁ :=
    hasLen_of_equiv (Submodule.Quotient.equiv _ _ ψ hmapC).symm hc₁
  have hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = cp • w := by
    intro w
    obtain ⟨t, ht⟩ := cok_kill hcp hE hform εT εL π i (hπ i) hHt _ (hmemT w)
    refine ⟨t, ?_⟩
    rw [hA, ← mulVec_mulVec, ← mulVec_mulVec, ht, mulVec_smul, mulVec_mulVec, ← transpose_mul,
      hVU, transpose_one, one_mulVec]
  obtain ⟨y, hy, hyc⟩ := hPL C v R hv d (Ix g) A cp hcp hkill c₁ hcA
  have hmapY : ((sxE Ht Bt εT εL π i).comap (inclE εL i (π i))).map
      (φ : LinearMap.range (Matrix.mulVecLin (εL i)) →ₗ[R] (Fin d → R)) = zSub A cp := by
    have key : ∀ x : LinearMap.range (Matrix.mulVecLin (εL i)),
        x ∈ (sxE Ht Bt εT εL π i).comap (inclE εL i (π i)) ↔ φ x ∈ zSub A cp := by
      intro x
      have hx : εL i *ᵥ (x : Fin g → R) = x := P_fix (εL i) hP _ x.2
      have hAx : Aᵀ *ᵥ φ x = Htᵀ *ᵥ (x : Fin g → R) := by
        have hAT : Aᵀ = (εT (π i))ᵀ * Htᵀ * U := by
          rw [hA, transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc]
        rw [hAT, hHtT, ← mulVec_mulVec, ← mulVec_mulVec, matU_mulVec, LinearEquiv.symm_apply_apply,
          hx]
      rw [Submodule.mem_comap]
      show (∃ s, s ∈ LinearMap.range (Matrix.mulVecLin (εT i)) ∧
          fromRows Ht Bt *ᵥ s = Sum.elim (0 : Fin g → R) (x : Fin g → R)) ↔ ∃ z, Aᵀ *ᵥ φ x = cp • z
      rw [hAx, ← exists_fromRows_mulVec_iff hcp hE hform εT εL π i (hHt i) (hBt i) _ hx]
      constructor
      · rintro ⟨_, ⟨t, rfl⟩, h⟩; exact ⟨t, h⟩
      · rintro ⟨t, h⟩; exact ⟨_, ⟨t, rfl⟩, h⟩
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (key x).1 hx
    · intro hz
      refine ⟨φ.symm z, (key _).2 (by rwa [LinearEquiv.apply_symm_apply]), ?_⟩
      exact LinearEquiv.apply_symm_apply φ z
  exact ⟨y, hasLen_of_equiv (Submodule.Quotient.equiv _ _ φ hmapY) hy, hyc⟩

end ReciprocityTheory.PGsh.Up
