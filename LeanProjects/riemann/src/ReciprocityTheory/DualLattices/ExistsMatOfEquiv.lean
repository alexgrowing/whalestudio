import ReciprocityTheory.DualLattices.MemDualLat
import ReciprocityTheory.DualLattices.MapTensorSpan

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

section Hopf

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def pullHopf {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N] [AddCommGroup X]
    [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) : HopfOrder (C := C) R X where
  carrier := AA.carrier.map (LinearMap.funLeft R C ψ)
  lat := hlat
  le_int := by
    rintro _ ⟨f, hf, rfl⟩ x
    exact AA.le_int hf (ψ x)
  one_mem := ⟨1, AA.one_mem, rfl⟩
  mul_mem := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, AA.mul_mem f g hf hg, rfl⟩
  comul := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← SecondCohomologyLattice.map_tensorSpan (⇑ψ) AA.carrier]
    refine ⟨addPull R N f, AA.comul f hf, ?_⟩
    funext x
    simp [addPull, LinearMap.funLeft_apply, map_add]
  antipode := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨fun x => f (-x), AA.antipode f hf, funext fun x => by simp [LinearMap.funLeft_apply]⟩

theorem pullHopf_carrier {N X : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    [AddCommGroup X] [Fintype X] [DecidableEq X] (ψ : X →+ N) (AA : HopfOrder (C := C) R N)
    (hlat : IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ))) :
    (pullHopf ψ AA hlat).carrier = AA.carrier.map (LinearMap.funLeft R C ψ) := rfl

theorem isLat_map_equiv {X K : Type} [Fintype X] [DecidableEq X] {_ : Fintype K} {_ : DecidableEq K}
    (e : X ≃ K) {M : Submodule R (K → C)} (hM : IsLat R M) :
    IsLat R (M.map (LinearMap.funLeft R C e)) := by
  obtain ⟨B, hB, rfl⟩ := hM
  refine ⟨B.submatrix e e, by rwa [Matrix.det_submatrix_equiv_self], ?_⟩
  rw [Submodule.map_span, ← Set.range_comp]
  have h1 : (fun j x => (B.submatrix e e) x j) =
      (⇑(LinearMap.funLeft R C e) ∘ fun j x => B x j) ∘ e := by
    funext j x
    rfl
  rw [h1, e.surjective.range_comp]

theorem hopfLat {K : Type} {_ : AddCommGroup K} {_ : Fintype K} {_ : DecidableEq K}
    (A : HopfOrder (C := C) R K) : IsLat R A.carrier := A.lat

theorem isLat_pull (v : Valuation C NNReal) (hv : v.Integers R) {N X : Type} [AddCommGroup N]
    [Fintype N] [DecidableEq N] [AddCommGroup X] [Fintype X] [DecidableEq X]
    (ψ : X →+ N) (hψ : Function.Injective ψ) (AA : HopfOrder (C := C) R N) :
    IsLat R (AA.carrier.map (LinearMap.funLeft R C ψ)) := by
  classical
  obtain ⟨⟨AK, hAK⟩, -⟩ := h2 C R v hv N ψ.range AA
  let e := AddMonoidHom.ofInjective hψ
  have hmap : (AA.carrier.map (resK ψ.range)).map (LinearMap.funLeft R C e.toEquiv) =
      AA.carrier.map (LinearMap.funLeft R C ψ) := by
    rw [← Submodule.map_comp]
    congr 1
  rw [← hmap, ← hAK]
  exact isLat_map_equiv e.toEquiv (hopfLat AK)

end Hopf

section Split

variable {S : Type} [CommRing S] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

theorem exists_split (e : Matrix n n S) (he : e * e = e) (B : Matrix n k S)
    (hr : LinearMap.range B.mulVecLin = LinearMap.range e.mulVecLin)
    (hk : LinearMap.ker B.mulVecLin = ⊥) : ∃ L : Matrix k n S, L * B = 1 ∧ B * L = e := by
  have hcol : ∀ j : n, ∃ c : k → S, B *ᵥ c = e *ᵥ Pi.single j 1 := by
    intro j
    have hmem : e *ᵥ Pi.single j 1 ∈ LinearMap.range B.mulVecLin := by
      rw [hr]
      exact ⟨_, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc⟩
  choose c hc using hcol
  let L : Matrix k n S := Matrix.of fun i j => c j i
  have hBL : B * L = e := by
    ext i j
    have h1 := congrFun (hc j) i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h1
    rw [← h1]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, L]
  have heB : e * B = B := by
    ext i j
    have hmem : B *ᵥ Pi.single j 1 ∈ LinearMap.range e.mulVecLin := by
      rw [← hr]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    have h2 : e *ᵥ (B *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
      rw [← hw]
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h2
    simpa [Matrix.col_apply] using congrFun h2 i
  have hinj : Function.Injective B.mulVecLin := LinearMap.ker_eq_bot.1 hk
  refine ⟨L, ?_, hBL⟩
  ext i j
  have h3 : B *ᵥ ((L * B) *ᵥ Pi.single j 1) = B *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hBL, heB]
  have h4 : (L * B) *ᵥ Pi.single j 1 = Pi.single j 1 := hinj h3
  rw [Matrix.mulVec_single_one] at h4
  have h5 := congrFun h4 i
  simp only [Matrix.col_apply] at h5
  rw [h5, Matrix.one_apply, Pi.single_apply]

end Split

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
