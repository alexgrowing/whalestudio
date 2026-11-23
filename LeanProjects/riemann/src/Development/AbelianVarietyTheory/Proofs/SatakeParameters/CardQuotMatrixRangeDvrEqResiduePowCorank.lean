import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EsymmInvMulEsymmCard

open GlobalTheory.LatHecke GlobalTheory.SatakeInv

namespace GlobalTheory.IdxRank

theorem mem_smul_top_of_forall_mem {O : Type} [CommRing O] (I : Ideal O) {r : ℕ}
    (z : Fin r → O) (hz : ∀ i, z i ∈ I) : z ∈ I • (⊤ : Submodule O (Fin r → O)) := by
  have h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial

theorem card_quot_range (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O)
    (hA : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤
      LinearMap.range A.mulVecLin) :
    Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) =
      qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  classical
  set F := IsLocalRing.ResidueField O with hF
  set res : O →+* F := IsLocalRing.residue O with hres
  set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb
  set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR
  let π : (Fin r → O) →ₗ[O] (Fin r → F) := (Algebra.linearMap O F).compLeft (Fin r)
  have hπ : ∀ x i, π x i = res (x i) := fun x i => rfl
  have hπs : Function.Surjective π := by
    intro y
    refine ⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩
    ext i
    exact (IsLocalRing.residue_surjective (y i)).choose_spec
  have hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x) := by
    intro x
    ext i
    have h2 : π x = res ∘ x := rfl
    rw [h2, hπ]
    exact RingHom.map_mulVec res A x i
  let φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R) := (R.mkQ.restrictScalars O).comp π
  have hφs : Function.Surjective φ :=
    (Submodule.mkQ_surjective R).comp hπs
  have hker : LinearMap.ker φ = LinearMap.range A.mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : π x ∈ R := by
        have : R.mkQ (π x) = 0 := hx
        simpa using this
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨y', rfl⟩ := hπs y
      have hy2 : π (A.mulVec y') = π x := by
        rw [hπA]; exact hy
      have hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin := by
        apply hA
        apply mem_smul_top_of_forall_mem
        intro i
        have h1 : π (x - A.mulVec y') i = 0 := by
          rw [map_sub, hy2, sub_self]; rfl
        rw [hπ] at h1
        exact (IsLocalRing.residue_eq_zero_iff _).1 h1
      have : x = (x - A.mulVec y') + A.mulVecLin y' := by
        simp
      rw [this]
      exact Submodule.add_mem _ hz ⟨y', rfl⟩
    · rintro ⟨y, rfl⟩
      show R.mkQ (π (A.mulVec y)) = 0
      rw [hπA]
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨π y, rfl⟩
  have e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hφs)).toEquiv
  rw [Nat.card_congr e]
  have hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r := by
    have := Submodule.finrank_quotient_add_finrank R
    simpa using this
  have hrank : Ab.rank = Module.finrank F R := rfl
  have hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank := by
    omega
  have : Finite ((Fin r → F) ⧸ R) := Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  rfl

end GlobalTheory.IdxRank
