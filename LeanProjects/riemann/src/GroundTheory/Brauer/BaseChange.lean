import Mathlib
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
import GroundTheory.Brauer.BaseChangeCSA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

universe u v

section Equivalence

variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]

theorem IsBrauerEquivalent.baseChange {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (baseChangeCSA L A) (baseChangeCSA L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(baseChangeMatrix K L A (Fin n)).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans <|
      baseChangeMatrix K L B (Fin m)⟩⟩

end Equivalence

namespace BrauerGroup

section Hom

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

noncomputable def baseChangeFun : BrauerGroup.{u, u} K → BrauerGroup.{u, u} L :=
  Quotient.map (baseChangeCSA L) fun _ _ h ↦ IsBrauerEquivalent.baseChange L h

noncomputable def baseChange : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun := baseChangeFun K L
  map_one' := Quotient.sound <|
    isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.rid K L L)
  map_mul' := by
    rintro ⟨A⟩ ⟨B⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATensor L A B)

variable {K L} in

@[simp]
theorem baseChange_mk (A : CSA.{u, u} K) :
    baseChange K L ⟦A⟧ = ⟦baseChangeCSA L A⟧ := rfl

theorem baseChange_comp (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange K M := by
  ext x
  induction x using Quotient.inductionOn with
  | h A => exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATower L M A)

theorem baseChange_baseChange (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (x : BrauerGroup.{u, u} K) :
    baseChange L M (baseChange K L x) = baseChange K M x :=
  DFunLike.congr_fun (baseChange_comp K L M) x

end Hom

section Relative

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

noncomputable def relBrauer : Subgroup (BrauerGroup.{u, u} K) :=
  (baseChange K L).ker

variable {K L}

theorem mem_relBrauer_iff (x : BrauerGroup.{u, u} K) :
    x ∈ relBrauer K L ↔ baseChange K L x = 1 :=
  MonoidHom.mem_ker

theorem mk_mem_relBrauer_iff (A : CSA.{u, u} K) :
    ⟦A⟧ ∈ relBrauer K L ↔
      ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) := by
  rw [mem_relBrauer_iff, baseChange_mk, BrauerGroup.one_def, Quotient.eq]
  change IsBrauerEquivalent (baseChangeCSA L A) (oneCSA L) ↔ _
  have : IsArtinianRing (baseChangeCSA L A) := IsArtinianRing.of_finite L _
  obtain ⟨k, hk, D, _, _, _, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite L (baseChangeCSA L A)
  constructor
  · intro h
    obtain ⟨g⟩ := (isBrauerEquivalent_iff_nonempty_algEquiv e
      ((matrixFinOneAlgEquiv (K := L) L).symm)).mp h
    exact ⟨k, ⟨e.trans g.mapMatrix⟩⟩
  · rintro ⟨n, ⟨f⟩⟩
    have hn : n ≠ 0 := by
      rintro rfl
      exact one_ne_zero (f.injective (Subsingleton.elim _ _) : (1 : L ⊗[K] A) = 0)
    have : NeZero n := ⟨hn⟩
    exact isBrauerEquivalent_of_algEquiv_matrix (C := L) f
      ((matrixFinOneAlgEquiv (K := L) L).symm)

end Relative

end BrauerGroup

end GroundTheory.Brauer
