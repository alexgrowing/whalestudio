import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels

open scoped TensorProduct
open GlobalTheory.TateLimit

theorem UpperTheory.V.K.tensTors :
    ∀ (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H] (x : ℤ_[l] ⊗[ℤ] H), IsOfFinAddOrder x → x ∈ LinearMap.range (LinearMap.lTensor ℤ_[l] (AddCommGroup.torsion H).subtype.toIntLinearMap) := by
  intro l _ H _ x hx
  let T := AddCommGroup.torsion H
  let g : H →ₗ[ℤ] (H ⧸ T) := (QuotientAddGroup.mk' T).toIntLinearMap
  have hg : Function.Surjective g := QuotientAddGroup.mk'_surjective T
  have hex : Function.Exact T.subtype.toIntLinearMap g := by
    intro h
    constructor
    · intro hh
      exact ⟨⟨h, (QuotientAddGroup.eq_zero_iff h).1 hh⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact (QuotientAddGroup.eq_zero_iff _).2 t.2
  have hE := lTensor_exact ℤ_[l] hex hg
  haveI : IsAddTorsionFree (H ⧸ T) := inferInstance
  haveI : Module.Flat ℤ (H ⧸ T) := inferInstance
  obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx
  let m : ℤ_[l] →ₗ[ℤ] ℤ_[l] := n • LinearMap.id
  have hm : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : (n : ℤ_[l]) * a = 0 := by simpa [m] using ha
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) hn.ne'
    · exact h
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := H ⧸ T) m hm
  have h0 : LinearMap.lTensor ℤ_[l] g x = 0 := by
    apply hinj
    have : LinearMap.rTensor (H ⧸ T) m = n • LinearMap.id := by
      ext a b
      simp [m, ← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [map_zero, this, LinearMap.smul_apply, LinearMap.id_apply, ← map_nsmul, hnx, map_zero]
  exact (hE x).1 h0
