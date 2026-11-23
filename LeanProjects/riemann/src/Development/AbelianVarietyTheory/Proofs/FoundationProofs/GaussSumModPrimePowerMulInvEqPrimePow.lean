import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvPrim
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp

theorem sum_mulChar_eq_sum_units {K : Type} [CommRing K] {n : ℕ} (ψ : MulChar (ZMod n) K)
    (f : ZMod n → K) [Fintype (ZMod n)] :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun a _ h => by
    by_contra hu; exact h (by rw [MulChar.map_nonunit ψ hu, zero_mul]))]
  refine (Finset.sum_nbij' (fun b : (ZMod n)ˣ => (b : ZMod n)) (fun a => if h : IsUnit a then h.unit else 1)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro b _; simp
  · intro a _; simp
  · intro b _; simp
  · intro a ha
    have hu : IsUnit a := (Finset.mem_filter.1 ha).2
    simp [hu]
  · intro b _; rfl

theorem gSum_mul_gSum_inv_prim : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l)
    (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive →
    gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  intro l _ m z ψ hz hψ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e : AddChar (ZMod (l ^ m)) (Qbar l) := AddChar.zmodChar (l ^ m) hz.pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root (l ^ m) hz
  have h1 : gSum m z ψ = gaussSum ψ e := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.zmodChar_apply]
  have h2 : gSum m z⁻¹ ψ⁻¹ = gaussSum ψ⁻¹ e⁻¹ := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.inv_apply', AddChar.zmodChar_apply, inv_pow]
  rw [h1, h2, GlobalTheory.KummerEisensteinGalois.gaussSum_mul_gaussSum_inv_prim hψ he]
  push_cast
  rfl

end GlobalTheory.KZ.Cmp
