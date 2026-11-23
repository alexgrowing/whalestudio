import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameRedEquivalence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle

noncomputable section

namespace GlobalTheory.IntPair

open NumberField Matrix Formalism.BasicNotions Formalism.HermitianLatticeCounting.S6 GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IntTerm GlobalTheory.SA
open GlobalTheory.HermLat (perp rs smulLat imLat isomGrp mem_isomGrp IsUnimod)

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {r g : ℕ}

def co (x : S.V) : Fin S.rank → E := S.frame.equivFun x

def latV (Λ : Submodule (𝓞 E) (Fin S.rank → E)) : Submodule (𝓞 E) S.V :=
  Λ.comap ((S.frame.equivFun.restrictScalars (𝓞 E) : S.V ≃ₗ[𝓞 E] (Fin S.rank → E)) : S.V →ₗ[𝓞 E] _)

def matOf (s : S.V ≃ₗ[E] S.V) : Matrix (Fin S.rank) (Fin S.rank) E :=
  LinearMap.toMatrix S.frame S.frame (s : S.V →ₗ[E] S.V)

variable {S} {T T' : E} {A : Matrix (Fin S.rank) (Fin (r + 1)) E} {Λ Λ₁ : Submodule (𝓞 E) (Fin S.rank → E)}
  {s t : S.V ≃ₗ[E] S.V} {F F' G : FlagD (ofHSpace S) r}

theorem co_surjective : Function.Surjective (co S) := S.frame.equivFun.surjective

theorem mem_latV (x : S.V) : x ∈ latV S Λ ↔ co S x ∈ Λ := Iff.rfl

theorem B_eq (x y : S.V) : (ofHSpace S).B x y = form (starRingEnd E) S.gram (co S x) (co S y) := by
  rw [ofHSpace_B, hT_eq_sum, form, Matrix.dotProduct_mulVec]; rfl

theorem isUnimod_latV (h : SelfDual (starRingEnd E) S.gram Λ) : IsUnimod (ofHSpace S) (latV S Λ) := by
  have hfg : (latV S Λ).FG := by
    rw [latV, Submodule.comap_equiv_eq_map_symm]; exact h.1.map _
  have hd (x : S.V) : x ∈ latV S Λ ↔ ∀ y ∈ latV S Λ, (ofHSpace S).B x y ∈ (1 : Submodule (𝓞 E) E) := by
    rw [mem_latV, h.2, co_surjective.forall]
    simp only [← B_eq, mem_latV, Submodule.mem_one, RingHom.mem_range]
  have hs : Submodule.span E (latV S Λ : Set S.V) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨N, hN⟩ := hfg
    obtain ⟨d, hd'⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) N
      fun y => star ((ofHSpace S).B x y)
    have hd0 : ((d : 𝓞 E) : E) ≠ 0 := by simpa using nonZeroDivisors.ne_zero d.2
    rw [← Submodule.smul_mem_iff _ (star_ne_zero.2 hd0)]
    refine Submodule.subset_span ((hd _).2 fun y hy => ?_)
    have k : star ((ofHSpace S).B (star ((d : 𝓞 E) : E) • x) y) ∈ (1 : Submodule (𝓞 E) E) := by
      rw [(ofHSpace S).herm]
      rw [← hN] at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, hc⟩ := hd' y hy
        refine Submodule.mem_one.2 ⟨c, hc.trans ?_⟩
        rw [(ofHSpace S).herm, LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]; rfl
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [int_smul_eq, map_smul (ofHSpace S).B, LinearMap.smul_apply]
        exact Submodule.smul_mem _ c ha
    obtain ⟨c, hc⟩ := Inhab.map_mem_int (starRingEnd E) (Submodule.mem_one.1 k)
    exact Submodule.mem_one.2 ⟨c, hc.trans (star_star _)⟩
  refine ⟨⟨⟨_, hfg, by simp⟩, hs⟩, Submodule.ext fun x => ?_⟩
  rw [GlobalTheory.HermLat.mem_dual_iff, hs, ← hd]
  simp

theorem coMat_mulVec {m : ℕ} (x : Fin m → S.V) (c : Fin m → E) : coMat S x *ᵥ c = co S (∑ a, c a • x a) := by
  ext i
  simp [coMat, co, Matrix.mulVec, dotProduct, mul_comm]

def flagOf (h : IsFrame (starRingEnd E) S.gram T A) (hT : T ≠ 0) : FlagD (ofHSpace S) r :=
  have k (a b : Fin (r + 1)) : (ofHSpace S).B (S.frame.equivFun.symm fun i => A i a)
      (S.frame.equivFun.symm fun i => A i b) = TF r T b a := by
    rw [B_eq, co, co, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, ← h.2, pairM, Matrix.mul_assoc]
    rfl
  { e := fun a => S.frame.equivFun.symm fun i => A i a
    T := T
    indep := by
      refine LinearIndependent.comp (v := fun a : Fin (r + 1) => S.frame.equivFun.symm fun i => A i a) ?_ _
        (Fin.castSucc_injective r)
      refine LinearIndependent.map' (v := A.col) ?_ _ S.frame.equivFun.symm.ker
      obtain ⟨L, hL⟩ := h.1
      refine Matrix.mulVec_injective_iff.1 fun c d e => ?_
      simpa [Matrix.mulVec_mulVec, hL] using congrArg (L *ᵥ ·) e
    iso := fun a b => by simp only [k]; simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
    zperp := fun a => by simp only [k]; simp [TF, Matrix.diagonal_apply, (Fin.castSucc_ne_last a).symm]
    zz := by simp only [k]; simp [TF]
    hT := hT }

end GlobalTheory.IntPair

end
