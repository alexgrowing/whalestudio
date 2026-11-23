import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cplFinite :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [CommRing B]
      [IsLocalRing B] [Algebra A B] [Module.Finite A B] (I : Ideal B), I ≠ ⊤ → IsAdicComplete I B := by
  intro A B _ _ _ _ _ _ _ _ I hI
  have hN : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hc : IsAdicComplete (maximalIdeal B) B := by
    exact GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A B
  have hle : I ≤ maximalIdeal B := le_maximalIdeal hI
  have hH : IsHausdorff I B := IsHausdorff.of_isLocalRing _ _ hI
  have hP : IsPrecomplete I B := by
    refine ⟨fun f hf => ?_⟩
    obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := f) (fun {m n} h =>
      (hf h).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hle m)))
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, ← Submodule.Quotient.mk_eq_zero]
    have hq : IsHausdorff (maximalIdeal B) (B ⧸ (I ^ n • (⊤ : Submodule B B))) :=
      IsHausdorff.of_isLocalRing _ _ (maximalIdeal.isMaximal B).ne_top
    refine hq.haus _ fun k => ?_
    rw [SModEq.zero]
    have h1 : f n - f (n + k) ∈ I ^ n • (⊤ : Submodule B B) := SModEq.sub_mem.1 (hf (Nat.le_add_right n k))
    have h2 : f (n + k) - L ∈ maximalIdeal B ^ k • (⊤ : Submodule B B) :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left k n)) (SModEq.sub_mem.1 (hL (n + k)))
    have e : f n - L = (f n - f (n + k)) + (f (n + k) - L) := by ring
    rw [e, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 h1, zero_add]
    have h3 := Submodule.mem_map_of_mem (f := (I ^ n • (⊤ : Submodule B B)).mkQ) h2
    rw [Submodule.map_smul''] at h3
    exact Submodule.smul_mono le_rfl le_top h3
  exact { }
