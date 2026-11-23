import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.LayerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem lu_key (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ)
    [Fact l.Prime] (hmu : HasMuQ l L) (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω]
    [IsScalarTower L L₁ Ω] [IsCyclotomicExtension {l ^ n} L L₁] :
    galOf L L₁ Ω = layU l L Ω (n - cZero l L) ∧ Module.finrank L L₁ = l ^ (n - cZero l L) := by
  haveI : IsAlgClosure L₁ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.tower_top (K := L) L₁⟩
  have h1 : galOf L L₁ Ω = Un L Ω l n := by
    rw [galOfCyc L Ω l n L L₁, galOf_self]
  have h2 : Un L Ω l n = layU l L Ω (n - cZero l L) := by
    rcases le_total n (cZero l L) with h | h
    · rw [((muQ L Ω l).2.1 n).2 h, layU, ((muQ L Ω l).2.1 _).2 (by omega)]
    · rw [layU, Nat.add_sub_cancel' h]
  refine ⟨h1.trans h2, ?_⟩
  rw [← (galEmbTop L L₁ Ω).2.2, h1, h2, (layerGen L Ω l hmu).1]

theorem UpperTheory.V.Tower.layerUniq :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, IsLayer l m L (layF l L Ω m)) ∧
        (∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω] [IsScalarTower L L₁ Ω], IsLayer l m L L₁ → galOf L L₁ Ω = layU l L Ω m) ∧
        ∀ (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁], IsCyclotomicExtension {l ^ n} L L₁ → IsLayer l (n - cZero l L) L L₁ := by
  intro L Ω _ _ _ _ _ l hl hmu
  refine ⟨fun m => ?_, fun m L₁ _ _ _ _ _ h => ?_, fun n L₁ _ _ _ h => ?_⟩
  · haveI h := (fnCyc L Ω l (cZero l L + m)).1
    refine ⟨⟨_, h⟩, ?_⟩
    have := (lu_key L Ω l hmu (cZero l L + m) (layF l L Ω m)).2
    rwa [Nat.add_sub_cancel_left] at this
  · obtain ⟨⟨k, hk⟩, hf⟩ := h
    obtain ⟨h1, h2⟩ := lu_key L Ω l hmu k L₁
    rw [h1, Nat.pow_right_injective hl.out.two_le (h2.symm.trans hf)]
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
    haveI : FiniteDimensional L L₁ := Module.Finite.of_restrictScalars_finite ℚ L L₁
    let f : L₁ →ₐ[L] Ω := IsAlgClosed.lift
    letI : Algebra L₁ Ω := f.toRingHom.toAlgebra
    haveI : IsScalarTower L L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    exact ⟨⟨n, h⟩, (lu_key L Ω l hmu n L₁).2⟩
