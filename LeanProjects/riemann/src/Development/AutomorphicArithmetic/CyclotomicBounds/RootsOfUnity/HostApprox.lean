import Mathlib
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuBasic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TotientLeOfCycPowEqOne
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.NuSumApprox
import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.AutApprox

open NumberField Formalism.HC KStar.Tree

theorem UpperTheory.Mu.hostApprox :
    ∀ (φ : Frame) (H : HostRaw φ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω] (v : (ZMod H.condN)ˣ), H.art v = 1 → ∀ u : ℤ_[l]ˣ, (l : ℤ_[l]) ^ H.condN.factorization l ∣ (u : ℤ_[l]) - (((v : ZMod H.condN).val : ℕ) : ℤ_[l]) → ∀ k : ℕ, ∃ g : Ω ≃ₐ[H.E] Ω, (l : ℤ_[l]) ^ k ∣ ((cyc l H.E Ω g : ℤ_[l]ˣ) : ℤ_[l]) - u := by
  intro φ H l _ Ω _ _ _ v hv u hu k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap H.E Ω).injective
  haveI : IsScalarTower ℚ H.E Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed H.E
  haveI : Algebra.IsAlgebraic H.E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ H.E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : H.condN ≠ 0 := by
    obtain ⟨hq, hd, -⟩ := H.hyp
    exact Nat.mul_ne_zero (Nat.mul_ne_zero H.QS_pos.ne' hq.ne_zero) hd.ne_zero
  haveI : NeZero (H.QS * H.q * H.d) := ⟨hN⟩
  haveI : NeZero (((H.QS * H.q * H.d : ℕ)) : ℚ) := ⟨by exact_mod_cast hN⟩
  haveI : IsGalois ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    @IsCyclotomicExtension.isGalois {H.QS * H.q * H.d} ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) _ _ _
      (CyclotomicField.isCyclotomicExtension (H.QS * H.q * H.d) ℚ)
  letI : Algebra H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) := H.cycEmb.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic H.E (CyclotomicField (H.QS * H.q * H.d) ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) H.E
  let ι : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[H.E] Ω := IsAlgClosed.lift
  let ιQ : CyclotomicField (H.QS * H.q * H.d) ℚ →ₐ[ℚ] Ω := ι.restrictScalars ℚ
  have hι : ∀ x : H.E, ιQ (H.cycEmb x) = algebraMap H.E Ω x := fun x => ι.commutes x
  have hζ : IsPrimitiveRoot (ιQ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective ιQ.injective
  obtain ⟨σ, hσζ, hσu⟩ := UpperTheory.Mu.autApprox l Ω H.condN hN (ιQ H.cycZeta) hζ v u hu k
  letI : Algebra (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω := ιQ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (CyclotomicField (H.QS * H.q * H.d) ℚ) Ω :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let τ := σ.restrictNormal (CyclotomicField (H.QS * H.q * H.d) ℚ)
  have hτ : ∀ y, ιQ (τ y) = σ (ιQ y) := fun y => AlgEquiv.restrictNormal_commutes σ _ y
  have hτζ : τ H.cycZeta = H.cycZeta ^ ((v : ZMod H.condN).val) := by
    have e : ιQ (τ H.cycZeta) = ιQ (H.cycZeta ^ ((v : ZMod H.condN).val)) := by
      rw [hτ, hσζ, map_pow]
    exact ιQ.injective e
  have hfix : ∀ x : H.E, σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
    intro x
    have h := H.art_spec v τ hτζ x
    rw [show H.art v = 1 from hv, map_one, AlgEquiv.one_apply] at h
    rw [← hι, ← hτ, ← h]
  exact ⟨{ σ with commutes' := hfix }, hσu⟩
