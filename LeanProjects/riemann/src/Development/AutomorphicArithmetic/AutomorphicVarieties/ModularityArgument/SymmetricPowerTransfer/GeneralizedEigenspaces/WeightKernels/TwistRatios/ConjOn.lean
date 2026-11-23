import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.KerLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.SkolemNoether

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.conjOn :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R R' : H →* GL (Fin n) k), IsIrr R → ∀ x₀ y₀ : GL (Fin n) k, (∀ h, Ga.tr (x₀ * R h) = Ga.tr (y₀ * R' h)) → RepIso R R' := by
  intro k _ _ H _ n R R' hR x₀ y₀ htr
  classical
  let φ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R'
  let ψ : H →* Matrix (Fin n) (Fin n) k := (Units.coeHom _).comp R
  let f : Matrix (Fin n) (Fin n) k →ₗ[k] k :=
    (Matrix.traceLinearMap (Fin n) k k) ∘ₗ LinearMap.mulLeft k (y₀ : Matrix (Fin n) (Fin n) k)
  obtain ⟨hdim, hker⟩ := Ga.kerLe k H n R hR x₀ (Matrix (Fin n) (Fin n) k) φ f
    (fun h => by simpa [f, φ, Ga.tr] using htr h)
  have htop : Algebra.adjoin k (Set.range φ) = ⊤ := by
    apply Subalgebra.toSubmodule_injective
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    simpa [Module.finrank_matrix, sq] using hdim
  let P : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H φ
  let Q : MonoidAlgebra k H →ₐ[k] Matrix (Fin n) (Fin n) k := MonoidAlgebra.lift k _ H ψ
  have hs : Function.Surjective P := by
    have hle : Algebra.adjoin k (Set.range φ) ≤ P.range :=
      Algebra.adjoin_le (by
        rintro _ ⟨h, rfl⟩
        exact ⟨MonoidAlgebra.of k H h, by simp [P]⟩)
    intro m
    have hm : m ∈ P.range := hle (htop ▸ Algebra.mem_top)
    exact hm
  have hk : ∀ a ∈ RingHom.ker P, Q a = 0 := fun a ha => hker a ha
  let T : Matrix (Fin n) (Fin n) k →ₐ[k] Matrix (Fin n) (Fin n) k :=
    (Ideal.Quotient.liftₐ (RingHom.ker P) Q hk).comp
      (Ideal.quotientKerAlgEquivOfSurjective hs).symm.toAlgHom
  have hT : ∀ h, T (φ h) = ψ h := by
    intro h
    have h1 : (Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h) =
        Ideal.Quotient.mk (RingHom.ker P) (MonoidAlgebra.of k H h) := by
      rw [AlgEquiv.symm_apply_eq]
      simp [P]
    change Ideal.Quotient.liftₐ (RingHom.ker P) Q hk
      ((Ideal.quotientKerAlgEquivOfSurjective hs).symm (φ h)) = ψ h
    rw [h1]
    change Q (MonoidAlgebra.of k H h) = ψ h
    simp [Q]
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom T
  refine ⟨J⁻¹, fun s => ?_⟩
  have h2 := hJ (φ s)
  rw [hT] at h2
  have h3 : R s * J = J * R' s := Units.ext h2
  rw [inv_inv, mul_assoc, h3, inv_mul_cancel_left]
