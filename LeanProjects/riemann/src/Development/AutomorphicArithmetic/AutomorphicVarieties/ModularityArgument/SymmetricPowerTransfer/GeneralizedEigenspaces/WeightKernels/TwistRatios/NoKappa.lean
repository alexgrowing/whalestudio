import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.KerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Coset
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.TraceSym4M
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.UfFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def phiB {k : Type} [Field k] {H : Type} [Group H] (a b : H →* GL (Fin 3) k) :
    H →* (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) where
  toFun h := ((a h : Matrix (Fin 3) (Fin 3) k), (b h : Matrix (Fin 3) (Fin 3) k), 1)
  map_one' := by simp
  map_mul' x y := by simp

private def fB {k : Type} [Field k] (A B : Matrix (Fin 3) (Fin 3) k) :
    (Matrix (Fin 3) (Fin 3) k × Matrix (Fin 3) (Fin 3) k × k) →ₗ[k] k :=
  (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k A ∘ₗ LinearMap.fst k _ _) +
    (Matrix.traceLinearMap (Fin 3) k k ∘ₗ LinearMap.mulLeft k B ∘ₗ LinearMap.fst k _ _ ∘ₗ LinearMap.snd k _ _) -
    (LinearMap.snd k _ _ ∘ₗ LinearMap.snd k _ _)

private theorem fB_apply {k : Type} [Field k] (A B X Y : Matrix (Fin 3) (Fin 3) k) (z : k) :
    fB A B (X, Y, z) = (A * X).trace + (B * Y).trace - z := by
  simp [fB]

theorem UpperTheory.V.Z.Sym.Ga.noKappa :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (r r' : Γ →* GL (Fin 2) (Qbar l)), IrrOpen (Ga.sym4 r) → ∀ V : Set Γ, IsOpen V → V.Nonempty → (∀ g ∈ V, Ga.uf (r' g) = Ga.uf (r g) ^ 2 - 2) → False := by
  intro l _ Γ _ _ _ _ _ r r' hirr V hV ⟨g, hg⟩ hu
  obtain ⟨H, -, hHo, hH⟩ := Ga.coset Γ V hV g hg
  have hR : IsIrr ((Ga.sym4 r).comp H.subtype) := hirr H hHo
  have key := Ga.kerLe (Qbar l) H 5 ((Ga.sym4 r).comp H.subtype) hR (Ga.sym4 r g)
    (Matrix (Fin 3) (Fin 3) (Qbar l) × Matrix (Fin 3) (Fin 3) (Qbar l) × Qbar l)
    (phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype))
    (fB (ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) (ad0 r' g)) ?_
  · have h1 := key.1
    have h2 : Module.finrank (Qbar l) ↥(Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))) ≤ 19 := by
      refine (Submodule.finrank_le (Subalgebra.toSubmodule (Algebra.adjoin (Qbar l)
        (Set.range ⇑(phiB ((ad0 r).comp H.subtype) ((ad0 r').comp H.subtype)))))).trans ?_
      simp [Module.finrank_prod, Module.finrank_matrix]
    omega
  · intro h
    have hgh := hu (g * h) (hH h h.2)
    have e1 : Ga.tr (Ga.sym4 r g * ((Ga.sym4 r).comp H.subtype) h) = Ga.tr (Ga.sym4 r (g * h)) := by
      simp [map_mul]
    have e2 : ((ad0 r g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r (h : Γ))).trace
        = Ga.uf (r (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r (g * h))).2.2.2.2 Γ r (g * h), map_mul]
      rfl
    have e3 : ((ad0 r' g : Matrix (Fin 3) (Fin 3) (Qbar l)) * (ad0 r' (h : Γ))).trace
        = Ga.uf (r' (g * h)) + 1 := by
      rw [← (Ga.ufFacts (Qbar l) (r' (g * h))).2.2.2.2 Γ r' (g * h), map_mul]
      rfl
    rw [e1, Ga.trSym4]
    show _ = fB _ _ ((((ad0 r).comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)),
      (((ad0 r').comp H.subtype) h : Matrix (Fin 3) (Fin 3) (Qbar l)), 1)
    rw [fB_apply]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [e2, e3, hgh]
    ring
