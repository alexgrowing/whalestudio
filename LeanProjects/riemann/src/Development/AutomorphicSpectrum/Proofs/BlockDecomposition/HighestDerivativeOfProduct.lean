import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HighestDeriv

section Coinv

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem twKer_le_comap {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ)
    (U : Subgroup G) (θ : U →* ℂˣ) :
    twKer π U θ ≤ (twKer σ U θ).comap φ.toIntertwiningMap.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, φ.toIntertwiningMap v, ?_⟩
  rw [map_sub, map_smul, ← φ.toIntertwiningMap.isIntertwining]
  rfl

def twJacquetEquiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ)
    (U : Subgroup G) (θ : U →* ℂˣ) : TwJacquet π U θ ≃ₗ[ℂ] TwJacquet σ U θ :=
  Submodule.Quotient.equiv _ _ φ.toLinearEquiv (le_antisymm
    (Submodule.map_le_iff_le_comap.2 (twKer_le_comap φ U θ))
    (fun y hy => ⟨φ.symm y, twKer_le_comap φ.symm U θ hy, φ.apply_symm_apply y⟩))

end Coinv

def piFinTwoTensor (X : Fin 2 → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] :
    (⨂[ℂ] a, X a) ≃ₗ[ℂ] X 0 ⊗[ℂ] X 1 :=
  ((LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => X i.succ) 0).symm).trans
    (GlobalTheory.SmGL.MultiIrr.tensorCons X)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Two

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t : ℕ}

def piTensorTwoEquiv' (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂)).Equiv
      ((extTensor π₁ π₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
  .mk (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)) fun g => by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    show GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W)
        (piTensor (GlobalTheory.BZMir.Leib.twoRep (k := k) π₁ π₂) g (PiTensorProduct.tprod ℂ x)) =
      extTensor π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g)
        (GlobalTheory.SmGL.Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ x))
    rw [piTensor_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod, GlobalTheory.SmGL.Exponents.boolTensorEquiv_tprod]
    exact (extTensor_tmul π₁ π₂ ((leviTwo k (Fin r) (Fin t)).symm g) (x false) (x true)).symm

theorem nonempty_prod2_equiv (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W) :
    Nonempty ((prod2 (k := k) rfl π₁ π₂).Equiv (prod₂ π₁ π₂)) :=
  ⟨LocGL.parIndEquiv (two (stdSum (rfl : r + t = r + t))) (piTensorTwoEquiv' π₁ π₂)⟩

end Two

section Main

def deg (r t : ℕ) : Fin 2 → ℕ := Fin.cases r fun _ => t

def fam {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) : ∀ a, GRep k (deg r t a) := Fin.cases π₁ fun _ => π₂

end Main

end GlobalTheory.CompanionTheory.HighestDeriv

end
