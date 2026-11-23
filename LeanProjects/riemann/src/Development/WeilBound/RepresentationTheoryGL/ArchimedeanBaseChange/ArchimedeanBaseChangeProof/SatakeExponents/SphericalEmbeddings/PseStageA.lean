import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lin

variable {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem coordL_lTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : U ⊗[ℂ] X) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisLeft b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add, map_add, hv, hw, map_add, Finsupp.mapRange_add (map_add g)]

theorem coordR_rTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : X ⊗[ℂ] U) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisRight b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x u =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add, map_add, hv, hw, map_add, Finsupp.mapRange_add (map_add g)]

theorem eq_zero_of_lTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : U ⊗[ℂ] X)
    (hv : ∀ h ∈ S, LinearMap.lTensor U (π h) v = v) (h0 : LinearMap.lTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisLeft b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisLeft b v i) =
        TensorProduct.equivFinsuppOfBasisLeft b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) (hv h hh)
      simpa [coordL_lTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisLeft b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) h0
      simpa [coordL_lTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

theorem eq_zero_of_rTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : X ⊗[ℂ] U)
    (hv : ∀ h ∈ S, LinearMap.rTensor U (π h) v = v) (h0 : LinearMap.rTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisRight b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisRight b v i) =
        TensorProduct.equivFinsuppOfBasisRight b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) (hv h hh)
      simpa [coordR_rTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisRight b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) h0
      simpa [coordR_rTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

end Lin

variable {n : ℕ} {V W Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

theorem kinj_comp {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) Z} (S : π.IntertwiningMap σ) (T : σ.IntertwiningMap τ) (hS : KInj k S)
    (hT : KInj k T) : KInj k (T.comp S) := by
  intro v hv h0
  have hv' : ∀ h : ↥(KO k (Fin n)), π h v = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • v := hv
  have hSv : S v ∈ GlobalTheory.PRep.fixed σ (KO k (Fin n)) := by
    show ∀ h : ↥(KO k (Fin n)), σ h (S v) = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • S v
    intro h
    rw [← S.isIntertwining, hv' h, map_smul]
  exact hS v hv (hT (S v) hSv h0)

theorem kinj_equiv {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (E : π.Equiv σ) :
    KInj k E.toIntertwiningMap := by
  intro v _ h
  simpa using h

end PositivityTheory.Rg.BcB.N3.PseStage

end
