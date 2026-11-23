import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.Twist.RestrictionTransfer

theorem rest_transfer : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → (∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r x ≠ 0) →
    ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f r ⟨hinv, hsch⟩ ⟨x₀, hx₀⟩ f₁
  refine ⟨hinv, ?_⟩
  set a₀ : κ → mixedEmbedding.mixedSpace F := fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) with ha₀
  have hc : f a₀ ≠ 0 := by
    intro h; apply hx₀; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]; rw [← ha₀, h, zero_mul]
  let zz : (κ → AF F) → (κ → AF F) := fun x i =>
    (((x₀ i).1 - (x i).1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have hz1 : ∀ x i, (x i + zz x i).1 = (x₀ i).1 := by
    intro x i; show (x i).1 + ((x₀ i).1 - (x i).1) = _; ring
  have hz2 : ∀ x i, (x i + zz x i).2 = (x i).2 := by
    intro x i; show (x i).2 + 0 = _; simp
  have hev : ∀ x, (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + zz x) i)) = a₀ := by
    intro x; funext i; simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, ha₀]; rw [hz1]
  have hAt : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (zz x) := by
    intro x u hu
    have hu1 : u.1 = 0 := by
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
    funext i
    show ((u.1 * ((x₀ i).1 - (x i).1), u.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
    rw [hu1]; simp
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * Φ (x + zz x)
      map_add' := by intro Φ Ψ; funext x; simp [mul_add]
      map_smul' := by intro c Φ; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, L Φ ∈ GlobalTheory.WeilM.schA F κ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, h, hh, rfl⟩ := hΦ
      have : L (GlobalTheory.WeilM.pureA F g h) = g a₀ • GlobalTheory.WeilM.pureA F f₁ h := by
        funext x
        have e := hev x
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI] at e ⊢
        rw [e]
        have : (fun i => (x i + zz x i).2) = fun i => (x i).2 := funext fun i => hz2 x i
        rw [this]; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₁, h, hh, rfl⟩)
    | zero => simp
    | add Φ Ψ _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
    | smul c Φ _ h1 => rw [map_smul]; exact Submodule.smul_mem _ c h1
  have hLt : L (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
      f a₀ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
    funext x
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul]
    rw [hev x, hinv x (zz x) (hAt x)]; ring
  have hm := key _ hsch
  rw [hLt] at hm
  have := Submodule.smul_mem _ (f a₀)⁻¹ hm
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.Twist.RestrictionTransfer
