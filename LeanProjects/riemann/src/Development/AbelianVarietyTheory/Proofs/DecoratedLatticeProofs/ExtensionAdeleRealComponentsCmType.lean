import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCMFamHost

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealComp

theorem eq_zero_of_map_eq_zero {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    {I : Type} {B : I → Type} [∀ i, CommRing (B i)] [∀ i, Algebra F (B i)] (f : ∀ i, A →ₐ[F] B i)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (z : A ⊗[F] E)
    (hz : ∀ i, Algebra.TensorProduct.map (f i) (AlgHom.id F E) z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  have key : ∀ i (y : A ⊗[F] E) k,
      (Algebra.TensorProduct.basis (B i) b).repr (Algebra.TensorProduct.map (f i) (AlgHom.id F E) y) k =
        f i ((Algebra.TensorProduct.basis A b).repr y k) := by
    intro i y k
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.smul_def, mul_comm]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply (Algebra.TensorProduct.basis A b).repr.injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hf _ fun i => ?_
  rw [← key, hz, map_zero, Finsupp.zero_apply]

theorem compInf_eq_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : InfinitePlace F) (z : AF F ⊗[F] E) : compInf F E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

variable {D : D7}

theorem compInf_eq (w : InfinitePlace D.host.F) (z : AE D) : compInf D.host.F D.host.E w z =
    Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E) (infPart D z) :=
  compInf_eq_map w z

theorem compInf_zero_iff (z : AE D) : (∀ w, compInf D.host.F D.host.E w z = 0) ↔ infPart D z = 0 := by
  refine ⟨fun h => ?_, fun h w => by rw [compInf_eq, h, map_zero]⟩
  exact eq_zero_of_map_eq_zero (fun w => GlobalTheory.AutFunCompare.evW w) (fun a ha => funext ha) _
    fun w => (compInf_eq w z).symm.trans (h w)

theorem theta_zero_iff {θ : InfFam D} (hθ : IsInfFam θ) (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    (∀ τ, θ τ y = 0) ↔ y = 0 := by
  refine ⟨fun h => ?_, fun h τ => by rw [h, map_zero]⟩
  refine (GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D)
    (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ).1 (funext fun τ => ?_)
  exact (h τ).trans (map_zero _).symm

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eq_zero_of_parts (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  rw [map_zero]
  exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h2)

theorem real_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → (∀ z : AE D, (∀ w, compInf D.host.F D.host.E w z = 0) ↔ ∀ τ, θ τ (infPart D z) = 0) ∧ (∀ z τ, θ τ (infPart D (cA D z)) = conj (θ τ (infPart D z))) ∧ (∀ x τ, θ τ (infPart D (incA D x)) = tauE D τ x) ∧ (∀ z : AE D, (∀ τ, θ τ (infPart D z) = 0) → finPart D z = 0 → z = 0) := by
  intro D θ hθ
  refine ⟨fun z => (compInf_zero_iff z).trans (theta_zero_iff hθ _).symm, fun z τ => ?_, fun x τ => (hθ τ).1 x,
    fun z h1 h2 => eq_zero_of_parts z ((theta_zero_iff hθ _).1 h1) h2⟩
  rw [infPart_conj]
  exact GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) _

end GlobalTheory.StdUnn.RealComp

end
