import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContractionLocal

section Tens
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def colTens (φ : SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n' ⊕ Unit)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁)
      (r := fun x r => x r (Sum.inr ())) (s := fun z => Matrix.fromCols z.1 (Matrix.of fun r _ => z.2 r))
      (by unfold Matrix.toCols₁; fun_prop) (continuous_pi fun r => by fun_prop) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases j with j | j
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply i).comp continuous_snd
    · intro x
      ext i (j | j)
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem colTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (colTens φ Ξ).1 x = Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())) := rfl

def rowTens (φ : SB (n → k)) : SB (Matrix n'' n k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n'' ⊕ Unit) (n' := n)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix (n'' ⊕ Unit) n k => x.toRows₁)
      (r := fun x => x (Sum.inr ())) (s := fun z => Matrix.fromRows z.1 (Matrix.of fun _ => z.2))
      (by unfold Matrix.toRows₁; fun_prop) (continuous_pi fun j => continuous_id.matrix_elem _ j) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases i with i | i
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply j).comp continuous_snd
    · intro x
      ext (i | i) j
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem rowTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n'' n k)) (x : Matrix (n'' ⊕ Unit) n k) :
    (rowTens φ Ξ).1 x = Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())) := rfl

end Tens

section Bil
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_contr (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ} {Ξ₂ : WO S B'.V₀ → ℂ}
    (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (h₂ : IsThetaFunO ψ S B'.V₀ Ξ₂) (u : WO B.A S) (v : WO S B'.A) :
    Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := by
  haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ h₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ h₂
  have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
    (h₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))).mul
      (h₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (continuous_kappa l S))))
  refine (integrable_const (C₂ * C₁)).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC₂ _) (hC₁ _) (norm_nonneg _) ((norm_nonneg _).trans (hC₂ 0))

def contrBil (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] (WO B.A S → WO S B'.A → ℂ) :=
  LinearMap.mk₂ ℂ (fun Ψ₁ Ψ₂ => GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂))
    (fun a a' b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a') (h₂ b) u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)
    (fun a b b' => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a) (h₂ b') u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)

@[simp] theorem contrBil_apply (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) (Ψ₁ : M₁) (Ψ₂ : M₂) :
    contrBil hψ l S vL T₁ T₂ h₁ h₂ Ψ₁ Ψ₂ = GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂) := rfl

end Bil

end GlobalTheory.ContractionLocal

namespace GlobalTheory.ContractionLocal

theorem exists_normPair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψk)
    (hν : ν.IsAddHaarMeasure) (n : Type) [Fintype n] [DecidableEq n] :
    ∃ φ₀ φ₀' : SB (n → k), ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) = 1 := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  let L := GlobalTheory.LatPair.stdLat k n
  have hc := GlobalTheory.FinPl.Comm.fpair_ne_zero ψk hψ (-1) (Or.inr rfl) (Measure.pi fun _ => ν) L
  set c := GlobalTheory.FinPl.Comm.fpair ψk (-1) (Measure.pi fun _ => ν) (GlobalTheory.FinPl.vecInd L) (GlobalTheory.FinPl.dualInd L)
  refine ⟨⟨_, GlobalTheory.FinPl.Comm.vecInd_mem L⟩, c⁻¹ • ⟨_, GlobalTheory.FinPl.Comm.dualInd_mem L⟩, ?_⟩
  have e : c = ∫ u, (GlobalTheory.FinPl.dualInd L u) * GlobalTheory.StepData.hat ψk ν (-1) (GlobalTheory.FinPl.vecInd L) u
      ∂(Measure.pi fun _ => ν) := by
    simp only [c, GlobalTheory.FinPl.Comm.fpair, GlobalTheory.StepData.hat]
    congr 1; funext u; ring
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, ← e, inv_mul_cancel₀ hc]

theorem contr_tens {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k)
    {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (φ₀ φ₀' : SB (n → k)) (Ξ₁ : SB (Matrix n n' k)) (Ξ₂ : SB (Matrix n'' n k)) (q : Matrix n n' k × Matrix n'' n k) :
    GlobalTheory.LocFlat.contr ψk ν (colTens φ₀ Ξ₁).1 (rowTens φ₀' Ξ₂).1 q =
      Ξ₁.1 q.1 * Ξ₂.1 q.2 * ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) := by
  simp only [GlobalTheory.LocFlat.contr, colTens_apply, rowTens_apply, Matrix.toCols₁_fromCols, Matrix.toRows₁_fromRows,
    GlobalTheory.StepData.hat]
  rw [← integral_const_mul]
  congr 1; funext u
  have h1 : (Matrix.fromRows q.2 (Matrix.of fun _ : Unit => u)) (Sum.inr ()) = u := rfl
  have h2 : ∀ y : n → k, (fun r => Matrix.fromCols q.1 (Matrix.of fun r (_ : Unit) => y r) r (Sum.inr ())) = y :=
    fun y => rfl
  simp only [h1, h2]
  rw [show (∫ y, Ξ₁.1 q.1 * φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν)) =
      Ξ₁.1 q.1 * ∫ y, φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν) by
    rw [← integral_const_mul]; congr 1; funext y; ring]
  ring
end GlobalTheory.ContractionLocal

end
