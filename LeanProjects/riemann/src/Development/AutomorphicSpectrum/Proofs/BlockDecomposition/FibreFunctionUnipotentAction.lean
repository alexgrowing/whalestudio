import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

variable {k : Type} [Field k]

theorem extTensor_fst_one {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (a : G) :
    extTensor ρ σ (a, 1) = LinearMap.rTensor W (ρ a) := by
  apply TensorProduct.ext'
  intro v w
  rw [extTensor_tmul, LinearMap.rTensor_tmul]
  show ρ a v ⊗ₜ[ℂ] σ 1 w = _
  rw [map_one, Module.End.one_apply]

theorem uM_comm (n : ℕ) (a b : Fin n → k) : uM k n a * uM k n b = uM k n b * uM k n a := by
  rw [← uM_add, ← uM_add]
  exact congrArg _ (add_comm a b)

theorem midV_add (i t : ℕ) (a b : Fin t → k) : midV k i t (a + b) = midV k i t a + midV k i t b := by
  funext j
  induction j using Fin.addCases <;> simp [midV]

theorem col_eq (i t : ℕ) (a : Fin (i + t) → k) : a = topV k i t (topP i t a) + midV k i t (middlePart i t a) := by
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp [topP, middlePart]

theorem point_mul_uM (i t : ℕ) (κ : GL (Fin (i + t)) k) (v : Fin t → k) (y : Fin (i + t) → k) :
    uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y =
      uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
        (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
          levi k (i + t) κ) := by
  rw [mul_assoc, levi_mul_uM, ← mul_assoc, ← mul_assoc, midV_add, uM_add]
  congr 1
  conv_lhs => rw [col_eq i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y), uM_add]
  rw [← mul_assoc, uM_comm (i + t) (midV k i t v)]
  exact mul_assoc _ _ _

theorem cInd_point {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (x : G) (f : cIndSpace H ρ) (p : G) :
    (cInd H ρ x f).1.1.1 p = f.1.1.1 (p * x) := rfl

theorem cInd_equi {G U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup U] [Module ℂ U]
    (H : Subgroup G) (ρ : Representation ℂ H U) (f : cIndSpace H ρ) (h : H) (p : G) :
    f.1.1.1 ((h : G) * p) = ρ h (f.1.1.1 p) := f.1.1.2 h p

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fibV_uM_of (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k)
    (h : uM k (i + t) (topV k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) ∈ HPG k i t)
    (hp : pgProj k i t ⟨_, h⟩ = (uM k i (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)), 1)) :
    fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
        (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  have e1 : fibV (prodPG τ σ (uM k (i + t) y) f) κ v =
      f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) κ * uM k (i + t) y) :=
    cInd_point (HPG k i t) (hRep τ σ) (uM k (i + t) y) f _
  have e2 := congrArg f.1.1.1 (point_mul_uM i t κ v y)
  have e3 := cInd_equi (HPG k i t) (hRep τ σ) f ⟨_, h⟩ (uM k (i + t) (midV k i t (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) *
    levi k (i + t) κ)
  have e4 : hRep τ σ ⟨_, h⟩ = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) :=
    (congrArg (extTensor τ σ) hp).trans (extTensor_fst_one τ σ _)
  exact e1.trans (e2.trans (e3.trans (LinearMap.congr_fun e4 _)))
end

theorem fibV_uM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k), fibV (prodPG τ σ (uM k (i + t) y) f) κ v = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ f y κ v
  exact Exists.elim (GlobalTheory.T.unipotent_top_mem_parabolic k i t (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y)))
    (fun h hp => fibV_uM_of τ σ f y κ v h hp)

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU

end
