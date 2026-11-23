import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}

abbrev sumN (M : ℕ → X.Modules) (k d e : ℕ) : X.Modules := ⨁ fun _ : Fin k => M (d + e)

def sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : sumN M k d e ⟶ M (d + e + 1) :=
  biproduct.desc fun i => T i (d + e)

def diagOp (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    sumN M k d e ⟶ sumN M k d (e + 1) :=
  biproduct.map fun _ => T j (d + e)

abbrev kerSeq (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : X.Modules := kernel (sumMap T d e)

theorem diagOp_sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    diagOp T d j e ≫ sumMap T d (e + 1) = sumMap T d e ≫ T j (d + e + 1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [diagOp, sumMap, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact hc j i (d + e)

def kerOp (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerSeq T d e ⟶ kerSeq T d (e + 1) :=
  kernel.lift _ (kernel.ι _ ≫ diagOp T d j e) (by
    rw [Category.assoc, diagOp_sumMap T hc, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem kerOp_ι (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerOp T hc d j e ≫ kernel.ι _ = kernel.ι _ ≫ diagOp T d j e :=
  kernel.lift_ι _ _ _

theorem diagOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    diagOp T d i e ≫ diagOp T d j (e + 1) = diagOp T d j e ≫ diagOp T d i (e + 1) := by
  apply biproduct.hom_ext
  intro l
  simp only [diagOp, Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  exact biproduct.π _ l ≫= hc i j (d + e)

theorem kerOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    kerOp T hc d i e ≫ kerOp T hc d j (e + 1) = kerOp T hc d j e ≫ kerOp T hc d i (e + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, kerOp_ι, kerOp_ι_assoc]
  rw [diagOp_comm T hc]

def kerSC (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (sumMap T d e)) (sumMap T d e) (kernel.condition _)

theorem kerSC_shortExact (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) [Epi (sumMap T d e)] :
    (kerSC T d e).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := by dsimp [kerSC]; infer_instance
  epi_g := by dsimp [kerSC]; infer_instance

end GlobalTheory.CompanionTheory.GE.KerSeq
