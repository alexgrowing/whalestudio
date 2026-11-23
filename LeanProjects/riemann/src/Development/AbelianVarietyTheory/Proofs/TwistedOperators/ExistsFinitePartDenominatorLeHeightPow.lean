import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientHeightLowerBoundShortIsotropicVector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFinNormComparison
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PointDenom

open GlobalTheory.HolDict.ShortVec (intRing)

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem tmul_mem {x : E} (hx : IsIntegral ℤ x) {a : 𝔸} (ha : a ∈ intRing F) :
    x ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := by
  have e1 : x ⊗ₜ[F] a = (x ⊗ₜ[F] (1 : 𝔸)) * ((1 : E) ⊗ₜ[F] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e1]
  exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨_, hx⟩, rfl⟩⟩, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨⟨a, fun v => Subring.mem_iInf.1 ha v⟩, rfl⟩))

theorem natCast_mul_tmul (c e : ℕ) (x : E) (a : 𝔸) :
    ((c * e : ℕ) : E ⊗[F] 𝔸) * (x ⊗ₜ[F] a) = ((c : E) * x) ⊗ₜ[F] ((e : 𝔸) * a) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← nsmul_eq_mul, mul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', smul_comm]

theorem comm_eq_sum {m : ℕ} (b : Module.Basis (Fin m) F E) (z : 𝔸 ⊗[F] E) :
    Algebra.TensorProduct.comm F 𝔸 E z = ∑ k, b k ⊗ₜ[F] (Algebra.TensorProduct.basis 𝔸 b).repr z k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis 𝔸 b).sum_repr z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.comm_tmul]

theorem exists_denom_comm {m : ℕ} (b : Module.Basis (Fin m) F E) : ∃ c : ℕ, 0 < c ∧ ∀ (e : ℕ) (z : 𝔸 ⊗[F] E),
      (∀ k, (e : 𝔸) * (Algebra.TensorProduct.basis 𝔸 b).repr z k ∈ intRing F) →
      ((c * e : ℕ) : E ⊗[F] 𝔸) * Algebra.TensorProduct.comm F 𝔸 E z ∈ Formalism.L2.Herm.intAf F E := by
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (integralClosure ℤ E).toSubring b fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨c, hc, fun e z hz => ?_⟩
  rw [comm_eq_sum b, Finset.mul_sum]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [natCast_mul_tmul]
  exact tmul_mem (h k) (hz k)

end

theorem exists_denom_le_height_pow : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧
    (d : ℝ) ≤ C * GlobalTheory.Grow.height V g ^ A ∧
    ∀ i j, (d : Lev.EAf D) * (Lev.finE V g).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D V
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨C, -, hC⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨c, hc, h⟩ := exists_denom_comm (Module.finBasis D.host.F D.host.E)
  refine ⟨c * C, 1, fun g => ?_⟩
  obtain ⟨d, hd, hdH, hint⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  refine ⟨c * d, Nat.mul_pos hc hd, ?_, fun i j => h d _ (hint i j)⟩
  rw [pow_one, Nat.cast_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdH.trans (hC g).1) (Nat.cast_nonneg c)

end GlobalTheory.PointDenom
