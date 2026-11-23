import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametric
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.SqrtFixCent

theorem eq_mul_of_comm_mulRight {K A : Type} [Field K] [Ring A] [Algebra K A] (f : Module.End K A)
    (hf : ∀ y : A, LinearMap.mulRight K y * f = f * LinearMap.mulRight K y) (y : A) :
    f y = f 1 * y := by
  have h := congrArg (fun g : Module.End K A => g 1) (hf y)
  change f 1 * y = f (1 * y) at h
  rw [one_mul] at h
  exact h.symm

end GlobalTheory.SqrtFixCent

namespace GlobalTheory

theorem sqrt_fix_near_one_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  intro p _ v B _ _ _
  letI tB : TopologicalSpace B := moduleTopology (Qv v) B
  haveI : IsModuleTopology (Qv v) B := ⟨rfl⟩
  intro e σ _ hσe hσm hσ1
  let M : Subalgebra (Qv v) B := Subalgebra.centralizer (Qv v) {e}
  have hM : ∀ x : B, x ∈ M ↔ x * e = e * x := by
    intro x
    simp [M, Subalgebra.mem_centralizer_iff, eq_comm]
  haveI : CharZero (Qv v) := charZero_of_injective_algebraMap (algebraMap ℚ (Qv v)).injective
  letI : NontriviallyNormedField (Qv v) := Valued.toNontriviallyNormedField _ _
  let d := Module.finrank (Qv v) M
  let bM := Module.finBasis (Qv v) M
  let Lm : M →ₐ[Qv v] Matrix (Fin d) (Fin d) (Qv v) :=
    (LinearMap.toMatrixAlgEquiv bM).toAlgHom.comp (Algebra.lmul (Qv v) M)
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Subalgebra.toSubmodule M)
  let P : B →ₗ[Qv v] M := Submodule.linearProjOfIsCompl (Subalgebra.toSubmodule M) q hq
  have hP : ∀ x : M, P x = x := fun x => Submodule.linearProjOfIsCompl_apply_left hq x
  let L : B →ₗ[Qv v] Matrix (Fin d) (Fin d) (Qv v) := Lm.toLinearMap ∘ₗ P
  have hLc : Continuous L := IsModuleTopology.continuous_of_linearMap L
  have hL1 : L 1 = 1 := by
    show Lm (P ((1 : M) : B)) = 1
    rw [hP, map_one]
  obtain ⟨W₀, hW₀, hW₀s⟩ := GlobalTheory.matrix_sqrt_near_one_ultrametric (Qv v) d (RingHom.id _) continuous_id
  refine ⟨L ⁻¹' W₀, hLc.continuousAt.preimage_mem_nhds (by rw [hL1]; exact hW₀), ?_⟩
  intro s hs hse hσs
  let sM : M := ⟨s, (hM s).2 hse⟩
  have hLs : L s = Lm sM := by
    show Lm (P (sM : B)) = Lm sM
    rw [hP]
  obtain ⟨R, hRR, hRc, -⟩ := hW₀s _ (show L s ∈ W₀ from hs)
  rw [hLs] at hRR hRc
  let T := LinearMap.toMatrixAlgEquiv bM
  let f : Module.End (Qv v) M := T.symm R
  have hTs : Lm sM = T (LinearMap.mulLeft (Qv v) sM) := rfl
  have hf : ∀ g : Module.End (Qv v) M, g * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * g →
      g * f = f * g := by
    intro g hg
    apply T.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
    apply hRc
    rw [hTs, ← map_mul, ← map_mul, hg]
  have hff : f * f = LinearMap.mulLeft (Qv v) sM := by
    apply T.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, hRR]
    exact hTs
  have hfy : ∀ y : M, f y = f 1 * y := by
    refine GlobalTheory.SqrtFixCent.eq_mul_of_comm_mulRight f fun y => (hf _ ?_)
    exact LinearMap.ext fun x => mul_assoc sM x y
  have hρρ : f 1 * f 1 = sM := by
    have h := LinearMap.congr_fun hff 1
    change f (f 1) = sM * 1 at h
    rw [hfy (f 1), mul_one] at h
    exact h
  let σM : Module.End (Qv v) M :=
    { toFun := fun x => ⟨σ x, (hM _).2 (hσe x ((hM x).1 x.2))⟩
      map_add' := fun x y => Subtype.ext (by show σ ((x : B) + y) = σ x + σ y; exact map_add σ _ _)
      map_smul' := fun c x => Subtype.ext (by show σ (c • (x : B)) = c • σ x; exact map_smul σ _ _) }
  have hσM : ∀ x : M, ((σM x : M) : B) = σ x := fun x => rfl
  have hcomm : σM * LinearMap.mulLeft (Qv v) sM = LinearMap.mulLeft (Qv v) sM * σM := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show σ ((sM : B) * x) = (sM : B) * σ x
    rw [hσm s x hse ((hM x).1 x.2), hσs]
  have hσ1M : σM 1 = 1 := Subtype.ext (by show σ ((1 : M) : B) = ((1 : M) : B); exact hσ1)
  have hσρ : σM (f 1) = f 1 := by
    have h := LinearMap.congr_fun (hf σM hcomm) 1
    change σM (f 1) = f (σM 1) at h
    rw [hσ1M] at h
    exact h
  refine ⟨((f 1 : M) : B), (hM _).1 (f 1).2, congrArg Subtype.val hσρ, congrArg Subtype.val hρρ⟩

end GlobalTheory
