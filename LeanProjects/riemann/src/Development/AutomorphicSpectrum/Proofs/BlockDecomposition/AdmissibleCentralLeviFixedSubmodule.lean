import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import GroundTheory.AutomorphicForms.AdmissibleFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvectorLiftOfSurjection

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetEigen

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal in

theorem exists_eigenvector_fixed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → ∀ (W T : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π)) (Λ : ℂ), Λ ≠ 0 → T ≤ W → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w ∈ W) → (∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ w - Λ • w ∈ T) → (∃ w ∈ W, w ∉ T) → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π, y ≠ 0 ∧ (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) ∧ GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y := by
  intro k _ _ _ _ N V _ _ π hπ h β _hβ a ha hcomm W T Λ hΛ hTW hWst hWT hex
  obtain ⟨w₀, hw₀W, hw₀T⟩ := hex
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N β π
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N β) := fun m =>
    (congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N β)
  have hA := isAdmissible_jacquetRep (β := β) hπ
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N) (β := β)
    ((hA.1 w₀).mem_nhds (one_mem (stabilizerOf _ w₀)))
  have hfix₁ : w₀ ∈ fixedVectors J (KM m₁) := by
    have : w₀ ∈ fixedVectors (jacquetRep k N β π) (KM m₁) := fun x hx => hm₁ hx
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨m₁, fun m hm => ?_⟩
  have hle : KM m ≤ KM m₁ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone k N hm (Subgroup.mem_subgroupOf.1 hx))
  have hfix : w₀ ∈ fixedVectors J (KM m) := fixedVectors_antitone _ hle hfix₁
  have hfin : FiniteDimensional ℂ (fixedVectors J (KM m)) := by
    have := hA.2 (KM m) (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup k N m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup k N m))
    rwa [fixedVectors_jacquetRep_congruenceSubgroup] at this
  let A : Module.End ℂ _ := J ⟨a, ha⟩
  let W' : Submodule ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) :=
    W ⊓ fixedVectors J (KM m)
  have hW'fin : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le inf_le_right
  have hst : ∀ w ∈ W', A w ∈ W' := by
    intro w hw
    refine ⟨hWst w hw.1, fun g hg => ?_⟩
    have hw2 := hw.2 g hg
    have hc : g * ⟨a, ha⟩ = ⟨a, ha⟩ * g := Subtype.ext (hcomm g g.2).symm
    show J g (J ⟨a, ha⟩ w) = J ⟨a, ha⟩ w
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ hw2
  let B : W' →ₗ[ℂ] W' := A.restrict hst
  let Tc : Submodule ℂ W' := T.comap W'.subtype
  have hw₀' : w₀ ∈ W' := ⟨hw₀W, hfix⟩
  have hsq : Tc.mkQ ∘ₗ B = (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) ∘ₗ Tc.mkQ := by
    ext w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    exact hWT _ w.2.1
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.CompanionTheory.EigenLift.nonzero_eigenvalue_lifts W' (W' ⧸ Tc) B
    (Λ • (LinearMap.id : (W' ⧸ Tc) →ₗ[ℂ] (W' ⧸ Tc))) Tc.mkQ (Submodule.mkQ_surjective _) hsq Λ
    (Tc.mkQ ⟨w₀, hw₀'⟩)
    (fun h0 => hw₀T (by simpa [Tc] using (Submodule.Quotient.mk_eq_zero Tc).1 h0))
    rfl hΛ
  refine ⟨y, fun h0 => hy0 (Subtype.ext h0), fun g hg => y.2.2 g (Subgroup.mem_subgroupOf.2 hg), ?_⟩
  exact congrArg Subtype.val hy

end GlobalTheory.CompanionTheory.JacquetEigen
