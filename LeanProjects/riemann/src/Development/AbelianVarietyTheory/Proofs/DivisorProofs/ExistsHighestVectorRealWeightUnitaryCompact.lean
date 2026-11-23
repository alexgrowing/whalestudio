import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_kHighest_real_of_finiteDimensional : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), KRel ε E → KUnit ε E → ∀ N : Submodule ℂ V, FiniteDimensional ℂ N → KStab ε E N → N ≠ ⊥ → ∃ (μ : Fin n → ℝ) (w : V), w ∈ N ∧ w ≠ 0 ∧ KHighest ε E μ w := by
  intro n ε V _ _ E hR hU N hfd hS hN
  classical
  haveI : FiniteDimensional ℂ N := hfd
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  have hcomm : ∀ k i j, ε i = ε j → E k k * E i j - E i j * E k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • E i j := by
    intro k i j h
    rw [hR k k i j rfl h]
    by_cases h1 : k = i <;> by_cases h2 : j = k
    · subst h1; subst h2; simp
    · subst h1; simp [h2]
    · subst h2; simp [h1]
    · simp [h1, h2]
  let H : Module.End ℂ V := ∑ k : Fin n, ((k : ℕ) : ℂ) • E k k
  have hH : ∀ i j, ε i = ε j → H * E i j = E i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • E i j := by
    intro i j hij
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hcomm _ _ _ hij, smul_smul, ← Finset.sum_smul]
    simp [mul_sub]
  have hHN : ∀ v ∈ N, H v ∈ N := by
    intro v hv
    simp only [H, LinearMap.sum_apply, LinearMap.smul_apply]
    exact N.sum_mem fun k _ => N.smul_mem _ (hS k k rfl v hv)
  let HN : Module.End ℂ N := H.restrict hHN
  let D : Fin n → Module.End ℂ N := fun k => (E k k).restrict (fun v hv => hS k k rfl v hv)
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | HN.HasEigenvalue c} Complex.re
    (Module.End.finite_hasEigenvalue HN) (Module.End.exists_eigenvalue HN)
  have hDc : ∀ i j, D i * D j = D j * D i := by
    intro i j
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := LinearMap.congr_fun (hcomm i j j rfl) (x : V)
    have h' : ((if i = j then (1 : ℂ) else 0) - (if j = i then 1 else 0)) = 0 := by
      by_cases h1 : i = j
      · subst h1; simp
      · simp [h1, Ne.symm h1]
    rw [h', zero_smul, LinearMap.zero_apply, LinearMap.sub_apply, sub_eq_zero] at h
    simpa [D, LinearMap.restrict_apply] using h
  obtain ⟨v, hv, hv0, ν, hν⟩ := GlobalTheory.AlgInfChar.exists_joint_eigenvector D hDc (HN.eigenspace l) hl
    (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      apply Subtype.ext
      have h1 := LinearMap.congr_fun (hH k k rfl) (u : V)
      have h2 : H (u : V) = l • (u : V) := congrArg Subtype.val hu
      simp only [sub_self, zero_smul, add_zero, Module.End.mul_apply] at h1
      simp only [HN, D, LinearMap.restrict_apply, SetLike.val_smul]
      rw [h1, h2, map_smul])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hHv : H (v : V) = l • (v : V) := congrArg Subtype.val hv
  have hEv : ∀ a, E a a (v : V) = ν a • (v : V) := fun a => congrArg Subtype.val (hν a)
  have hv0' : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hreal : ∀ a, (((ν a).re : ℝ) : ℂ) = ν a := by
    intro a
    have h := hU a a rfl (v : V) (v : V)
    rw [hEv, inner_smul_left, inner_smul_right] at h
    have hne : ⟪(v : V), (v : V)⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0'
    exact Complex.conj_eq_iff_re.1 (mul_right_cancel₀ hne h)
  refine ⟨fun a => (ν a).re, v, v.2, hv0', fun a => by rw [hEv, hreal], fun a b hab he => ?_⟩
  by_contra h0
  let u : N := ⟨E a b v, hS a b he v v.2⟩
  have hu0 : u ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hHu : HN u = (l + (((a : ℕ) : ℂ) - (b : ℕ))) • u := by
    apply Subtype.ext
    have h1 := LinearMap.congr_fun (hH a b he) (v : V)
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at h1
    simp only [HN, u, LinearMap.restrict_apply, SetLike.val_smul]
    rw [h1, hHv, map_smul, add_smul]
  have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hHu, hu0⟩)
  have hab' : (a : ℕ) < b := hab
  simp at h2
  exact absurd hab' (not_lt.2 (by exact_mod_cast h2))

end GlobalTheory
