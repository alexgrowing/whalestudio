import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlternatingDifferenceTermWindowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoBadWindowDivRhoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignedInvolutionStableLatticeSumMulFixedUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeIdempotentPositionInvolutionStableStatement

noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

namespace GlobalTheory.UnitLemma.Desc

variable {K : UQ} (B : InvAlg K) {ι : Type}

theorem eS_mul_eS_of_disjoint_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e)
    {I J : Finset ι} (h : Disjoint I J) : eS B e I * eS B e J = 0 := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  exact he.ortho (fun hij => Finset.disjoint_left.1 h hi (hij ▸ hj))

theorem eS_mul_self_inv [Fintype ι] {e : ι → B.A} (he : CompleteOrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  unfold eS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i]
  · exact (he.idem i).eq
  · intro j _ hji; exact he.ortho (Ne.symm hji)
  · intro h; exact absurd hi h

theorem σ_eS_inv [Fintype ι] {e : ι → B.A} {S : Finset ι} (hP : IsPre B e S) (I : Finset ι) :
    B.σ (eS B e I) = eS B e I := by
  unfold eS
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨f, -, -, -, h1, h2⟩ := hP.2 i
  by_cases hi : i ∈ S
  · obtain ⟨h, hf⟩ := h1 hi; rw [h, hf]
  · obtain ⟨-, h⟩ := h2 hi; rw [h, map_add, B.σ_σ, add_comm]

theorem HH_sub_chi_mul_HH_negligible : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι]
    (e π : ι → B.A) (S : Finset ι) (a : K.O), B.LieReg → K.Small a → IsFrame B e π S → ∀ I ⊆ S, ∀ x : B.A,
    B.Plus x → Tendsto (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) atTop (𝓝 0) := by
  intro K B ι _ _ e π S a hL ha hF I hI x hx
  have hEE := eS_mul_self_inv B hF.1.1 I
  have hE'E := eS_mul_eS_of_disjoint_inv B hF.1.1 (Finset.sdiff_disjoint (s := I) (t := S))
  have hσE := σ_eS_inv B hF.1 I
  have hcov : ∀ i ∈ S, i ∈ I ∨ i ∈ S \ I := fun i hi => by
    by_cases h : i ∈ I
    · exact Or.inl h
    · exact Or.inr (Finset.mem_sdiff.2 ⟨hi, h⟩)
  set E := eS B e I with hEdef
  set E' := eS B e (S \ I) with hE'def
  obtain ⟨xi, hxi⟩ : ∃ xi : B.A, x * xi = 1 := ⟨_, hx.1.mul_val_inv⟩

  have hyu : IsUnit (x * E + (1 - E)) :=
    IsUnit.of_mul_eq_one (xi * E + (1 - E)) (by linear_combination (E * E) * hxi + (2 - x - xi) * hEE)
  have hx'u : IsUnit (x * (1 - E) + E) :=
    IsUnit.of_mul_eq_one (xi * (1 - E) + E) (by linear_combination (1 - E) ^ 2 * hxi + (2 - x - xi) * hEE)
  have hyP : B.Plus (x * E + (1 - E)) := ⟨hyu, by simp only [map_add, map_mul, map_sub, map_one, hx.2, hσE]⟩
  have hxy : (x * E + (1 - E)) * (x * (1 - E) + E) = x := by linear_combination (-(x - 1) ^ 2) * hEE
  have hchi : chi B e I x = K.eta (Algebra.norm K.E (x * E + (1 - E))) := rfl

  have haU : IsUnit (algebraMap K.O B.A a) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A a]
    refine (IsUnit.mk0 _ fun h => ha.1 ?_).map _
    exact IsFractionRing.injective K.O K.E (h.trans (map_zero _).symm)

  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_lattice_idempotent_position_involution_stable K B ι e π S a hL.2 ha hF
  obtain ⟨L₀, hL₀⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    (x * (1 - E) + E) (x * E + (1 - E)) hx'u hyu
  obtain ⟨L₁, hL₁⟩ := GlobalTheory.T.alternatingDifference_term_window K B ι e π S a hL.2 ha hF I (S \ I) hI Finset.sdiff_subset hcov N
    1 1 isUnit_one isUnit_one
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → Submodule K.O B.A → ℚ, ∀ k M, F k M =
      B.sgnLat M * term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → Submodule K.O B.A → ℚ, ∀ k M, G k M =
      B.sgnLat M * term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M := ⟨_, fun _ _ => rfl⟩
  have hsg : ∀ M, |B.sgnLat M| = 1 := fun M => by unfold InvAlg.sgnLat; exact abs_eta _
  have hFfin : ∀ k, (B.Lin ∩ Function.support (F k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ ((hx'u.mul (haU.pow _))) hyu).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hFdef, h0, mul_zero])⟩
  have hGfin : ∀ k, (B.Lin ∩ Function.support (G k)).Finite := fun k =>
    (GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero K B ι e π S hL.2 hF I (S \ I) hI Finset.sdiff_subset _ _ (haU.pow _) isUnit_one).subset
      fun M ⟨hM, h⟩ => ⟨hM, fun h0 => h (by rw [hGdef, h0, mul_zero])⟩
  have hsub : ∀ k, ∑ᶠ M ∈ B.Lin, (F k M - G k M) = ∑ᶠ M ∈ B.Lin, F k M - ∑ᶠ M ∈ B.Lin, G k M := by
    intro k
    have hFG : (B.Lin ∩ Function.support (fun M => F k M - G k M)).Finite :=
      ((hFfin k).union (hGfin k)).subset fun M ⟨hM, h⟩ => by
        by_cases h1 : F k M = 0
        · exact Or.inr ⟨hM, fun h2 => h (show F k M - G k M = 0 by rw [h1, h2, sub_zero])⟩
        · exact Or.inl ⟨hM, h1⟩
    rw [eq_sub_iff_add_eq, ← finsum_mem_add_distrib' hFG (hGfin k)]
    simp only [sub_add_cancel]

  have key : ∀ k : ℕ, HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 =
      K.eta (Algebra.norm K.E (x * E + (1 - E))) * ∑ᶠ M ∈ B.Lin, (F k M - G k M) := by
    intro k
    have hx_eq : x * algebraMap K.O B.A a ^ (2 * k) =
        (x * E + (1 - E)) * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) := by
      rw [← mul_assoc, hxy]
    rw [hx_eq, GlobalTheory.T.signedInvolutionStableLatticeSum_mul_fixed_unit K B ι π I (S \ I) _ 1 _ hL hyP, hchi, mul_one, hsub, ← mul_sub]
    congr 1
    unfold HH
    congr 1
    · exact finsum_congr fun M => finsum_congr fun _ => (hFdef k M).symm
    · exact finsum_congr fun M => finsum_congr fun _ => (hGdef k M).symm

  have hcmp := GlobalTheory.T.tendsto_finsum_div_rho_pow_zero K B ι e π S a hL.2 ha hF I (S \ I) hcov N (max L₀ L₁)
    (2 * 2 ^ I.card * 2 ^ (S \ I).card) (fun k M => F k M - G k M) hN
    (by
      intro k M
      rw [hFdef, hGdef, ← mul_sub, abs_mul, hsg, one_mul]
      calc _ ≤ |term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) (x * E + (1 - E)) M| +
            |term B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 M| := abs_sub _ _
        _ ≤ 2 ^ I.card * 2 ^ (S \ I).card + 2 ^ I.card * 2 ^ (S \ I).card :=
            add_le_add (abs_term _ _ _ _ _ _ _) (abs_term _ _ _ _ _ _ _)
        _ = _ := by ring)
    (by
      intro k hk M _ p hp hf
      rw [hFdef, hGdef, ← mul_sub] at hf
      have hne := right_ne_zero_of_mul hf
      obtain ⟨h1a, h1b⟩ := hL₀ (max L₀ L₁) (le_max_left _ _) k hk M p hp
      obtain ⟨h2a, h2b⟩ := hL₁ (max L₀ L₁) (le_max_right _ _) k hk M p hp
      rw [one_mul] at h2a h2b
      rw [← hEdef, ← hE'def] at h1b h2b
      have hW : Win I (S \ I) (max L₀ L₁) k p := by
        by_cases h : term B π I (S \ I) ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k))
            (x * E + (1 - E)) M = 0
        · exact h2a fun h2 => hne (by rw [h, h2, sub_zero])
        · exact h1a h
      refine ⟨hW, fun hmid => hne ?_⟩
      have hEx : E * ((x * (1 - E) + E) * algebraMap K.O B.A a ^ (2 * k)) = E * algebraMap K.O B.A a ^ (2 * k) := by
        linear_combination algebraMap K.O B.A a ^ (2 * k) * (1 - x) * hEE
      have hE'y : E' * (x * E + (1 - E)) = E' * 1 := by linear_combination (x - 1) * hE'E
      rw [h1b hW hmid, h2b hW hmid, hEx, hE'y, sub_self])
  have hfun : (fun k : ℕ => (((HH B π I (S \ I) (x * algebraMap K.O B.A a ^ (2 * k)) 1 -
      chi B e I x * HH B π I (S \ I) (algebraMap K.O B.A a ^ (2 * k)) 1 : ℚ) : ℝ) /
      (B.rho (algebraMap K.O B.A a ^ k) : ℝ))) = fun k : ℕ =>
      (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ) * (((∑ᶠ M ∈ B.Lin, (F k M - G k M) : ℚ) : ℝ) /
        (B.rho (algebraMap K.O B.A a ^ k) : ℝ)) := by
    funext k
    rw [key k, Rat.cast_mul, mul_div_assoc]
  rw [hfun]
  simpa using hcmp.const_mul (K.eta (Algebra.norm K.E (x * E + (1 - E))) : ℝ)

end GlobalTheory.UnitLemma.Desc
