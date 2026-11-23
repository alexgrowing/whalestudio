import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleStrongApproxModAdelicIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRationalPointOfMemMovedThetaLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.LocAgree

theorem exists_int_mul (D : D7) {N : ℕ} (q : ℕ) (k : GA D N) (h : TrivAt D q (k : GL (Fin N) (AE D))) :
    ∃ s : ℕ, Nat.Coprime s q ∧
      (∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D) ∧
      ∀ i j, (s : AE D) * (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
        Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  have h0 : ∀ i j, ∃ m : ℕ, Nat.Coprime m q ∧ (m : AE D) *
      (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
    intro i j
    obtain ⟨m, -, hm, s, hs, he⟩ := h i j 0
    refine ⟨m, hm, ?_⟩
    rw [pow_zero, one_mul] at he
    rw [he]
    exact hs
  choose m hm hmS using h0
  set s : ℕ := ∏ r : Fin N × Fin N, m r.1 r.2 with hs
  have hint : ∀ i j, (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
    intro i j
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun r : Fin N × Fin N => m r.1 r.2) (Finset.mem_univ (i, j))
    have h1 : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have : (s : AE D) * ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j = (c : AE D) * ((m i j : AE D) *
        (((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
          (1 : Matrix (Fin N) (Fin N) (AE D)) i j)) + (s : AE D) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
      rw [hs, hc]; push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ c) (hmS i j)) (mul_mem (natCast_mem _ s) h1)
  refine ⟨s, Nat.Coprime.prod_left fun r _ => hm r.1 r.2, hint, fun i j => ?_⟩
  rw [AdLattice.inv_entry (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) _ k.2]
  have := Formalism.UG.P.csDual_sig_mem (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (hint j i)
  rwa [map_mul, map_natCast] at this

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ ((m : D.host.E) • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  show δ * embT D τ ((m : D.host.E) * z i j) = m • (δ * embT D τ (z i j))
  rw [map_mul, map_natCast, nsmul_eq_mul]
  ring

theorem matrix_move {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) {N N' : ℕ} (g₁ g₂ : GL (Fin N) A)
    (g₁' g₂' : GL (Fin N') A) (s s' : ℕ) (z : Matrix (Fin N') (Fin N) R) :
    ((g₂'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * (((s * s' : ℕ) : R) • z).map f *
      (g₂ : Matrix (Fin N) (Fin N) A) =
      ((s' : A) • ((g₂'⁻¹ * g₁' : GL (Fin N') A) : Matrix (Fin N') (Fin N') A)) *
      (((g₁'⁻¹ : GL (Fin N') A) : Matrix (Fin N') (Fin N') A) * z.map f * (g₁ : Matrix (Fin N) (Fin N) A)) *
      ((s : A) • ((g₁⁻¹ * g₂ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A)) := by
  have e1 : (((s * s' : ℕ) : R) • z).map f = ((s : A) * (s' : A)) • z.map f := by
    ext i j
    simp
  rw [e1]
  simp only [Units.val_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (g₁ : Matrix (Fin N) (Fin N) A), Units.mul_inv, Matrix.one_mul,
    ← Matrix.mul_assoc (g₁' : Matrix (Fin N') (Fin N') A), Units.mul_inv, Matrix.one_mul]

theorem smul_mem_La (D : D7) (hG : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : cc ≠ ⊥) {N N' : ℕ}
    (g₁ g₂ : GA D N) (g₁' g₂' : GA D N')
    {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h₁ : Moves D (g₁ : GL (Fin N) (AE D)) L₁) (h₁' : Moves D (g₁' : GL (Fin N') (AE D)) L₁')
    (h₂ : Moves D (g₂ : GL (Fin N) (AE D)) L₂) (h₂' : Moves D (g₂' : GL (Fin N') (AE D)) L₂')
    (s s' : ℕ)
    (hs : ∀ i j, (s : AE D) * (((g₁ : GL (Fin N) (AE D))⁻¹ * (g₂ : GL (Fin N) (AE D)) : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (hs' : ∀ i j, (s' : AE D) * (((g₂' : GL (Fin N') (AE D))⁻¹ * (g₁' : GL (Fin N') (AE D)) : GL (Fin N') (AE D)) :
      Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D)
    (x : VC D N N') (hx : x ∈ La D (tor0 D cc δ) L₁ L₁') : (s * s') • x ∈ La D (tor0 D cc δ) L₂ L₂' := by
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D hG cc δ hc N N' g₁ g₁' L₁ L₁' h₁ h₁' x hx
  rw [← pt_nsmul]
  refine GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic D hG cc δ hc N N' g₂ g₂' L₂ L₂' h₂ h₂' _ ?_
  have hI := (GlobalTheory.AdelicApprox.approx_mod_ideal D cc hc).2.2
  intro i j
  rw [matrix_move (inc D) (g₁ : GL (Fin N) (AE D)) _ (g₁' : GL (Fin N') (AE D)), Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine hI _ (hs l j) _ ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun r _ => hI _ (hs' i r) _ (hz r l)

end GlobalTheory.NormSum.LocAgree

open GlobalTheory.NormSum.LocAgree in

theorem GlobalTheory.NormSum.La_agree_of_trivAt : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' q : ℕ) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TrivAt D q (k : GL (Fin N) (AE D)) → TrivAt D q (k' : GL (Fin N') (AE D)) → Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → (∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₂ L₂') ∧ (∀ x ∈ La D (tor0 D cc δ) L₂ L₂', ∃ m : ℕ, Nat.Coprime m q ∧ m • x ∈ La D (tor0 D cc δ) L₁ L₁') := by
  intro D hG cc δ hc N N' q h k h' k' L₁ L₂ L₁' L₂' hk hk' h₁ h₁' h₂ h₂'
  obtain ⟨s, hsq, hs, hsi⟩ := exists_int_mul D q k hk
  obtain ⟨s', hsq', hs', hsi'⟩ := exists_int_mul D q k' hk'
  refine ⟨fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩,
    fun x hx => ⟨s * s', Nat.Coprime.mul_left hsq hsq', ?_⟩⟩
  · refine smul_mem_La D hG cc δ hc h (h * k) h' (h' * k') h₁ h₁' h₂ h₂' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi'
  · refine smul_mem_La D hG cc δ hc (h * k) h (h' * k') h' h₂ h₂' h₁ h₁' s s' ?_ ?_ x hx
    · rw [Subgroup.coe_mul, mul_inv_rev, inv_mul_cancel_right]; exact hsi
    · rw [Subgroup.coe_mul, inv_mul_cancel_left]; exact hs'
