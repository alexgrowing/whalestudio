import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IsFixMapIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Descent

open QuadraticAlgebra Matrix UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.One.splitS :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ →
        τ ∈ (algebraMap O K).range → (∃ u : Oˣ, algebraMap O K u = 2 - τ) → ∀ (c : K) (d m : EL Δ τ), IsDat c d m → ∀ S : Set (Sp Δ τ), IsFix O c d m S →
        (∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) ∧ (∀ x ∈ S, ∀ r : Lsq K Δ, IsInt O r → r • x ∈ S) ∧ (∀ x ∈ S, ((x.1, 0) : Sp Δ τ) ∈ S) ∧
        ∀ x ∈ S, ∀ v : Etau K τ, v.re ∈ (algebraMap O K).range → v.im ∈ (algebraMap O K).range → ((0, ofE Δ v * x.2) : Sp Δ τ) ∈ S := by
  intro O K _ _ _ _ _ Δ τ hL hτ hu2 c d m hD S hS
  obtain ⟨τ0, hτ0⟩ := hτ
  obtain ⟨u, hu⟩ := hu2
  obtain ⟨hfg, hdual, hstab⟩ := hS
  have hd := hD.d_norm
  have hu' : algebraMap O K ↑u⁻¹ * (2 - τ) = 1 := by
    rw [← hu, ← map_mul, Units.inv_mul, map_one]
  obtain ⟨s, rfl⟩ := hfg
  set P := Submodule.span O (↑s : Set (Sp Δ τ)) with hP
  have hsemi : ∀ x ∈ (P : Set (Sp Δ τ)), semi d x ∈ (P : Set (Sp Δ τ)) := by
    intro x hx
    rw [← hstab]
    exact ⟨x, hx, rfl⟩
  have hT : ∀ x ∈ (P : Set (Sp Δ τ)),
      ((x.1, ofE Δ (ω : Etau K τ) * x.2) : Sp Δ τ) ∈ (P : Set (Sp Δ τ)) := by
    intro x hx
    have h := hsemi _ (hsemi x hx)
    have e : semi d (semi d x) = ((x.1, ofE Δ (ω : Etau K τ) * x.2) : Sp Δ τ) := by
      simp only [semi, star_star, sigL_mul, sigL_sigL]
      rw [← mul_assoc, hd]
    rwa [e] at h
  have h3 : ∀ x ∈ (P : Set (Sp Δ τ)), ((x.1, 0) : Sp Δ τ) ∈ (P : Set (Sp Δ τ)) := by
    intro x hx
    have e : ((x.1, 0) : Sp Δ τ) = (↑u⁻¹ : O) • (((x.1, ofE Δ (ω : Etau K τ)
        * (ofE Δ (ω : Etau K τ) * x.2)) : Sp Δ τ)
        - τ0 • ((x.1, ofE Δ (ω : Etau K τ) * x.2) : Sp Δ τ) + x) := by
      ext <;> simp [ofE] <;> simp only [Algebra.smul_def, hτ0] <;>
        first | linear_combination (-x.1.re) * hu' | linear_combination (-x.1.im) * hu' | ring
    rw [e]
    exact P.smul_mem _ (P.add_mem (P.sub_mem (hT _ (hT x hx)) (P.smul_mem _ (hT x hx))) hx)
  refine ⟨fun x hx y hy => P.add_mem hx hy, ?_, h3, ?_⟩
  · intro x hx r hr
    rw [hdual]
    intro z hz
    have hh : herm c m z (r • x) = star r * herm c m z x := by
      have hs : star (sigL (r • x.2)) = star r • star (sigL x.2) := by
        ext <;> simp [sigL] <;> ring
      simp only [herm, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, star_mul, hs, mul_smul_comm, map_smul]
      ring
    rw [hh]
    obtain ⟨u0, s0, hs0, hΔeq⟩ := hL.even
    have hdesc := descent O K Δ hL s0⁻¹ u0
      (by rw [hΔeq, mul_assoc, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]) r
    exact IsIntegral.mul (hdesc.2 hr) (((hdual x).mp hx) z hz)
  · intro x hx v hvre hvim
    obtain ⟨a, ha⟩ := hvre
    obtain ⟨b, hb⟩ := hvim
    have e : ((0, ofE Δ v * x.2) : Sp Δ τ) = b • ((x.1, ofE Δ (ω : Etau K τ) * x.2) : Sp Δ τ)
        + a • x - (a + b) • ((x.1, 0) : Sp Δ τ) := by
      ext <;> simp [ofE] <;> simp only [Algebra.smul_def, map_add, ← ha, ← hb] <;> ring
    rw [e]
    exact P.sub_mem (P.add_mem (P.smul_mem _ (hT x hx)) (P.smul_mem _ hx)) (P.smul_mem _ (h3 x hx))
