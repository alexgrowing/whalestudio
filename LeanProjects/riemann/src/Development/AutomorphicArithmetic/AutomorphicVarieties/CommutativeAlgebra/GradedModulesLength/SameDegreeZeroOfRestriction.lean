import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ZmOfHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsNotInP
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FixHolds
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.XProjZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.PrimeMaximalOrKernel

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem same_degree_zero_of_restriction {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] [Field K] [Algebra O K] {ξ ξ' : A →ₐ[O] K} (h : res0 𝒜 ξ = res0 𝒜 ξ') : Same0 𝒜 ξ ξ' :=
  fun b hb => DFunLike.congr_fun h ⟨b, hb⟩

theorem UpperTheory.V.Alg.M.zii_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    SpansCot x 𝒜 (-1) Q.F → SpansCot x 𝒜 (-2) Q.G → M2 𝒜 Q.ideal → M3 𝒜 K x Q.ideal →
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (idD 𝒜).map (algebraMap (𝒜 0) (mR Q)) ≤ p → (maximalIdeal (𝒜 0)).map (algebraMap (𝒜 0) (mR Q)) ≤ p := by
  intro O _ _ _ _ _ K _ _ _ _ A _ _ 𝒜 _ _ x hW r s r' s' m Q hF hG h2 h3 p hp hirr hsec hZ hD
  have hi := (zi_holds O A 𝒜 x hW r s r' s' m Q p hp hirr hsec hZ).1
  have hP : (p.comap (algebraMap (𝒜 0) (mR Q))).IsPrime := Ideal.comap_isPrime _ _
  rcases emb_holds O K A 𝒜 x Q.ideal h2 _ hP (fun b hb => hi b hb) with h | ⟨-, σ, hσ⟩
  · rw [Ideal.map_le_iff_le_comap, h]
  exfalso
  obtain ⟨ξm, hmS, hmP, hmN, hm0⟩ := zm_holds O K A 𝒜 x hW r s r' s' m Q p hp hirr hsec hZ hD σ hσ
  obtain ⟨ξp, hpS, hpN, hpP, hp0⟩ := zp_holds O K A 𝒜 x hW r s r' s' m Q p hp hirr hsec hZ hD σ hσ
  obtain ⟨ξ, hS, hN, hPz, h0⟩ := fix_holds O K A 𝒜 x hW r s r' s' m Q σ
    (by rw [hσ]; exact Ideal.map_le_iff_le_comap.1 hD)
    (fun b hb => by
      have : b ∈ RingHom.ker σ := by rw [hσ]; exact hi b hb
      exact this)
  have sm : Same0 𝒜 ξm ξ := same_degree_zero_of_restriction 𝒜 (hm0.trans h0.symm)
  have sp : Same0 𝒜 ξp ξ := same_degree_zero_of_restriction 𝒜 (hp0.trans h0.symm)
  by_cases hx : ξ = (Algebra.ofId O K).comp x
  · exact hmN (ct_holds O K A 𝒜 x hW r s r' s' m Q hF hG ξm hmS hmP (hx ▸ sm))
  · rcases h3 ξ hS hN hPz hx with h | h
    · exact h ⟨ξp, hpS, hpN, hpP, sp⟩
    · exact h ⟨ξm, hmS, hmP, hmN, sm⟩
