import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open UpperTheory.V.Af

namespace UpperTheory.V.Z.Win.Birth

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def conjEquiv (g : GL (Fin n) k) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))
    (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, mul_inv_cancel]; simp)
    (by rw [← Matrix.mulVecLin_mul, ← Units.val_mul, inv_mul_cancel]; simp)

private theorem conjEquiv_apply (g : GL (Fin n) k) (v : Fin n → k) :
    conjEquiv g v = (g : Matrix (Fin n) (Fin n) k).mulVec v := rfl

private theorem intertwine {r r' : Γ →* GL (Fin n) k} {g : GL (Fin n) k}
    (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k).mulVec (conjEquiv g v) =
      conjEquiv g ((r s : Matrix (Fin n) (Fin n) k).mulVec v) := by
  have h : (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
      (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) := by
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  simp only [conjEquiv_apply, Matrix.mulVec_mulVec, h]

private theorem ss_of_conj {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  intro W hW
  have h0 : IsInv r (W.comap (conjEquiv g).toLinearMap) := by
    intro s v hv
    have hv' : conjEquiv g v ∈ W := hv
    show conjEquiv g _ ∈ W
    rw [← intertwine hg]
    exact hW s _ hv'
  obtain ⟨W', hW', hc⟩ := H _ h0
  refine ⟨W'.map (conjEquiv g).toLinearMap, ?_, ?_⟩
  · rintro s _ ⟨v, hv, rfl⟩
    exact ⟨(r s : Matrix (Fin n) (Fin n) k).mulVec v, hW' s v hv, (intertwine hg s v).symm⟩
  · have hm := (Submodule.orderIsoMapComap (conjEquiv g)).isCompl hc
    have hW2 : (Submodule.orderIsoMapComap (conjEquiv g)) (W.comap (conjEquiv g).toLinearMap) = W := by
      ext x
      simp [Submodule.orderIsoMapComap_apply, Submodule.mem_map]
    rw [hW2] at hm
    exact hm

end Conj

private theorem frob_of_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : RepIso r r')
    {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂ} (H : FrobEig ι r w B) : FrobEig ι r' w B := by
  obtain ⟨g, hg⟩ := h
  intro A hA
  obtain ⟨h1, h2⟩ := H A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · rw [hg s, h1 s hs, mul_one, mul_inv_cancel]
  · rw [hg σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact h2 σ hσ

theorem prIso : PrIso := by
  intro F Ω _ _ _ _ _ _ l _ ι n r r' h
  rintro ⟨π, h1, h2, h3⟩
  exact ⟨π, h1, ⟨ss_of_conj h h2.1, h2.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, frob_of_conj h hB'⟩⟩, h3⟩

end UpperTheory.V.Z.Win.Birth
