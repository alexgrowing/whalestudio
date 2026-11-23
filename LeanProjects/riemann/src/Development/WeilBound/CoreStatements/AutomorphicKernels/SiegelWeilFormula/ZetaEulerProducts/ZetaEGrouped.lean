import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.NatCastPowCpow
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zetaE_grouped {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)))
      (GroundTheory.Global.continuedDedekindZeta E s)⁻¹ := by
  classical
  have hex : ∀ P : HeightOneSpectrum (𝓞 E), ∃ v : HeightOneSpectrum (𝓞 F), P ∈ fib F E v := by
    intro P
    refine ⟨⟨P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)), inferInstance, ?_⟩, ?_⟩
    · intro h
      exact P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    · rw [mem_fib]
      exact ⟨rfl⟩
  have huniq : ∀ (P : HeightOneSpectrum (𝓞 E)) (v w : HeightOneSpectrum (𝓞 F)),
      P ∈ fib F E v → P ∈ fib F E w → v = w := by
    intro P v w hv hw
    rw [mem_fib] at hv hw
    apply HeightOneSpectrum.ext
    rw [hv.over, hw.over]
  choose π hπ using hex
  let e : (Σ v : HeightOneSpectrum (𝓞 F), {P // P ∈ fib F E v}) ≃ HeightOneSpectrum (𝓞 E) :=
    { toFun := fun x => x.2.1
      invFun := fun P => ⟨π P, ⟨P, hπ P⟩⟩
      left_inv := by
        rintro ⟨v, P, hP⟩
        exact Sigma.subtype_ext (huniq P _ _ (hπ P) hP) rfl
      right_inv := fun P => rfl }
  obtain ⟨h, -⟩ := zeta_euler E hs
  have h' := (e.hasProd_iff).2 h
  exact h'.sigma (fun v => Finset.hasProd (fib F E v) _)

end PositivityTheory.Lord
