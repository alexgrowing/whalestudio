import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem val_le_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (A : ValuationSubring Ω) (x : 𝓞 K) : A.valuation (algebraMap K Ω (x : K)) ≤ 1 := by
  have hi : IsIntegral ℤ (algebraMap K Ω (x : K)) := (x.2 : IsIntegral ℤ (x : K)).map (IsScalarTower.toAlgHom ℤ K Ω)
  have hA : IsIntegral A (algebraMap K Ω (x : K)) := hi.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [A.valuation_le_one_iff, ← hy]
  exact y.2

private theorem exists_place {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) :
    ∃ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v := by
  let I : Ideal (𝓞 K) :=
    { carrier := {x | A.valuation (algebraMap K Ω (x : K)) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        have e : algebraMap K Ω ((a + b : 𝓞 K) : K) = algebraMap K Ω (a : K) + algebraMap K Ω (b : K) := by
          simp
        rw [e]
        exact Valuation.map_add_lt _ ha hb
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : algebraMap K Ω ((c • a : 𝓞 K) : K) = algebraMap K Ω (c : K) * algebraMap K Ω (a : K) := by
          simp
        rw [e, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one A c)) ha }
  have hmem : ∀ x : 𝓞 K, x ∈ I ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := fun _ => Iff.rfl
  have hprime : I.IsPrime := by
    refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
    · have := (hmem 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hmem] at hab
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      rw [hmem, not_lt] at h1 h2
      have e1 := le_antisymm (val_le_one A a) h1
      have e2 := le_antisymm (val_le_one A b) h2
      have e : algebraMap K Ω ((a * b : 𝓞 K) : K) = algebraMap K Ω (a : K) * algebraMap K Ω (b : K) := by
        simp
      rw [e, map_mul, e1, e2] at hab
      simp at hab
  have hne : I ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    intro hI
    have h1 : A.valuation (algebraMap F Ω (x : F)) < 1 := (hA x).2 hx
    have h2 : algebraMap (𝓞 F) (𝓞 K) x ∈ I := by
      rw [hmem]
      rw [IsScalarTower.algebraMap_apply F K Ω] at h1
      exact h1
    rw [hI, Ideal.mem_bot] at h2
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by simpa using h2))
  exact ⟨⟨I, hprime, hne⟩, fun x => (hmem x).symm⟩

theorem UpperTheory.GalN.V.L.wdown :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω], Unlinked (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → Unlinked r := by
  intro F Ω _ _ _ _ _ l _ n r K _ _ _ _ _ hK w hl A hA hfin
  obtain ⟨v, hv⟩ := exists_place (K := K) hA
  have hu : v.under (𝓞 F) = w := by
    have h1 : IsPlaceOver A (v.under (𝓞 F)) := GlobalTheory.AboveL.SatBC.isPlaceOver_under hv
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    exact (h1 x).symm.trans (hA x)
  have hN : normV v = normV w ^ v.asIdeal.inertiaDeg (𝓞 F) := by
    have := GlobalTheory.AboveL.SatBC.normV_under_pow F K v
    rwa [hu] at this
  have hf : 1 ≤ v.asIdeal.inertiaDeg (𝓞 F) := by
    rcases Nat.eq_zero_or_pos (v.asIdeal.inertiaDeg (𝓞 F)) with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hN
      have hne : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
      exact hne (Ideal.absNorm_eq_one_iff.1 hN)
    · exact h0
  have hlv : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro h
    apply hl
    have h1 := (hv _).2 h
    refine (hA _).1 ?_
    simpa using h1
  have hfinK : ((r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) '' (Ine (F := K) A : Set (G K Ω))).Finite := by
    refine hfin.subset ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨(AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) s, ⟨hs.1, hs.2⟩, rfl⟩
  obtain ⟨s, j, hj, hs, hno⟩ := hK v hlv A hv hfinK
  set f := v.asIdeal.inertiaDeg (𝓞 F) with hfdef
  have hpow : normV v ^ j = normV w ^ (f * j) := by rw [hN, pow_mul]
  refine ⟨(AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω) s, f * j, Nat.mul_pos hf hj, ⟨hs.1, ?_⟩, ?_⟩
  · intro x hx
    have := hs.2 x hx
    rw [hpow] at this
    exact this
  · rw [← hpow]
    exact hno
