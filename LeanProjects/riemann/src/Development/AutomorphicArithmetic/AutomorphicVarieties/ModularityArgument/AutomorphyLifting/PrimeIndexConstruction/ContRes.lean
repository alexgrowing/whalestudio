import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticFieldSplitPrimeTwoPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRingHomToLocalFieldInducingPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ComplexConjugationsAreConjugate
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
open UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem cont_res {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    [NumberField F] : Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem not_both {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := by
  intro hq
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (a : Ω) * p + (b : Ω) * q = 1 := by exact_mod_cast congrArg (Int.cast (R := Ω)) hab
  have hz : ∀ (z : ℤ) (x : Ω), A.valuation x < 1 → A.valuation (z * x) < 1 := fun z x hx => by
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 (intCast_mem A z)) zero_le hx
  have := A.valuation.map_add_lt (hz a _ hp) (hz b _ hq)
  rw [e, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Z.Win.Birth.mixOfP :
    MixSeedP → MixOfP := by
  intro hP Ω _ _ _ l hl c D T k₀ _ _ φ ι H C
  have hl2 : l ≠ 2 := H.good.l_odd
  obtain ⟨hsp, w, w', hne, hw, hw', hpl⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg l hl.out H.spl
  obtain ⟨hsp2, u, -, -, hu, -, -⟩ := UpperTheory.quadratic_field_split_prime_two_places Ω k₀ H.deg 2 Nat.prime_two H.sp2
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  have hker : ∀ g : G ℚ Ω, D.ξ g = 1 → up D.ξ g = 1 := fun g hg => by
    change Units.map _ (D.ξ g) = 1
    rw [hg, map_one]
  have lift : ∀ g : G T.F Ω, resQ T.F g ∈ k₀.fixingSubgroup → ∃ s : G k₀ Ω, resQ k₀ s = resQ T.F g := fun g hg =>
    ⟨k₀.fixingSubgroupEquiv ⟨_, hg⟩, rfl⟩
  obtain ⟨Au, hAu⟩ := exists_isPlaceOver Ω u
  have hAu2 : Au.valuation ((2 : ℕ) : Ω) < 1 := by
    have h := (hAu _).2 hu
    rwa [show algebraMap k₀ Ω (((2 : ℕ) : 𝓞 k₀) : k₀) = ((2 : ℕ) : Ω) from
      map_natCast ((algebraMap k₀ Ω).comp (algebraMap (𝓞 k₀) k₀)) 2] at h
  obtain ⟨g, hg, hg4⟩ := H.two.big2 Au (by simpa using hAu2)
  rw [Ne, C.al] at hg4
  obtain ⟨s, hs⟩ := lift g (H.sp2 Au hAu2 hg.1)
  have hsI : s ∈ Ine (F := k₀) Au := by
    have h1 : resQ T.F g ∈ Ine (F := ℚ) Au := ⟨hg.1, hg.2⟩
    rw [← hs] at h1
    exact ⟨h1.1, h1.2⟩
  obtain ⟨k, t, π, r, hk, ht, hkl, -, hc, hi, ha, hd, hr, ⟨haw, hrw⟩, hab⟩ :=
    hP k₀ Ω l hl2 (by rw [H.deg]; exact even_two) hsp ι ((up D.ξ).comp (resQ k₀))
      (Subgroup.isOpen_mono (H₁ := D.ξ.ker.comap (resQ k₀)) (fun x hx => hker _ hx)
        (H.good.xi_open.preimage (cont_res k₀)))
      (fun x hx => by
        have h1 : IsConj (resQ k₀ x) D.cc := UpperTheory.complex_conjugations_are_conjugate Ω _ _ hx H.good.isCC
        have h2 : D.ξ (resQ k₀ x) = -1 := by
          rw [← H.good.xi_odd]
          exact isConj_iff_eq.1 (D.ξ.map_isConj h1)
        change Units.map _ (D.ξ (resQ k₀ x)) = -1
        rw [h2]
        exact Units.ext (by simp))
      (fun A hA x hx => hker _ (H.two.xi A (fun p hp => by
        rw [Finset.mem_singleton.1 hp]
        exact not_both A ((Nat.coprime_primes hl.out Nat.prime_two).2 hl2) hA) ⟨hx.1, hx.2⟩))
      ⟨u, Au, (hsp2 u hu).1, hAu, fun h => hg4 (by
        have h1 : up D.ξ (resQ k₀ s) = 1 := h hsI
        rw [← hs, h1]
        simp [Cong])⟩
      ⟨s ^ 2, by
        rw [map_pow, ← pow_mul, MonoidHom.comp_apply, hs]
        exact hg4⟩
      (fun A hA => by
        obtain ⟨x, hx, hx4⟩ := H.two.bigL A hA
        rw [Ne, C.al] at hx4
        obtain ⟨y, hy⟩ := lift x (H.spl A hA hx)
        have h1 : resQ T.F x ∈ Dec (F := ℚ) A := hx
        rw [← hy] at h1
        refine ⟨y ^ 4, pow_mem (show y ∈ Dec (F := k₀) A from h1) 4, ?_⟩
        rw [map_pow, MonoidHom.comp_apply, hy]
        exact hx4)
      {w} ⟨w, rfl, hw⟩ ⟨w', hne.symm, hw'⟩
  obtain ⟨h1, h1'⟩ := (hab w hw).1 rfl
  obtain ⟨h2, h2'⟩ := (hab w' hw').2 hne.symm
  obtain ⟨he, he'⟩ := UpperTheory.exists_ringHom_to_localField_inducing_place k₀ l ι
  obtain ⟨τ, hτ⟩ := he w hw
  obtain ⟨τ', hτ'⟩ := he w' hw'
  refine ⟨k, t, r, And.symm ⟨hrw, ?_⟩⟩
  refine ⟨hk, ht, hkl, hc, hi, ⟨π, ha, _, _, fun h => hne (he' w w' τ τ' hτ hτ' h), h1' τ hτ, h2' τ' hτ'⟩,
    hd, hr, haw, fun A A' hA x hx hAA => ?_⟩
  rcases hpl A A' hA x hx hAA with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨h1 A a, h2 A' b⟩
  · exact Or.inr ⟨h2 A a, h1 A' b⟩
