import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.Temper
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CompatPSOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagPol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem place_under {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} {p : ℕ}
    (hp0 : p ≠ 0) (hp : A.valuation (p : Ω) < 1) :
    ∃ w : HeightOneSpectrum (𝓞 F), IsPlaceOver A w ∧ (p : 𝓞 F) ∈ w.asIdeal := by
  have hA : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
      ((x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom).tower_top : IsIntegral A (algebraMap F Ω (x : F)))
    exact hy ▸ y.2
  let f : 𝓞 F →+* A := ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A hA
  have hf : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hm : (p : 𝓞 F) ∈ (IsLocalRing.maximalIdeal A).comap f := (hf _).1 (by simpa using hp)
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h => ?_⟩, hf, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hp0 (Nat.cast_eq_zero.1 hm)

private theorem pow_eq_one_of_kills {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    {M : ℕ} (hM : 1 ≤ M) : ∃ k : ℕ, 0 < k ∧ ∀ (C : Type) [Monoid C] (χ : G F Ω →* C), KillsMu M χ → ∀ s, χ s ^ k = 1 := by
  let S : SubMulAction (G F Ω) Ω :=
    { carrier := {ζ | ζ ^ M = 1}
      smul_mem' := fun s ζ (h : ζ ^ M = 1) => by
        show (s ζ) ^ M = 1
        rw [← map_pow, h, map_one] }
  haveI : Finite S := by
    classical
    refine Set.Finite.subset (s := ((nthRoots M (1 : Ω)).toFinset : Set Ω)) (Finset.finite_toSet _) fun ζ h => ?_
    exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ((mem_nthRoots hM).2 h))
  refine ⟨Nat.card (Equiv.Perm S), Nat.card_pos, fun C _ χ h s => ?_⟩
  rw [← map_pow]
  refine h _ fun ζ hζ => ?_
  have e : MulAction.toPermHom (G F Ω) S (s ^ Nat.card (Equiv.Perm S)) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg Subtype.val (DFunLike.congr_fun e ⟨ζ, hζ⟩)

private theorem charpoly_of_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} {r : H →* GL (Fin n) k}
    {κ : Fin n → H →* kˣ} (h : W.HasFlag r κ) (s : H) (b : GL (Fin n) k) :
    ((b * r s * b⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = ∏ i, (X - C ((κ i s : kˣ) : k)) := by
  obtain ⟨a, ha⟩ := h
  have h1 := Matrix.charpoly_of_upperTriangular ((a * r s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
    fun i j hij => (ha s).1 i j hij
  simp only [(ha s).2] at h1
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem UpperTheory.V.Th.freePU :
    Af.HypothesesH → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ (r : G K Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Continuous r → AutP ι r → Unl l M m r → FreeAt l r := by
  intro PH K Ω _ _ _ _ _ _ hK l _ hl ι n hn r M m hM hm hr haut hU B hB
  have P : Af.Hypotheses₂ := PH.toClassicalTheorems
  obtain ⟨w, hBw, hw⟩ := place_under (F := K) (Fact.out : l.Prime).ne_zero hB
  obtain ⟨π, hreg, hpol, hatt⟩ := haut
  obtain ⟨A, hA, κ, hF, hunl⟩ := hU w hw
  obtain ⟨χ, hχ, hflag, hκ⟩ := id hF
  obtain ⟨rc, hrc⟩ := P.exists_rec hA
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P K n π w
  obtain ⟨k, hk, hpow⟩ := pow_eq_one_of_kills (F := K) (Ω := Ω) hM
  have hflag' : W.HasFlag (r.comp (Dec (F := K) A).subtype) κ := hflag
  obtain ⟨g, hg, hfree⟩ := purLocS P K Ω l hl ι n r hr w A hA hw (rc (algNorm σ))
    (fun O _ _ _ Bw hj => by
      obtain ⟨h1, h2⟩ := Lev.compatPSOf P P.ss K hK n hn l Ω ι r π hr hreg hpol hatt
        w A hA O Bw hj
      obtain ⟨μ, hμ, -⟩ := Lev.flagPol K Ω l ι n M hM m r hr w A hA O Bw hj κ hF h1
      exact ⟨h1, fun _ => h2 σ hσ rc hrc ⟨μ, hμ⟩⟩)
    (temper P K Ω n (by omega) π hreg hpol w A hA rc hrc σ hσ) κ m k hflag' hm hk
    (fun i s hs => by
      rw [hκ i s hs, zpow_neg, mul_inv_cancel_comm]
      exact hpow _ _ (hχ i) _) (Or.inl hunl)
  obtain ⟨t, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := K) hA hBw
  refine ⟨t * g * t⁻¹, ?_, ?_, fun i => κ i g, hfree, ?_⟩
  · have h1 : (g : G K Ω) • A = A := g.2
    show (t * (g : G K Ω) * t⁻¹) • t • A = t • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, hg]
  · have h1 := charpoly_of_flag hflag' g (r t)
    rw [← h1]
    show (r (t * g * t⁻¹)).val.charpoly = _
    rw [map_mul, map_mul, map_inv]
    rfl
