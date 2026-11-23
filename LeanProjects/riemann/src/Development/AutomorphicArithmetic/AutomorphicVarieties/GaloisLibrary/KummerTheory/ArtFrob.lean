import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

section SlopeTestRemainingChoices

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω]

private theorem int_mem (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ A := by
  have h : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

omit [NumberField L] in
private theorem int_mem' (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  exact int_mem A (RingOfIntegers.isIntegral_coe x).algebraMap

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  classical
  let f : 𝓞 L →+* A :=
    { toFun := fun x => ⟨algebraMap L Ω (x : L), int_mem' A x⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap f ↔
      A.valuation (algebraMap L Ω (x : L)) < 1 := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hv : ∀ y : 𝓞 K, algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) y : 𝓞 L) : L) =
      algebraMap K Ω (y : K) := by
    intro y
    rw [IsScalarTower.algebraMap_apply K L Ω]
    congr 1
  obtain ⟨y, hyv, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hyP : algebraMap (𝓞 K) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap f := by
    rw [hmem, hv]
    exact (hA y).mpr hyv
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, Ideal.comap_isPrime f _, ?_⟩, ?_, ?_⟩
  · intro h
    rw [h, Ideal.mem_bot] at hyP
    apply hy0
    have h1 : algebraMap K Ω (y : K) = 0 := by
      rw [← hv, hyP]
      simp
    have h2 : (y : K) = 0 := (map_eq_zero_iff _ (algebraMap K Ω).injective).mp h1
    exact_mod_cast h2
  · intro x
    exact (hmem x).symm
  · refine ⟨Ideal.ext fun z => ?_⟩
    change z ∈ v.asIdeal ↔ algebraMap (𝓞 K) (𝓞 L) z ∈ (IsLocalRing.maximalIdeal A).comap f
    rw [hmem, hv]
    exact (hA z).symm

variable [IsGalois K L]

omit [NumberField K] [NumberField L] in
private theorem coe_res_smul (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) :=
  AlgEquiv.restrictNormal_commutes σ L (x : L)

private theorem res_frob {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal] {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  have hq : Nat.card (𝓞 K ⧸ w.asIdeal.under (𝓞 K)) = normV v := by
    rw [← h.over]
    rfl
  intro x
  rw [hq]
  refine (hw _).mp ?_
  simp only [MulSemiringAction.toAlgHom_apply, map_sub, map_pow, coe_res_smul]
  exact hσ.2 _ ((A.valuation_le_one_iff _).mpr (int_mem' A x))

end SlopeTestRemainingChoices

open GroundTheory.Global in
theorem UpperTheory.V.Kum.artFrob :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (σ : G K Ω), IsPlaceOver A v → IsFrob (F := K) A (normV v) σ → artCl K Ω σ = primeCl v := by
  intro K Ω _ _ _ _ _ A v σ hA hσ
  haveI := IsAlgClosure.isAlgClosed K (K := Ω)
  obtain ⟨w, hw, hlo⟩ := place_between (L := hilbertClassField K Ω) hA
  have hf := res_frob hw hσ
  have h2 := IsArithFrobAt.arithFrobAt (𝓞 K) Gal(hilbertClassField K Ω/K) w.asIdeal
  have hin := hf.mul_inv_mem_inertia h2
  have hcard : Nat.card (Ideal.inertia Gal(hilbertClassField K Ω/K) w.asIdeal) = 1 := by
    rw [natCard_inertia v w]
    exact (isUnramifiedIn_iff_ramificationIdx K (hilbertClassField K Ω) v).mp
      ((isUnramifiedEverywhere_hilbertClassField K Ω).1 v) w hlo
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot, mul_inv_eq_one] at hin
  unfold artCl primeCl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq,
    hilbertClassFieldArtinEquiv_mk0 K Ω v w]
  exact hin
