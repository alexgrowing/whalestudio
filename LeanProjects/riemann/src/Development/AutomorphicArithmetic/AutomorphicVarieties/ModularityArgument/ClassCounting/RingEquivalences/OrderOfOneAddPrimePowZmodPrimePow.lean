import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.MinusLenLeOfCl
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClMapBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClSubUniv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage

section

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base
open UpperTheory.V.ZK

namespace PositivityTheory.QuaternionShaBounds

def LayEx : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l c ν : ℕ) [Fact l.Prime],
    TopRoot l c L → c ≤ ν → ∃ (ζ : (𝓞 (Kum.Fn L Ω l ν))ˣ) (γ : Kum.Fn L Ω l ν ≃ₐ[L] Kum.Fn L Ω l ν), Lay l c ν ζ γ ∧
      ∃ g : G L Ω, IsLift γ.toRingEquiv g.toRingEquiv ∧
        ((Kum.cycR L Ω l ν g : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 + (l : ZMod (l ^ ν)) ^ c

def ClInj : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l c ν E : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [NumberField K] [Algebra L K] [Algebra K Ω] [IsScalarTower L K Ω] (γ : K ≃ₐ[L] K) (g : G L Ω),
    IsLift γ.toRingEquiv g.toRingEquiv →
    ((Kum.cycR L Ω l ν g : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 + (l : ZMod (l ^ ν)) ^ c →
    ∃ f : {θ : Kum.ClEq K l (qzG L Ω l (E : ℤ)) // ∀ x, (l : ℤ_[l]) ^ ν • θ.1 x = 0} → ZK.EqHom γ ((1 + l ^ c) ^ E) (l ^ ν),
      Function.Injective f

def ShaAsm : Prop := LayEx → ClInj → SSha

def ShaMono : Prop :=
  ∀ (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (l j E : ℕ) [Fact l.Prime]
    [IsCyclotomicExtension {l ^ j} L L'], HasMuQ l L → 1 ≤ E → shaInv L l E ≤ shaInv L' l E

def LayDisc : Prop :=
  ∀ (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (q : ℕ) [NeZero q]
    [IsCyclotomicExtension {q} L L'],
    (discr L').natAbs ≤ (discr L).natAbs ^ Module.finrank L L' * q ^ Module.finrank ℚ L'

def LayField : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (l E : ℕ) [Fact l.Prime], HasMuQ l L → 1 ≤ E →
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (c : ℕ) (_ : IsCyclotomicExtension {l ^ c} L L'),
      IsTotallyComplex L' ∧ TopRoot l c L' ∧ 2 * E + 1 < l ^ c ∧ 2 * E + 1 < nrComplexPlaces L' ∧
      Module.finrank L L' ≤ (Module.finrank ℚ L + 1) * (4 * E + 4) ∧ l ^ c ≤ 2 * Module.finrank ℚ L'

def LocalH0Terms : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (D : LData L Ω l), HasMuQ l L → ∀ e : ℕ, 1 ≤ e → ∀ w : D.S, ∃ t : ℕ,
      Module.length ℤ_[l] (H0 ((qzTw D (e : ℤ)).comp (locFam D.S D.A w))) = t ∧ l ^ t ≤ 4 * Module.finrank ℚ L * e

def FinalAsm : Prop := LocalH0Terms → SFinal

end PositivityTheory.QuaternionShaBounds

end

end

section

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base
open UpperTheory.V.ZK

namespace PositivityTheory.QuaternionShaBounds.CyclotomicLayerExistence

theorem orderOf_one_add_prime_pow_zmod_prime_pow (l c k : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (h2 : l = 2 → 2 ≤ c) :
    orderOf (1 + (l : ZMod (l ^ (k + c))) ^ c) = l ^ k := by
  have hlc : c + 2 ≤ l * c := by
    by_cases h : l = 2
    · subst h; have := h2 rfl; omega
    · have h3 : 3 ≤ l := by have := hl.two_le; omega
      have := Nat.mul_le_mul_right c h3
      omega
  have hnd : ¬ (l : ℤ) ∣ 1 := fun h => by
    have h1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg l) h
    have : l = 1 := by exact_mod_cast h1
    exact hl.one_lt.ne' this
  have := ZMod.orderOf_one_add_mul_prime_pow hl c (by omega) hlc 1 hnd k
  simpa using this

theorem unit_aux (l c : ℕ) [Fact l.Prime] (hc : 1 ≤ c) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ c := by
  have hl : l.Prime := Fact.out
  have h1 : ‖(l : ℤ_[l]) ^ c‖ < 1 :=
    (PadicInt.norm_lt_one_iff_dvd _).2 (dvd_pow_self _ (by omega))
  have h2 : ‖(1 : ℤ_[l]) + (l : ℤ_[l]) ^ c‖ = 1 := by
    have : ‖(1 : ℤ_[l])‖ ≠ ‖(l : ℤ_[l]) ^ c‖ := by rw [norm_one]; exact h1.ne'
    rw [PadicInt.norm_add_eq_max_of_ne this, norm_one]
    exact max_eq_left h1.le
  exact ⟨(PadicInt.isUnit_iff.2 h2).unit, rfl⟩

end PositivityTheory.QuaternionShaBounds.CyclotomicLayerExistence

open PositivityTheory.QuaternionShaBounds.CyclotomicLayerExistence in
theorem PositivityTheory.QuaternionShaBounds.LayEx_holds : PositivityTheory.QuaternionShaBounds.LayEx := by
  intro L Ω _ _ _ _ _ l c ν _ hT hcν
  have hl : l.Prime := Fact.out
  obtain ⟨hc1, hc2, ⟨z, hz⟩, hnz⟩ := hT
  obtain ⟨k, rfl⟩ : ∃ k, ν = k + c := ⟨ν - c, by omega⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero (l ^ (k + c)) := ⟨pow_ne_zero _ hl.ne_zero⟩

  obtain ⟨hM1, -, hM3, -⟩ := UpperTheory.V.Tower.muQ L Ω l
  have hc0 : UpperTheory.V.Tower.cZero l L = c := by
    have a := (hM1 c).1 ⟨z, hz⟩
    have b : ¬ c + 1 ≤ UpperTheory.V.Tower.cZero l L := fun h => hnz ((hM1 (c + 1)).2 h)
    omega
  have hmu : HasMuQ l L := by
    refine hM3.2 ?_
    rw [hc0]; unfold qExp; split_ifs with h
    · exact hc2 h
    · exact hc1

  obtain ⟨u, hu⟩ := unit_aux l c hc1
  have hur : u ∈ (cycZ L Ω l).range := by
    rw [UpperTheory.V.Tower.cycRange L Ω l hmu, hc0, KStar.TotallyRealRoots.mem_princ, hu]
    simp
  obtain ⟨g, hg⟩ := hur
  have hgR : ((Kum.cycR L Ω l (k + c) g : (ZMod (l ^ (k + c)))ˣ) : ZMod (l ^ (k + c))) =
      1 + (l : ZMod (l ^ (k + c))) ^ c := by
    show PadicInt.toZModPow (k + c) ((cycZ L Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = _
    rw [hg, hu]
    simp

  set F := Kum.Fn L Ω l (k + c)
  haveI hcyc : IsCyclotomicExtension {l ^ (k + c)} L F := (Kum.fnCyc L Ω l (k + c)).1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hgal : IsGalois L F := IsCyclotomicExtension.isGalois {l ^ (k + c)} L F
  let γ : F ≃ₐ[L] F := AlgEquiv.restrictNormalHom F g
  have hlift : IsLift γ.toRingEquiv g.toRingEquiv := (UpperTheory.V.Base.galQuot L F Ω).2.2 g
  have hcomm : ∀ x : F, algebraMap F Ω (γ x) = g (algebraMap F Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes g F x

  set ζ : F := IsCyclotomicExtension.zeta (l ^ (k + c)) L F
  have hζ : IsPrimitiveRoot ζ (l ^ (k + c)) := IsCyclotomicExtension.zeta_spec (l ^ (k + c)) L F
  have hpos : 0 < l ^ (k + c) := pow_pos hl.pos _
  let zO : 𝓞 F := ⟨ζ, hζ.isIntegral hpos⟩
  have hzO : IsPrimitiveRoot zO (l ^ (k + c)) :=
    hζ.of_map_of_injective (f := algebraMap (𝓞 F) F) RingOfIntegers.coe_injective
  let ζu : (𝓞 F)ˣ := (hzO.isUnit hpos.ne').unit
  have hζu : ((ζu : 𝓞 F) : F) = ζ := rfl
  have hprim : IsPrimitiveRoot ζu (l ^ (k + c)) :=
    IsPrimitiveRoot.coe_units_iff.1 (by rw [IsUnit.unit_spec]; exact hzO)

  have hact : γ ζ = ζ ^ (1 + l ^ c) := by
    apply (algebraMap F Ω).injective
    rw [hcomm, map_pow]
    have ht : (algebraMap F Ω ζ) ^ l ^ (k + c) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have hs := cyclotomicCharacter.spec l g.toRingEquiv _ ht
    have e : cycZ L Ω l g = cyclotomicCharacter Ω l g.toRingEquiv := rfl
    have hv : ((cyclotomicCharacter Ω l g.toRingEquiv).val.toZModPow (k + c)) =
        ((1 + l ^ c : ℕ) : ZMod (l ^ (k + c))) := by
      rw [← e, hg, hu]; simp
    rw [hv, ZMod.val_natCast, ← pow_eq_pow_mod _ ht] at hs
    exact hs

  have hA : ((hζ.autToPow L γ : (ZMod (l ^ (k + c)))ˣ) : ZMod (l ^ (k + c))) =
      1 + (l : ZMod (l ^ (k + c))) ^ c := by
    have h1 := hζ.autToPow_spec L γ
    rw [hact, pow_eq_pow_mod _ hζ.pow_eq_one, pow_eq_pow_mod (1 + l ^ c) hζ.pow_eq_one] at h1
    have h2 := hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) h1
    rw [← ZMod.natCast_zmod_val ((hζ.autToPow L γ : (ZMod (l ^ (k + c)))ˣ) : ZMod (l ^ (k + c))),
      (ZMod.natCast_eq_natCast_iff' _ _ _).2 h2]
    simp
  have hord : orderOf γ = l ^ k := by
    rw [← orderOf_injective _ (hζ.autToPow_injective L) γ, ← orderOf_units, hA]
    exact orderOf_one_add_prime_pow_zmod_prime_pow l c k hl hc1 hc2

  have hdeg : Module.finrank L F ≤ l ^ k := by
    obtain ⟨i, -, hi⟩ := (hz.map_of_injective (algebraMap L F).injective).eq_pow_of_pow_eq_one
      (ξ := ζ ^ l ^ k) (by rw [← pow_mul, ← pow_add, hζ.pow_eq_one])
    rw [(hζ.powerBasis L).finrank, IsPrimitiveRoot.powerBasis_dim]
    have hne := Polynomial.X_pow_sub_C_ne_zero (pow_pos hl.pos k) (z ^ i)
    have hdvd : minpoly L ζ ∣ Polynomial.X ^ l ^ k - Polynomial.C (z ^ i) := by
      refine minpoly.dvd L ζ ?_
      simp [map_pow, hi]
    have := Polynomial.natDegree_le_of_dvd hdvd hne
    rwa [Polynomial.natDegree_X_pow_sub_C] at this
  have hgen : Subgroup.zpowers γ = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [Nat.card_zpowers, hord, IsGalois.card_aut_eq_finrank]
    exact hdeg
  refine ⟨ζu, γ, ⟨hgal, hprim, fun σ => by rw [hgen]; trivial, ?_, ?_, hc1, hc2, hcν⟩, g, hlift, hgR⟩
  · rw [hζu]; exact hact
  · rw [hord, Nat.add_sub_cancel]

end

section

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base
open UpperTheory.V.ZK

namespace PositivityTheory.QuaternionShaBounds.ClassGroupInjection

def toHom {C M : Type} [CommGroup C] [AddCommGroup M] (θ : C → M) (h : ∀ a b, θ (a * b) = θ a + θ b) :
    C →* Multiplicative M where
  toFun c := Multiplicative.ofAdd (θ c)
  map_one' := by
    have h1 := h 1 1
    rw [one_mul] at h1
    have h2 : θ 1 = 0 := by
      have h3 : θ 1 + θ 1 - θ 1 = θ 1 - θ 1 := by rw [← h1]
      simpa using h3
    rw [h2]
    rfl
  map_mul' a b := by rw [h]; rfl

theorem toHom_apply {C M : Type} [CommGroup C] [AddCommGroup M] (θ : C → M) (h : ∀ a b, θ (a * b) = θ a + θ b)
    (c : C) : toHom θ h c = Multiplicative.ofAdd (θ c) := rfl

theorem theta_prod {C M ι : Type} [CommGroup C] [AddCommGroup M] (θ : C → M) (h : ∀ a b, θ (a * b) = θ a + θ b)
    (s : Finset ι) (f : ι → C) (n : ι → ℤ) : θ (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i • θ (f i) := by
  have h1 : θ (∏ i ∈ s, f i ^ n i) = Multiplicative.toAdd (toHom θ h (∏ i ∈ s, f i ^ n i)) := rfl
  rw [h1, map_prod, toAdd_prod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zpow, toAdd_zpow, toHom_apply, toAdd_ofAdd]

theorem theta_one {C M : Type} [CommGroup C] [AddCommGroup M] (θ : C → M) (h : ∀ a b, θ (a * b) = θ a + θ b) :
    θ 1 = 0 := by
  have h1 : θ 1 = Multiplicative.toAdd (toHom θ h 1) := rfl
  rw [h1, map_one, toAdd_one]

theorem ordP_eq_ordv {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) :
    ordP P α = Kum.ordv P α := by
  rw [ordP, Kum.ordv, ← HeightOneSpectrum.valuationOfNeZero_eq]
  rfl

theorem prod_primeCl {F : Type} [Field F] [NumberField F] (α : Fˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), Kum.primeCl v ^ Kum.ordv v α = 1 := by
  have h := (Kum.clProd F).2.2.2 α
  simpa [Kum.radCl] using h

theorem actP_mem {L F : Type} [Field L] [Field F] [NumberField F] [Algebra L F] (σ : F ≃ₐ[L] F)
    (P : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    x ∈ P.asIdeal ↔ RingOfIntegers.mapRingEquiv σ.toRingEquiv x ∈ (actP σ P).asIdeal := by
  simp only [actP, HeightOneSpectrum.equivOfRingEquiv, Equiv.coe_fn_mk]
  change _ ↔ _ ∈ Ideal.comap _ P.asIdeal
  rw [Ideal.mem_comap]
  simp

end PositivityTheory.QuaternionShaBounds.ClassGroupInjection

namespace PositivityTheory.QuaternionShaBounds

open ClassGroupInjection

theorem ClInj_holds : ClInj := by
  intro L Ω _ _ _ _ _ l c ν E _ K _ _ _ _ _ γ g hlift hcyc
  obtain ⟨ι, hιinj, hιrange, hιsmul⟩ := Kum.zmodToQZ l ν
  have hadd : ∀ θ : Kum.ClEq K l (qzG L Ω l (E : ℤ)), ∀ a b, θ.1 (a * b) = θ.1 a + θ.1 b :=
    fun θ => (Submodule.mem_inf.1 θ.2).1.1
  have hcond : ∀ θ : Kum.ClEq K l (qzG L Ω l (E : ℤ)), ∀ (h : G L Ω) (τ : K ≃+* K), IsLift τ h.toRingEquiv →
      ∀ c, θ.1 (Kum.clMap τ c) = qzG L Ω l (E : ℤ) h (θ.1 c) := by
    intro θ h τ hτ c
    have h1 := (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 θ.2).2 h
    exact h1 τ hτ c
  have hinv : IsLift (γ⁻¹ : K ≃ₐ[L] K).toRingEquiv (g⁻¹ : G L Ω).toRingEquiv := by
    have h1 : ∀ y : K, g (algebraMap K Ω y) = algebraMap K Ω (γ y) := hlift
    intro x
    show (g⁻¹ : G L Ω) (algebraMap K Ω x) = algebraMap K Ω ((γ⁻¹ : K ≃ₐ[L] K) x)
    rw [AlgEquiv.aut_inv, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, h1, AlgEquiv.apply_symm_apply]
  have hcyc' : PadicInt.toZModPow ν ((cycZ L Ω l g : ℤ_[l]) ^ E) = (((1 + l ^ c) ^ E : ℕ) : ZMod (l ^ ν)) := by
    have h1 : PadicInt.toZModPow ν (cycZ L Ω l g : ℤ_[l]) = 1 + (l : ZMod (l ^ ν)) ^ c := hcyc
    rw [map_pow, h1]
    push_cast
    rfl
  let F : {θ : Kum.ClEq K l (qzG L Ω l (E : ℤ)) // ∀ x, (l : ℤ_[l]) ^ ν • θ.1 x = 0} →
      HeightOneSpectrum (𝓞 K) → ZMod (l ^ ν) :=
    fun θ P => Function.invFun ι (θ.1.1 (Kum.primeCl P))
  have hF : ∀ θ P, ι (F θ P) = θ.1.1 (Kum.primeCl P) := fun θ P =>
    Function.invFun_eq ((hιrange _).2 (θ.2 _))
  have hmem : ∀ θ, F θ ∈ EqHom γ ((1 + l ^ c) ^ E) (l ^ ν) := by
    intro θ
    refine ⟨fun α => ?_, fun P => ?_⟩
    · have hfin := (Kum.clProd K).2.2.1 α
      rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ ?_]
      · apply hιinj
        rw [map_zero, map_sum]
        have h1 : ∀ P, ι ((ordP P α : ZMod (l ^ ν)) * F θ P) = Kum.ordv P α • θ.1.1 (Kum.primeCl P) := by
          intro P
          rw [ordP_eq_ordv, ← zsmul_eq_mul, map_zsmul, hF]
        simp only [h1]
        rw [← theta_prod _ (hadd θ.1), ← finprod_eq_prod_of_mulSupport_subset, prod_primeCl, theta_one _ (hadd θ.1)]
        intro P hP
        simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
        intro h0
        apply hP
        simp [h0]
      · intro P hP
        simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
        intro h0
        apply hP
        simp [ordP_eq_ordv, h0]
    · apply hιinj
      have h2 : Kum.clMap (γ⁻¹ : K ≃ₐ[L] K).toRingEquiv (Kum.primeCl P) = Kum.primeCl (actP γ⁻¹ P) :=
        (Kum.clMapBasic K K K (γ⁻¹ : K ≃ₐ[L] K).toRingEquiv (γ⁻¹ : K ≃ₐ[L] K).toRingEquiv).2.2.2 P _
          (actP_mem γ⁻¹ P)
      rw [hF, ← h2, hcond θ.1 g⁻¹ _ hinv, qzG_apply, ← hF, map_inv, inv_zpow', neg_neg, zpow_natCast,
        Units.val_pow_eq_pow_val, ← hιsmul, hcyc']
  refine ⟨fun θ => ⟨F θ, hmem θ⟩, fun θ₁ θ₂ heq => ?_⟩
  have hP : ∀ P, θ₁.1.1 (Kum.primeCl P) = θ₂.1.1 (Kum.primeCl P) := fun P => by
    rw [← hF, ← hF]
    exact congrArg ι (congrFun (congrArg Subtype.val heq) P)
  have h1 : toHom _ (hadd θ₁.1) = toHom _ (hadd θ₂.1) := by
    refine MonoidHom.eq_of_eqOn_dense (Kum.clSubUniv K) ?_
    rintro _ ⟨P, -, rfl⟩
    simp only [toHom_apply, hP P]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h2 := DFunLike.congr_fun h1 x
  simpa only [toHom_apply, EmbeddingLike.apply_eq_iff_eq] using h2

end PositivityTheory.QuaternionShaBounds

end

end

section

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank
  UpperTheory.V.Base
open UpperTheory.V.ZK

namespace PositivityTheory.QuaternionShaBounds.ShaAssumptions

theorem tors_fun (l : ℕ) [Fact l.Prime] {X : Type} [Finite X] (θ : X → QZ l) :
    ∃ r : ℕ, ∀ x, (l : ℤ_[l]) ^ r • θ x = 0 := by
  have h : ∀ x, ∃ k : ℕ, l ^ k • θ x = 0 := fun x => (Kum.qzBasic l).2.1 (θ x)
  choose k hk using h
  cases nonempty_fintype X
  refine ⟨Finset.univ.sup k, fun x => ?_⟩
  have hx : k x ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ x)
  have h1 : (l : ℤ_[l]) ^ k x • θ x = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact hk x
  rw [← Nat.sub_add_cancel hx, pow_add, mul_smul, h1, smul_zero]

theorem pow_smul_of_le (l : ℕ) [Fact l.Prime] {r ν : ℕ} (h : r ≤ ν) {y : QZ l}
    (hy : (l : ℤ_[l]) ^ r • y = 0) : (l : ℤ_[l]) ^ ν • y = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hy, smul_zero]

theorem procyc_of_top (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (l c : ℕ) [Fact l.Prime] (h : TopRoot l c L) : Kum.Procyc L Ω l := by
  have hM := Tower.muQ L Ω l
  by_cases h2 : l = 2
  · refine hM.2.2.2.2.2 (Or.inr (hM.2.2.1.2 ?_))
    have hc : c ≤ Tower.cZero l L := (hM.1 c).1 h.2.2.1
    have hq : qExp l ≤ c := by
      unfold qExp; rw [if_pos h2]; exact h.2.1 h2
    omega
  · exact Or.inl h2

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]

def Good (E ν : ℕ) (φ : Kum.Uinf L Ω l → QZ l) : Prop :=
  ∃ ψ ∈ Kum.EqHom l (Kum.Un L Ω l ν) (qzG L Ω l (E : ℤ)),
    Kum.restr ℤ_[l] (QZ l) (cycU_le_levU l ⊤ ν) ψ = φ ∧ (l : ℤ_[l]) ^ ν • ψ = 0

theorem up (E : ℕ) {n m : ℕ} (h : n ≤ m) (ψ : Kum.Un L Ω l n → QZ l)
    (hψ : ψ ∈ Kum.EqHom l (Kum.Un L Ω l n) (qzG L Ω l (E : ℤ))) :
    ∃ ψ' ∈ Kum.EqHom l (Kum.Un L Ω l m) (qzG L Ω l (E : ℤ)),
      Kum.restr ℤ_[l] (QZ l) (cycU_le_levU l ⊤ m) ψ' = Kum.restr ℤ_[l] (QZ l) (cycU_le_levU l ⊤ n) ψ ∧
      ∀ u, ∃ v, ψ' u = ψ v :=
  ⟨Kum.restr ℤ_[l] (QZ l) (Kum.levU_anti (l := l) ⊤ h) ψ,
    (Kum.restrMem L Ω l _ _ _ ℤ_[l] (QZ l) _).2.1 ⟨ψ, hψ, rfl⟩, rfl, fun _ => ⟨_, rfl⟩⟩

theorem good_of (E : ℕ) (φ : Kum.Uinf L Ω l → QZ l)
    (hφ : φ ∈ Kum.EqHom l (Kum.Uinf L Ω l) (qzG L Ω l (E : ℤ))) :
    ∃ n, ∀ ν, n ≤ ν → Good (L := L) (Ω := Ω) E ν φ := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨n, ψ, hψ, hψφ⟩ := (Kum.eqExt L Ω l l ⊤ ℤ_[l] (QZ l) (qzG L Ω l (E : ℤ)) hl0 (by simp)
    (Kum.locConst_qzG _)).1 φ hφ
  obtain ⟨ψ₀, hψ₀, hψ₀φ, -⟩ := up E (le_max_left n 2) ψ hψ
  have hpe := (Kum.pullEq L Ω (Kum.Fn L Ω l (max n 2)) _ (Kum.galOf_Fn (max n 2)).ge l ℤ_[l] (QZ l)
    (qzG L Ω l (E : ℤ)) hl0 (Kum.galOf_Fn (max n 2)).le
    (Or.inl ((Kum.fnCyc L Ω l (max n 2)).2.2 (le_max_right _ _)))).1
  have hm := hψ₀
  rw [← hpe] at hm
  obtain ⟨θ₀, -, hθ₀⟩ := hm
  obtain ⟨r, hr⟩ := tors_fun l θ₀
  refine ⟨max (max n 2) r, fun ν hν => ?_⟩
  obtain ⟨ψ', hψ', hψ'φ, hv⟩ := up E ((le_max_left _ _).trans hν) ψ₀ hψ₀
  refine ⟨ψ', hψ', hψ'φ.trans (hψ₀φ.trans hψφ), ?_⟩
  funext u
  obtain ⟨v, hv⟩ := hv u
  rw [Pi.smul_apply, hv, ← hθ₀, Kum.clPull_apply, Pi.zero_apply]
  exact pow_smul_of_le l ((le_max_right _ _).trans hν) (hr _)

theorem card_le (hLay : LayEx) (hCl : ClInj) (c E B : ℕ) (hTop : TopRoot l c L)
    (hB : ∀ (F : Type) [Field F] [NumberField F] [Algebra L F] (ν : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F),
      Lay l c ν ζ γ →
      Finite (ZK.EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) ∧ Nat.card (ZK.EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) ≤ B)
    (ν : ℕ) (hcν : c ≤ ν) (h2ν : 2 ≤ ν) (T : Finset (Kum.Uinf L Ω l → QZ l))
    (hT : ∀ φ ∈ T, Good (L := L) (Ω := Ω) E ν φ) : T.card ≤ B := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨ζ, γ, hL, g, hlift, hcyc⟩ := hLay L Ω l c ν hTop hcν
  obtain ⟨f, hf⟩ := hCl L Ω l c ν E (Kum.Fn L Ω l ν) γ g hlift hcyc
  obtain ⟨hfin, hcard⟩ := hB (Kum.Fn L Ω l ν) ν ζ γ hL
  have hpe := (Kum.pullEq L Ω (Kum.Fn L Ω l ν) _ (Kum.galOf_Fn ν).ge l ℤ_[l] (QZ l) (qzG L Ω l (E : ℤ)) hl0
    (Kum.galOf_Fn ν).le (Or.inl ((Kum.fnCyc L Ω l ν).2.2 h2ν))).1
  have hinj := (Kum.pullMem L Ω (Kum.Fn L Ω l ν) _ (Kum.galOf_Fn ν).ge l ℤ_[l] (QZ l) hl0).2
    (Kum.galOf_Fn ν).le
  have hpick : ∀ φ : T, ∃ θ : {θ : Kum.ClEq (Kum.Fn L Ω l ν) l (qzG L Ω l (E : ℤ)) //
      ∀ x, (l : ℤ_[l]) ^ ν • θ.1 x = 0},
      Kum.restr ℤ_[l] (QZ l) (cycU_le_levU l ⊤ ν)
        (Kum.clPull (Kum.Fn L Ω l ν) (Kum.galOf_Fn ν).ge ℤ_[l] (QZ l) θ.1.1) = φ.1 := by
    intro φ
    obtain ⟨ψ, hψ, hψφ, hψt⟩ := hT φ.1 φ.2
    have hm := hψ
    rw [← hpe] at hm
    obtain ⟨θ, hθ, rfl⟩ := hm
    refine ⟨⟨⟨θ, hθ⟩, fun x => ?_⟩, hψφ⟩
    have h0 : Kum.clPull (Kum.Fn L Ω l ν) (Kum.galOf_Fn ν).ge ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ ν • θ) =
        Kum.clPull (Kum.Fn L Ω l ν) (Kum.galOf_Fn ν).ge ℤ_[l] (QZ l) 0 := by
      rw [map_smul, hψt, map_zero]
    exact congrFun (hinj h0) x
  choose pick hpick using hpick
  have hinj2 : Function.Injective (fun φ : T => f (pick φ)) := by
    intro a b hab
    have h1 : pick a = pick b := hf hab
    apply Subtype.ext
    rw [← hpick a, ← hpick b, h1]
  calc T.card = Nat.card T := (Nat.card_eq_finsetCard T).symm
    _ ≤ Nat.card (ZK.EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) := Nat.card_le_card_of_injective _ hinj2
    _ ≤ B := hcard

end

end PositivityTheory.QuaternionShaBounds.ShaAssumptions

theorem PositivityTheory.QuaternionShaBounds.ShaAsm_holds : PositivityTheory.QuaternionShaBounds.ShaAsm := by
  intro hLay hCl L _ _ _ l c E B _ hTop hE hB
  let Ω := AlgebraicClosure L
  obtain ⟨D⟩ := ldata_nonempty (F := L) (Ω := Ω) l
  have he : (E : ℤ) ≠ 0 := by exact_mod_cast (show E ≠ 0 by omega)
  have hinj := Kum.resInfInj L Ω l D (E : ℤ) he (PositivityTheory.QuaternionShaBounds.ShaAssumptions.procyc_of_top L Ω l c hTop)
  have hW : (Formalism.GaloisCohomology.Sha D (E : ℤ)).map (Kum.resInf D (E : ℤ)) ≤
      Kum.EqHom l (Kum.Uinf L Ω l) (qzG L Ω l (E : ℤ)) :=
    Kum.resInfMem L Ω l D (E : ℤ)
  have key : ∀ T : Finset (Kum.Uinf L Ω l → QZ l),
      (↑T : Set (Kum.Uinf L Ω l → QZ l)) ⊆ ((Formalism.GaloisCohomology.Sha D (E : ℤ)).map (Kum.resInf D (E : ℤ)) : Set _) →
      T.card ≤ B := by
    intro T hT
    have ha : ∀ φ : T, ∃ n, ∀ ν, n ≤ ν → PositivityTheory.QuaternionShaBounds.ShaAssumptions.Good (L := L) (Ω := Ω) E ν φ.1 :=
      fun φ => PositivityTheory.QuaternionShaBounds.ShaAssumptions.good_of E φ.1 (hW (hT φ.2))
    choose N hN using ha
    exact PositivityTheory.QuaternionShaBounds.ShaAssumptions.card_le hLay hCl c E B hTop hB (max (max c 2) (Finset.univ.sup N))
      (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) T
      fun φ hφ => hN ⟨φ, hφ⟩ _ (le_max_of_le_right (Finset.le_sup (Finset.mem_univ _)))
  set W := (Formalism.GaloisCohomology.Sha D (E : ℤ)).map (Kum.resInf D (E : ℤ)) with hWdef
  have hfin : (W : Set (Kum.Uinf L Ω l → QZ l)).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
    have := key T hT
    omega
  have : Finite W := hfin.to_subtype
  obtain ⟨k, hk, hcard⟩ := Kum.lenOfCard l W
  refine ⟨k, ?_, ?_⟩
  · rw [← shaLen_eq_shaInv D, Formalism.GaloisCohomology.shaLen, ← hk]
    exact (Submodule.equivMapOfInjective _ hinj _).length_eq
  · rw [← hcard]
    have h1 := key hfin.toFinset (by simp)
    rwa [← Set.ncard_eq_toFinset_card _ hfin, ← Nat.card_coe_set_eq] at h1

end

theorem PositivityTheory.QuaternionShaBounds.sSha : UpperTheory.V.ZK.SSha := PositivityTheory.QuaternionShaBounds.ShaAsm_holds PositivityTheory.QuaternionShaBounds.LayEx_holds PositivityTheory.QuaternionShaBounds.ClInj_holds
