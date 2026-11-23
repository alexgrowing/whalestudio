import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualityClausesOfMulEquiv
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

noncomputable section

namespace GlobalTheory.LocalDualityAll

def cycP (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [Fact l.Prime] (r : ℕ) :
    GK p K →* (ZMod (l ^ r))ˣ :=
  (Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp
    ((cyclotomicCharacter (PadicAlgCl p) l).comp
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p)))

theorem localCyclotomicCharacter_spec (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) (σ : GK p K) (ζ : PadicAlgCl p) (hζ : ζ ^ (l ^ r) = 1) :
    σ ζ = ζ ^ ((cycP p K l r σ : ZMod (l ^ r)).val) := by
  have : NeZero ((l : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ (PadicAlgCl p) σ) ζ hζ

theorem exists_mulEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K) (e : Dec (F := F) A ≃* GK p K),
      Continuous e ∧ Continuous e.symm ∧
        ∀ (r : ℕ) (g : Dec (F := F) A), cycP p K l r (e g) = cycMod F Ω l r (g : G F Ω) := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F Ω v A hv hA
  let K : Formalism.BasicNotions.Loc.FinExt p :=
    ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x)),
      GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω))⟩
  have hK := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := F) hj K rfl
  obtain ⟨hf, hf'⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[p] (PadicAlgCl p) K.1
  refine ⟨K.1, hK, e.trans (IntermediateField.fixingSubgroupEquiv K.1), hf.comp he, he'.comp hf',
    fun r g => Units.ext ?_⟩
  have hl : l.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := j.charZero
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  have hζ' := hζ.map_of_injective j.injective
  have ha : (g : Ω ≃ₐ[F] Ω) ζ = ζ ^ ((cycMod F Ω l r (g : G F Ω) : ZMod (l ^ r))).val :=
    cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[F] Ω) Ω (g : Ω ≃ₐ[F] Ω)) ζ
      hζ.pow_eq_one
  set σ : GK p K.1 := (e.trans (IntermediateField.fixingSubgroupEquiv K.1)) g with hσ
  have hb : σ (j ζ) = j ζ ^ ((cycP p K.1 l r σ : ZMod (l ^ r))).val :=
    localCyclotomicCharacter_spec p K.1 l r σ _ hζ'.pow_eq_one
  have hc : σ (j ζ) = j ((g : Ω ≃ₐ[F] Ω) ζ) := hec g ζ
  rw [hc, ha, map_pow] at hb
  exact (ZMod.val_injective _ (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hb)).symm

theorem exists_mu (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (l : ℕ) [hl : Fact l.Prime]
    (r : ℕ) : ∃ e : ZMod (l ^ r) ≃+ (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).V,
      ∀ (g : GK p K) (m : ZMod (l ^ r)), e ((cycP p K l r g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g (e m) := by
  have : IsSepClosure ↥K (PadicAlgCl p) :=
    ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[p] K _⟩
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hl.out.ne_zero)
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  refine ⟨e.symm, fun g m => ?_⟩
  have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
      (galRootsOfUnity.{0} ↥K (PadicAlgCl p) (l ^ r)).ρ g x =
        (cycP p K l r g : ZMod (l ^ r)).val • x := by
    intro x
    rw [galRootsOfUnity_ρ_apply]
    apply Additive.toMul.injective
    rw [toMul_ofMul, toMul_nsmul]
    apply Subtype.ext
    apply Units.ext
    rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
    refine localCyclotomicCharacter_spec p K l r g _ ?_
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
  refine Eq.trans ?_ (key _).symm
  refine Eq.trans ?_ (map_nsmul e.symm _ m)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem tate_p (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K)
    (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (GK p K) M) (hrho : ContAction rho) :
    Nonempty (H2 (charRep (cycP p K l r)) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) ∧
    Function.Bijective (cupH0H2TwistedDual (cycP p K l r) rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual (cycP p K l r) rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 (cycP p K l r) rho (MonoidHom.id _)) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨eD, hD⟩ := exists_mu p K l r
  exact CompanionTheory.LocalTateOrthogonality.Gcoh.tate_core CompanionTheory.LocalTateOrthogonality.Gcoh.gcRep CompanionTheory.LocalTateOrthogonality.Gcoh.gc0 CompanionTheory.LocalTateOrthogonality.Gcoh.gc1 CompanionTheory.LocalTateOrthogonality.Gcoh.gc2
    (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)) (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    (cycP p K l r) eD hD M rho hrho

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', hcyc⟩ := exists_mulEquiv F Ω p l v A hpv hA
  have hc' : ContAction (rho.comp e.symm.toMonoidHom) := hc.comp' he'
  have hχ : ((cycMod F Ω l r).comp (Dec (F := F) A).subtype).comp e.symm.toMonoidHom = cycP p K l r := by
    ext1 σ
    have := hcyc r (e.symm σ)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine GlobalTheory.CohTransport.dualityClauses_of_mulEquiv (ZMod (l ^ r)) _ _ M e.symm he' he _ rho hc hc' ?_
  rw [hχ]
  exact tate_p p K hK l r M _ hc'

end GlobalTheory.LocalDualityAll
