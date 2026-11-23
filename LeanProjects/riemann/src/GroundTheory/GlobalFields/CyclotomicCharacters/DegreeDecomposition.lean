import Mathlib
import GroundTheory.GlobalFields.CyclotomicCharacters.Degree
import GroundTheory.GlobalFields.CyclotomicCharacters.ClosedSubgroups

open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise

namespace GroundTheory.Global

namespace Cyclotomic

open GroundTheory.LocalField.Abstract

local notation "ℚ̄" => AlgebraicClosure ℚ

section Lift

theorem isOpen_stabilizer_ringOfIntegers (b : 𝓞 ℚ̄) :
    IsOpen (MulAction.stabilizer Gal(ℚ̄/ℚ) b : Set Gal(ℚ̄/ℚ)) := by
  have : FiniteDimensional ℚ ℚ⟮(b : ℚ̄)⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  refine Subgroup.isOpen_mono (H₁ := (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup) (fun σ hσ => ?_)
    (ℚ⟮(b : ℚ̄)⟯).fixingSubgroup_isOpen
  rw [MulAction.mem_stabilizer_iff]
  exact RingOfIntegers.ext ((mem_fixingSubgroup_iff _ σ).mp hσ (b : ℚ̄) (mem_adjoin_simple_self ℚ _))

noncomputable abbrev ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) : 𝓞 L →+* 𝓞 ℚ̄ :=
  RingOfIntegers.mapRingHom (algebraMap L ℚ̄)

theorem coe_ringOfIntegersIncl (L : IntermediateField ℚ ℚ̄) (a : 𝓞 L) :
    ((ringOfIntegersIncl L a : 𝓞 ℚ̄) : ℚ̄) = ((a : L) : ℚ̄) :=
  rfl

theorem exists_mem_stabilizer_of_comap_eq (L : IntermediateField ℚ ℚ̄) (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] (τ : Gal(ℚ̄/ℚ))
    (h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L)) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, ∀ x ∈ L, σ x = τ x := by
  let G := L.fixingSubgroup
  let _ : Algebra (𝓞 L) (𝓞 ℚ̄) := (ringOfIntegersIncl L).toAlgebra
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : CompactSpace G :=
    isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hfix : ∀ (g : G) (a : 𝓞 L), g • ringOfIntegersIncl L a = ringOfIntegersIncl L a :=
    fun g a => RingOfIntegers.ext ((mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  have : SMulCommClass G (𝓞 L) (𝓞 ℚ̄) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', RingHom.algebraMap_toAlgebra, hfix]⟩
  have : ContinuousSMul G (𝓞 ℚ̄) := continuousSMul_iff_stabilizer_isOpen.2 fun b =>
    (isOpen_stabilizer_ringOfIntegers b).preimage continuous_subtype_val
  have : Algebra.IsInvariant (𝓞 L) (𝓞 ℚ̄) G := ⟨fun b hb => by
    have hmem : (b : ℚ̄) ∈ fixedField L.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro f hf
      exact congrArg (fun c : 𝓞 ℚ̄ => (c : ℚ̄)) (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L ℚ̄) (algebraMap L ℚ̄).injective).1
        b.isIntegral_coe
    exact ⟨⟨⟨b, hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := 𝓞 L) (G := G) P (τ⁻¹ • P) h.symm
  refine ⟨τ * g, ?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    calc τ • ((g : Gal(ℚ̄/ℚ)) • P) = τ • (g • P) := rfl
      _ = τ • (τ⁻¹ • P) := by rw [hg]; rfl
      _ = P := smul_inv_smul τ P
  · change τ ((g : Gal(ℚ̄/ℚ)) x) = τ x
    rw [(mem_fixingSubgroup_iff _ _).1 g.2 x hx]

end Lift

section Cyclotomic

theorem modCharacter_eq_of_eqOn {M : ℕ} [NeZero M] {σ τ : Gal(ℚ̄/ℚ)}
    (h : ∀ x ∈ rootsOfUnityField M, σ x = τ x) : modCharacter M σ = modCharacter M τ :=
  Units.ext (modCharacter_unique σ fun t ht => by
    rw [h t (subset_adjoin ℚ _ ht), modCharacter_spec τ ht])

theorem redUnits_character (q : Nat.Primes) (k : ℕ) (σ : Gal(ℚ̄/ℚ)) :
    (redUnits q k (Units.map (toPadicInt q).toMonoidHom (character σ)) : ZMod ((q : ℕ) ^ k)) =
      (modCharacter ((q : ℕ) ^ k) σ : ZMod ((q : ℕ) ^ k)) := by
  rw [coe_redUnits, Units.coe_map]
  change PadicInt.toZModPow k (toPadicInt q (character σ : ℤ̂)) = _
  rw [toZModPow_toPadicInt]
  exact proj_character (primePowPNat q k) σ

theorem exists_mem_stabilizer_modCharacter_eq_prime {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 ℚ̄))
    [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] {M : ℕ} [NeZero M] (hM : ¬ p ∣ M) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, (modCharacter M σ : ZMod M) = p := by
  set L := rootsOfUnityField M
  let Q : Ideal (𝓞 L) := P.comap (ringOfIntegersIncl L)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    rw [Ideal.under, Ideal.comap_comap, show (ringOfIntegersIncl L).comp (algebraMap ℤ (𝓞 L)) =
      algebraMap ℤ (𝓞 ℚ̄) from RingHom.ext_int _ _]
    exact hP.over⟩
  obtain ⟨τ₀, hτ₀, -⟩ := existsUnique_isArithFrobAt p L Q hM
  let τ : Gal(ℚ̄/ℚ) := τ₀.liftNormal ℚ̄
  have hτ : ∀ x : L, τ (x : ℚ̄) = (τ₀ x : ℚ̄) := fun x => τ₀.liftNormal_commutes ℚ̄ x
  have hstab := hτ₀.mem_stabilizer
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    have h1 : τ • ringOfIntegersIncl L x = ringOfIntegersIncl L (τ₀ • x) :=
      RingOfIntegers.ext (hτ x)
    rw [h1, ← Ideal.mem_comap]
    change τ₀ • x ∈ Q ↔ x ∈ Q
    conv_lhs => rw [← MulAction.mem_stabilizer_iff.1 hstab]
    exact Ideal.smul_mem_pointwise_smul_iff
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  refine ⟨σ, hσ, ?_⟩
  have hres : σ.restrictNormal L = τ₀ := by
    ext x
    rw [← hτ x, ← hστ _ x.2]
    exact σ.restrictNormal_commutes L x
  rw [← isArithFrobAt_restrictNormal_iff M p Q hM σ, hres]
  exact hτ₀

theorem eq_of_natCast_mem_rootsOfUnityField {p : ℕ} [hp : Fact p.Prime] (k : ℕ)
    {Q₁ Q₂ : Ideal (𝓞 (rootsOfUnityField (p ^ (k + 1))))} [Q₁.IsPrime] [Q₂.IsPrime]
    (h₁ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₁)
    (h₂ : (p : 𝓞 (rootsOfUnityField (p ^ (k + 1)))) ∈ Q₂) : Q₁ = Q₂ := by
  let L := rootsOfUnityField (p ^ (k + 1))
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ (p ^ (k + 1))
  let ζL : L := ⟨ζ, subset_adjoin ℚ _ hζ.pow_eq_one⟩
  have hζL : IsPrimitiveRoot ζL (p ^ (k + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap L ℚ̄) hζ (algebraMap L ℚ̄).injective
  have hprime : Prime (hζL.toInteger - 1) := hζL.zeta_sub_one_prime
  have hmax : (Ideal.span {hζL.toInteger - 1}).IsMaximal :=
    ((Ideal.span_singleton_prime hprime.ne_zero).2 hprime).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hprime.ne_zero)
  have key : ∀ Q : Ideal (𝓞 L), Q.IsPrime → (p : 𝓞 L) ∈ Q →
      Q = Ideal.span {hζL.toInteger - 1} := by
    intro Q hQ hpQ
    refine (hmax.eq_of_le hQ.ne_top ?_).symm
    rw [Ideal.span_singleton_le_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
    have : CharP (𝓞 L ⧸ Q) p := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem]
      exact hpQ)
    have h1 : (Ideal.Quotient.mk Q (hζL.toInteger - 1)) ^ (p ^ (k + 1)) = 0 := by
      rw [map_sub, map_one, sub_pow_char_pow, ← map_pow,
        (hζL.toInteger_isPrimitiveRoot).pow_eq_one, map_one, one_pow, sub_self]
    exact (pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)).1 h1
  rw [key Q₁ ‹_› h₁, key Q₂ ‹_› h₂]

theorem exists_mem_stabilizer_modCharacter_eq_of_prime_pow {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [hP : P.LiesOver (Ideal.span {(p : ℤ)})] (k : ℕ)
    (a : (ZMod (p ^ (k + 1)))ˣ) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, modCharacter (p ^ (k + 1)) σ = a := by
  obtain ⟨τ, hτ⟩ := exists_modCharacter_eq (p ^ (k + 1)) a
  set L := rootsOfUnityField (p ^ (k + 1))
  have hpP : ((p : ℕ) : 𝓞 ℚ̄) ∈ P := by
    have h : (p : ℤ) ∈ P.under ℤ := by
      rw [← hP.over]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h
    exact h
  have hpP' : ((p : ℕ) : 𝓞 ℚ̄) ∈ τ⁻¹ • P := by
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    change MulSemiringAction.toRingHom _ _ τ (p : 𝓞 ℚ̄) ∈ P
    rw [map_natCast]
    exact hpP
  have h : (τ⁻¹ • P).comap (ringOfIntegersIncl L) = P.comap (ringOfIntegersIncl L) :=
    eq_of_natCast_mem_rootsOfUnityField k (by rw [Ideal.mem_comap, map_natCast]; exact hpP')
      (by rw [Ideal.mem_comap, map_natCast]; exact hpP)
  obtain ⟨σ, hσ, hστ⟩ := exists_mem_stabilizer_of_comap_eq L P τ h
  exact ⟨σ, hσ, (modCharacter_eq_of_eqOn hστ).trans hτ⟩

end Cyclotomic

section Component

theorem exists_degreeComponent_ne_one (q : Nat.Primes) (w : ℤ_[q]ˣ)
    (hw : padicUnitsLog q w ≠ 1) :
    ∃ N, 0 < N ∧ ∀ σ : Gal(ℚ̄/ℚ), (modCharacter ((q : ℕ) ^ N) σ : ZMod ((q : ℕ) ^ N)) =
      PadicInt.toZModPow N (w : ℤ_[q]) → degreeComponent q σ ≠ 1 := by
  obtain ⟨n, hn⟩ : ∃ n, PadicInt.toZModPow n (Multiplicative.toAdd (padicUnitsLog q w)) ≠ 0 := by
    by_contra! hcon
    apply hw
    have h0 : Multiplicative.toAdd (padicUnitsLog q w) = 0 :=
      PadicInt.ext_of_toZModPow.mp fun n => by rw [hcon n, map_zero]
    rw [← ofAdd_toAdd (padicUnitsLog q w), h0, ofAdd_zero]
  refine ⟨n + unitsLevel q, by have := unitsLevel_ne_zero q; omega, fun σ hσ h1 => hn ?_⟩
  have hred : redUnits q (n + unitsLevel q) (Units.map (toPadicInt q).toMonoidHom (character σ)) =
      redUnits q (n + unitsLevel q) w :=
    Units.ext (by rw [redUnits_character, hσ, coe_redUnits])
  rw [toZModPow_padicUnitsLog, ← hred, ← toZModPow_padicUnitsLog, ← degreeComponent_apply, h1,
    toAdd_one, map_zero]

theorem genLog_ne_zero (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : genLog ℓ ≠ 0 := by
  intro h
  have := coprime_genLog ℓ
  rw [h, Nat.coprime_zero_right] at this
  exact hℓ.out.one_lt.ne' this

theorem exists_mem_stabilizer_degreeComponent_ne_one {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (q : Nat.Primes) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, degreeComponent q σ ≠ 1 := by
  have : NeZero (q : ℕ) := ⟨q.2.ne_zero⟩
  by_cases hpq : p = q
  · have hw : padicUnitsLog q (genPadicUnit q) ≠ 1 := by
      intro h
      have := padicUnitsLog_genPadicUnit (q : ℕ)
      rw [h, toAdd_one] at this
      exact genLog_ne_zero q (Nat.cast_eq_zero.1 this.symm)
    obtain ⟨N, hN, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    subst hpq
    obtain ⟨σ, hσP, hσa⟩ := exists_mem_stabilizer_modCharacter_eq_of_prime_pow P k
      (redUnits q (k + 1) (genPadicUnit q))
    exact ⟨σ, hσP, hσ σ (by rw [hσa, coe_redUnits])⟩
  · have hcop : Nat.Coprime q p := (Nat.coprime_primes q.2 hp.out).2 (Ne.symm hpq)
    have hw : padicUnitsLog q (isUnit_natCast_of_coprime (q : ℕ) hcop).unit ≠ 1 := by
      intro h
      rw [padicUnitsLog_eq_one_iff] at h
      have h2 := congrArg (fun u : ℤ_[q]ˣ => (u : ℤ_[q])) h
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
      rw [← Nat.cast_pow, ← Nat.cast_one, Nat.cast_inj, Nat.pow_eq_one] at h2
      rcases h2 with h2 | h2
      · exact hp.out.one_lt.ne' h2
      · exact (torsionExponent_pos q).ne' h2
    obtain ⟨N, -, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    have hM : ¬ p ∣ (q : ℕ) ^ N := fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp.out q.2).1 (hp.out.dvd_of_dvd_pow h))
    obtain ⟨σ, hσP, hσp⟩ := exists_mem_stabilizer_modCharacter_eq_prime P hM
    exact ⟨σ, hσP, hσ σ (by rw [hσp, IsUnit.unit_spec, map_natCast])⟩

end Component

section Image

theorem isClosed_stabilizer (P : Ideal (𝓞 ℚ̄)) :
    IsClosed (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) := by
  let _ : TopologicalSpace (𝓞 ℚ̄) := ⊥
  have : DiscreteTopology (𝓞 ℚ̄) := ⟨rfl⟩
  have : ContinuousSMul Gal(ℚ̄/ℚ) (𝓞 ℚ̄) :=
    continuousSMul_iff_stabilizer_isOpen.2 isOpen_stabilizer_ringOfIntegers
  have hset : (MulAction.stabilizer Gal(ℚ̄/ℚ) P : Set Gal(ℚ̄/ℚ)) =
      (⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ • x) ⁻¹' (P : Set (𝓞 ℚ̄))) ∩
        ⋂ x ∈ P, (fun σ : Gal(ℚ̄/ℚ) => σ⁻¹ • x) ⁻¹' (P : Set (𝓞 ℚ̄)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_preimage]
    constructor
    · intro h
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [← h]
        exact Ideal.smul_mem_pointwise_smul_iff.2 hx
      · rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, h]
        exact hx
    · rintro ⟨h1, h2⟩
      apply le_antisymm
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
        have := h1 _ hy
        rwa [smul_inv_smul] at this
      · intro y hy
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
        exact h2 y hy
  rw [hset]
  refine (isClosed_biInter fun x _ => ?_).inter (isClosed_biInter fun x _ => ?_)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_id.smul continuous_const)
  · exact (isClosed_discrete (P : Set (𝓞 ℚ̄))).preimage (continuous_inv.smul continuous_const)

variable (q : Nat.Primes) (P : Ideal (𝓞 ℚ̄))

def decompositionComponentImage : AddSubgroup ℤ_[q] where
  carrier := (fun σ => Multiplicative.toAdd (degreeComponent q σ)) ''
    (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩

theorem coe_decompositionComponentImage :
    (decompositionComponentImage q P : Set ℤ_[q]) =
      (fun σ => Multiplicative.toAdd (degreeComponent q σ)) ''
        (MulAction.stabilizer Gal(ℚ̄/ℚ) P) :=
  rfl

theorem isClosed_decompositionComponentImage :
    IsClosed (decompositionComponentImage q P : Set ℤ_[q]) :=
  ((isClosed_stabilizer P).isCompact.image
    (continuous_toAdd.comp (continuous_degreeComponent q))).isClosed

def decompositionDegreeImage : AddSubgroup ℤ̂ where
  carrier := (fun σ => Multiplicative.toAdd (degree σ)) '' (MulAction.stabilizer Gal(ℚ̄/ℚ) P)
  add_mem' := by
    rintro _ _ ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, by simp⟩
  zero_mem' := ⟨1, one_mem _, by simp⟩
  neg_mem' := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ⁻¹, inv_mem hσ, by simp⟩

theorem coe_decompositionDegreeImage :
    (decompositionDegreeImage P : Set ℤ̂) =
      (fun σ => Multiplicative.toAdd (degree σ)) '' (MulAction.stabilizer Gal(ℚ̄/ℚ) P) :=
  rfl

theorem isClosed_decompositionDegreeImage :
    IsClosed (decompositionDegreeImage P : Set ℤ̂) :=
  ((isClosed_stabilizer P).isCompact.image (continuous_toAdd.comp continuous_degree)).isClosed

theorem topologicalClosure_decompositionDegreeImage :
    (decompositionDegreeImage P).topologicalClosure = decompositionDegreeImage P :=
  SetLike.coe_injective (by
    rw [AddSubgroup.topologicalClosure_coe, (isClosed_decompositionDegreeImage P).closure_eq])

theorem exists_mem_decompositionComponentImage_ne_zero (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ x ∈ decompositionComponentImage q P, x ≠ 0 := by
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, fun h => hne ?_⟩
  have h' : Multiplicative.toAdd (degreeComponent q σ) = 0 := h
  rw [← ofAdd_toAdd (degreeComponent q σ), h', ofAdd_zero]

theorem isOpen_decompositionComponentImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    IsOpen (decompositionComponentImage q P : Set ℤ_[q]) := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact isOpen_of_isClosed_of_ne_zero _ (isClosed_decompositionComponentImage q P) hx hx0

theorem infinite_decompositionComponentImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (decompositionComponentImage q P : Set ℤ_[q]).Infinite := by
  obtain ⟨x, hx, hx0⟩ := exists_mem_decompositionComponentImage_ne_zero q P p
  exact infinite_of_ne_zero _ hx hx0

theorem nonempty_addEquiv_decompositionDegreeImage (p : ℕ) [Fact p.Prime] [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nonempty ((decompositionDegreeImage P).topologicalClosure ≃+ ℤ̂) := by
  rw [topologicalClosure_decompositionDegreeImage]
  refine nonempty_addEquiv_of_isClosed _ (isClosed_decompositionDegreeImage P) fun q => ?_
  obtain ⟨σ, hσ, hne⟩ := exists_mem_stabilizer_degreeComponent_ne_one (p := p) P q
  refine ⟨_, ⟨σ, hσ, rfl⟩, ?_⟩
  rw [toPadicInt_degree]
  exact fun h => hne (by rw [← ofAdd_toAdd (degreeComponent q σ), h, ofAdd_zero])

end Image

end Cyclotomic

end GroundTheory.Global
