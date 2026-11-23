import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValuationSubringIntegralClosureCompleteDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfLevel
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CMVal GlobalTheory.HeckeGal IsLocalRing

namespace GlobalTheory.ToricRational

section Inertia

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]

def intBar : ValuationSubring (AlgebraicClosure (FractionRing O)) :=
  ⟨(integralClosure O _).toSubring, fun x => GlobalTheory.LN.isIntegral_or_isIntegral_inv O _ x⟩

variable {O}

theorem mem_intBar {x : AlgebraicClosure (FractionRing O)} : x ∈ intBar O ↔ IsIntegral O x := Iff.rfl

private theorem valuation_lt_one_iff_mem_and_inv_not_mem {L : Type} [Field L] (B : ValuationSubring L) (z : L) :
    B.valuation z < 1 ↔ z ∈ B ∧ (z = 0 ∨ z⁻¹ ∉ B) := by
  constructor
  · intro h
    have hz : z ∈ B := (B.valuation_le_one_iff z).1 h.le
    refine ⟨hz, ?_⟩
    by_cases h0 : z = 0
    · exact Or.inl h0
    right
    intro hi
    have h3 := (B.valuation_le_one_iff _).2 hi
    rw [map_inv₀] at h3
    have hne : B.valuation z ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h4 : 1 ≤ B.valuation z := by
      by_contra h5
      push_neg at h5
      have h6 := one_lt_inv₀ (zero_lt_iff.2 hne) |>.2 h5
      exact absurd h3 (not_le.2 h6)
    exact absurd h (not_lt.2 h4)
  · rintro ⟨hz, h0 | hi⟩
    · simp [h0]
    · have hv := (B.valuation_le_one_iff z).2 hz
      rcases lt_or_eq_of_le hv with h | h
      · exact h
      · exfalso
        apply hi
        rw [← B.valuation_le_one_iff, map_inv₀, h, inv_one]

theorem val_lt_one {a : O} (ha : a ∈ maximalIdeal O) :
    (intBar O).valuation (algebraMap O (AlgebraicClosure (FractionRing O)) a) < 1 := by
  rw [valuation_lt_one_iff_mem_and_inv_not_mem]
  refine ⟨mem_intBar.2 isIntegral_algebraMap, ?_⟩
  by_cases h0 : a = 0
  · left; simp [h0]
  right
  intro hi
  rw [mem_intBar, IsScalarTower.algebraMap_apply O (FractionRing O) (AlgebraicClosure (FractionRing O)),
    ← map_inv₀] at hi
  have hi' : IsIntegral O (algebraMap O (FractionRing O) a)⁻¹ :=
    IsIntegral.tower_bot (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).injective hi
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi'
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, hb, map_one, mul_inv_cancel₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 h0
  exact ((IsLocalRing.mem_maximalIdeal a).1 ha) (isUnit_iff_exists_inv.2 ⟨b, hab⟩)

theorem exists_sub_lt_one (hk : IsAlgClosed (ResidueField O)) {x : AlgebraicClosure (FractionRing O)} (hx : x ∈ intBar O) :
    ∃ a : O, (intBar O).valuation (x - algebraMap O _ a) < 1 := by
  classical
  obtain ⟨p, hpm, hp⟩ := mem_intBar.1 hx
  set π := IsLocalRing.residue O
  have hcard : (p.map π).roots.card = (p.map π).natDegree := IsAlgClosed.card_roots_eq_natDegree
  set lift := Function.surjInv (IsLocalRing.residue_surjective (R := O))
  set Q : Polynomial O := (((p.map π).roots.map lift).map (fun a => Polynomial.X - Polynomial.C a)).prod
  have hQ : Q.map π = p.map π := by
    simp only [Q, Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, lift, π, Function.surjInv_eq IsLocalRing.residue_surjective]
    exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hpm.map _) hcard
  have hcoef : ∀ i, (p - Q).coeff i ∈ IsLocalRing.maximalIdeal O := by
    intro i
    rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.coeff_map, Polynomial.map_sub, hQ, sub_self,
      Polynomial.coeff_zero]
  have hx1 : (intBar O).valuation x ≤ 1 := ((intBar O).valuation_le_one_iff x).2 hx
  have hval : (intBar O).valuation (Polynomial.aeval x (p - Q)) < 1 := by
    rw [Polynomial.aeval_eq_sum_range]
    apply Valuation.map_sum_lt _ one_ne_zero
    intro i _
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hx1 i)) (val_lt_one (hcoef i))
  have hpx : Polynomial.aeval x p = 0 := by rw [Polynomial.aeval_def]; exact hp
  rw [map_sub, hpx, zero_sub, Valuation.map_neg] at hval
  simp only [Q, map_multiset_prod, Multiset.map_map, Function.comp_def, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at hval
  by_contra hne
  push_neg at hne
  refine absurd hval (not_lt.2 ?_)
  apply Multiset.one_le_prod_of_one_le
  intro t ht
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 ht
  exact hne _

theorem apply_mem_intBar (τ : AlgebraicClosure (FractionRing O) ≃ₐ[FractionRing O] AlgebraicClosure (FractionRing O))
    (x : AlgebraicClosure (FractionRing O)) : τ x ∈ intBar O ↔ x ∈ intBar O := by
  rw [mem_intBar, mem_intBar]
  constructor
  · intro h
    have h2 := h.map (τ.symm.toAlgHom.restrictScalars O)
    simpa using h2
  · intro h
    exact h.map (τ.toAlgHom.restrictScalars O)

theorem val_apply_sub_lt_one (hk : IsAlgClosed (ResidueField O))
    (τ : AlgebraicClosure (FractionRing O) ≃ₐ[FractionRing O] AlgebraicClosure (FractionRing O))
    {x : AlgebraicClosure (FractionRing O)} (hx : x ∈ intBar O) : (intBar O).valuation (τ x - x) < 1 := by
  obtain ⟨a, ha⟩ := exists_sub_lt_one hk hx
  set y := x - algebraMap O (AlgebraicClosure (FractionRing O)) a with hy
  have hτa : τ (algebraMap O (AlgebraicClosure (FractionRing O)) a) = algebraMap O (AlgebraicClosure (FractionRing O)) a := by
    rw [IsScalarTower.algebraMap_apply O (FractionRing O) (AlgebraicClosure (FractionRing O)), τ.commutes]
  have e : τ x - x = τ y - y := by rw [hy, map_sub, hτa]; ring
  rw [e]
  have hτy : (intBar O).valuation (τ y) < 1 := by
    have ha' := ha
    rw [valuation_lt_one_iff_mem_and_inv_not_mem] at ha' ⊢
    obtain ⟨h1, h2⟩ := ha'
    refine ⟨(apply_mem_intBar τ y).2 h1, ?_⟩
    rcases h2 with h | h
    · left; simp [h]
    · right; rwa [← map_inv₀ τ y, apply_mem_intBar]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hτy ha)

private theorem comap_valuation_lt_one_iff' {K L : Type} [Field K] [Field L] (B : ValuationSubring L) (f : K →+* L)
    (z : K) : (B.comap f).valuation z < 1 ↔ B.valuation (f z) < 1 := by
  rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

theorem exists_inertia (hk : IsAlgClosed (ResidueField O)) {l : ℕ} (hl : l ≠ 0) (hO : (l : O) ∈ maximalIdeal O)
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (J : Ω →+* AlgebraicClosure (FractionRing O))
    (hJ : ∀ x : K, J (algebraMap K Ω x) ∈ (algebraMap (FractionRing O) (AlgebraicClosure (FractionRing O))).range) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), (l : 𝓞 K) ∈ v.asIdeal ∧ IsPlaceOver A v ∧
      ∀ τ : AlgebraicClosure (FractionRing O) ≃ₐ[FractionRing O] AlgebraicClosure (FractionRing O),
        ∃ g : G K Ω, g ∈ Ine (F := K) A ∧ ∀ x, J (g x) = τ (J x) := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  set A : ValuationSubring Ω := (intBar O).comap J with hA
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := by
    intro x
    rw [ValuationSubring.mem_comap, mem_intBar]
    obtain ⟨p, hpm, hp⟩ := NumberField.RingOfIntegers.isIntegral_coe x
    refine ⟨p.map (Int.castRingHom O), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap O (AlgebraicClosure (FractionRing O))).comp (Int.castRingHom O))
      ((J.comp (algebraMap K Ω)).comp (algebraMap ℤ K))]
    have h2 := Polynomial.hom_eval₂ p (algebraMap ℤ K) (J.comp (algebraMap K Ω)) (algebraMap (𝓞 K) K x)
    rw [hp, map_zero] at h2
    exact h2.symm
  set f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint with hf
  set P : Ideal (𝓞 K) := Ideal.comap f (IsLocalRing.maximalIdeal A) with hP
  have hPmem : ∀ x : 𝓞 K, x ∈ P ↔ A.valuation (algebraMap K Ω (x : K)) < 1 := by
    intro x
    rw [hP, Ideal.mem_comap]
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hlP : (l : 𝓞 K) ∈ P := by
    rw [hPmem, hA, comap_valuation_lt_one_iff']
    have e : J (algebraMap K Ω ((l : 𝓞 K) : K)) = algebraMap O (AlgebraicClosure (FractionRing O)) (l : O) := by
      simp only [map_natCast]
    rw [e]
    exact val_lt_one hO
  have hl0 : (l : 𝓞 K) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap (𝓞 K) K) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    exact hl h2
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h] at hlP
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  haveI : P.IsPrime := Ideal.comap_isPrime f _
  let v : HeightOneSpectrum (𝓞 K) := ⟨P, inferInstance, hP0⟩
  refine ⟨v, A, hlP, fun x => (hPmem x).symm, fun τ => ?_⟩
  have hfix : τ.toAlgHom.toRingHom.comp (J.comp (algebraMap K Ω)) = J.comp (algebraMap K Ω) := by
    ext c
    obtain ⟨w, hw⟩ := hJ c
    show τ (J (algebraMap K Ω c)) = J (algebraMap K Ω c)
    rw [← hw]
    exact τ.commutes w
  have hrange : ∀ x : Ω, ∃ y : Ω, J y = τ (J x) := by
    intro x
    set p := minpoly K x
    have hxi : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have hp0 : p ≠ 0 := minpoly.ne_zero hxi
    have key := Polynomial.hom_eval₂ p (J.comp (algebraMap K Ω)) τ.toAlgHom.toRingHom (J x)
    rw [hfix] at key
    have h0 : p.eval₂ (J.comp (algebraMap K Ω)) (J x) = 0 := by
      rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    rw [h0, map_zero] at key
    have hroot : ((p.map (algebraMap K Ω)).map J).IsRoot (τ (J x)) := by
      rw [Polynomial.IsRoot, Polynomial.map_map, Polynomial.eval_map]
      exact key.symm
    have hspl : (p.map (algebraMap K Ω)).Splits :=
      Polynomial.splits_iff_card_roots.2 IsAlgClosed.card_roots_eq_natDegree
    obtain ⟨y, hy⟩ := hspl.mem_range_of_isRoot (Polynomial.map_ne_zero hp0) hroot
    exact ⟨y, hy⟩
  choose σ hσ using hrange
  let gh : Ω →ₐ[K] Ω :=
    { toFun := σ
      map_one' := J.injective (by simp only [hσ, map_one])
      map_mul' := fun a b => J.injective (by simp only [hσ, map_mul])
      map_zero' := J.injective (by simp only [hσ, map_zero])
      map_add' := fun a b => J.injective (by simp only [hσ, map_add])
      commutes' := fun c => J.injective (by
        rw [hσ]
        obtain ⟨w, hw⟩ := hJ c
        rw [← hw]
        exact τ.commutes w) }
  have hbij : Function.Bijective gh := Algebra.IsAlgebraic.algHom_bijective gh
  let g : G K Ω := AlgEquiv.ofBijective gh hbij
  have hg : ∀ x, J (g x) = τ (J x) := fun x => hσ x
  refine ⟨g, ?_, hg⟩
  show g ∈ Formalism.ConjugateSelfDual.Inertia (F := K) A
  refine And.intro ?_ (fun x hx => ?_)
  · open Pointwise in
    rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
    ext z
    have e : J (g (g⁻¹ • z)) = J z := by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, ← apply_mem_intBar τ, ← hg, e]
  · have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
    rw [hA, comap_valuation_lt_one_iff', map_sub, hg]
    exact val_apply_sub_lt_one hk τ (ValuationSubring.mem_comap.1 hxA)

end Inertia

section Fourier

theorem eq_one_of_chars {Δ Ω : Type} [CommGroup Δ] [Finite Δ] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] {a : Δ}
    (h : ∀ r : Δ →* Ωˣ, r a = 1) : a = 1 := by
  haveI : NeZero ((Monoid.exponent Δ : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  by_contra ha
  obtain ⟨r, hr⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Δ Ω ha
  exact hr (h r)

theorem exists_fixed {Δ Ω C : Type} [CommGroup Δ] [Fintype Δ] [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field C] (j : Ω →+* C)
    (P : Δ → C) (ρ : (Δ →* Ωˣ) → Ω) (h : ∀ r, j (ρ r) = ∑ δ, j (r δ) * P δ) (δ : Δ) :
    ∃ z, j z = P δ ∧ ∀ g : Ω ≃+* Ω, (∀ r, g (ρ r) = ρ ((Units.map g.toMonoidHom).comp r)) → g z = z := by
  classical
  haveI : NeZero ((Monoid.exponent Δ : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  haveI : Fintype (Δ →* Ωˣ) := Fintype.ofFinite _
  set N : ℕ := Fintype.card (Δ →* Ωˣ) with hNdef
  have hN : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hNC : (N : C) ≠ 0 := by rw [← map_natCast j]; exact (map_ne_zero j).2 hN
  have orth : ∀ d : Δ, ∑ r : Δ →* Ωˣ, ((r d : Ωˣ) : Ω) = if d = 1 then (N : Ω) else 0 := by
    intro d
    split_ifs with hd
    · simp [hd, hNdef]
    · have hnot : ¬ ∀ r : Δ →* Ωˣ, r d = 1 := fun h' => hd (eq_one_of_chars (Ω := Ω) h')
      obtain ⟨r0, hr0⟩ := not_forall.1 hnot
      have hs : ∑ r : Δ →* Ωˣ, ((r0 d : Ωˣ) : Ω) * ((r d : Ωˣ) : Ω) = ∑ r : Δ →* Ωˣ, ((r d : Ωˣ) : Ω) :=
        Fintype.sum_equiv (Equiv.mulLeft r0) _ _ (fun r => by simp)
      rw [← Finset.mul_sum] at hs
      have h1 : ((r0 d : Ωˣ) : Ω) ≠ 1 := fun h' => hr0 (Units.ext h')
      have h2 : (1 - ((r0 d : Ωˣ) : Ω)) * ∑ r : Δ →* Ωˣ, ((r d : Ωˣ) : Ω) = 0 := by
        rw [sub_mul, one_mul, hs, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm h1))
  refine ⟨(N : Ω)⁻¹ * ∑ r : Δ →* Ωˣ, (((r δ)⁻¹ : Ωˣ) : Ω) * ρ r, ?_, ?_⟩
  · have key : ∀ r : Δ →* Ωˣ, j (((r δ)⁻¹ : Ωˣ) : Ω) * j (ρ r) =
        ∑ d, j (((r (δ⁻¹ * d)) : Ωˣ) : Ω) * P d := by
      intro r
      rw [h r, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [map_mul r, map_inv r, Units.val_mul, map_mul j, mul_assoc]
    simp only [map_mul, map_inv₀, map_natCast, map_sum]
    simp_rw [key]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, orth]
    rw [Finset.sum_eq_single δ]
    · simp [hNC]
    · intro d _ hd
      have : δ⁻¹ * d ≠ 1 := fun h' => hd (by rw [inv_mul_eq_one] at h'; exact h'.symm)
      simp [this]
    · intro hδ; exact absurd (Finset.mem_univ δ) hδ
  · intro g hg
    let e : (Δ →* Ωˣ) ≃ (Δ →* Ωˣ) :=
      { toFun := fun r => (Units.map g.toMonoidHom).comp r
        invFun := fun r => (Units.map g.symm.toMonoidHom).comp r
        left_inv := fun r => by ext d; simp
        right_inv := fun r => by ext d; simp }
    simp only [map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    refine Fintype.sum_equiv e _ _ (fun r => ?_)
    rw [hg r]
    simp [e]

end Fourier

section Values

variable {E : Type} [Field E] [NumberField E]

theorem modF_mem (M : Subfield ℂ) (y : (Af E)ˣ) : ((modF y : ℝ) : ℂ) ∈ M := by
  have hq : ((modF y : ℝ)) = ((∏ᶠ v : HeightOneSpectrum (𝓞 E),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))) : ℚ) : ℝ) := by
    rw [modF]
    have h := (Rat.castHom ℝ).toMonoidHom.map_finprod_of_injective Rat.cast_injective
      (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
    simpa using h.symm
  rw [hq, Complex.ofReal_ratCast]
  exact SubfieldClass.ratCast_mem M _

theorem finPart_mem {I : Type} [Fintype I] {φ : I → E →+* ℂ} {m : I → ℤ} {χ : HChar E} (hm : HasInf χ φ m) {c : Ideal (OF E)}
    (hc : c ≠ ⊥) [Finite (PicO c)] (hu : ∀ y ∈ hatOUnits c, finPart χ y = 1) (M : Subfield ℂ)
    (hE : ∀ (σ : E →+* ℂ) (x : E), σ x ∈ M) (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∉ S, (χ.val P : ℂ) ∈ M)
    (y : (Af E)ˣ) : (finPart χ y : ℂ) ∈ M := by
  classical
  let H : Subgroup ℂˣ :=
    { carrier := {z | (z : ℂ) ∈ M}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
        exact M.mul_mem ha hb
      one_mem' := by
        simp only [Set.mem_setOf_eq, Units.val_one]
        exact M.one_mem
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] at ha ⊢
        exact M.inv_mem ha }
  have hH : ∀ z : ℂˣ, z ∈ H ↔ (z : ℂ) ∈ M := fun z => Iff.rfl
  let ψ : (Af E)ˣ →* ℂˣ ⧸ H := (QuotientGroup.mk' H).comp (finPart χ)
  have hψ : ∀ z, ψ z = 1 ↔ (finPart χ z : ℂ) ∈ M := by
    intro z
    rw [← hH]
    exact QuotientGroup.eq_one_iff (finPart χ z)
  have hker : princ ⊔ hatOUnits c ≤ ψ.ker := by
    refine sup_le ?_ ?_
    · intro z hz
      have hz' : z ∈ (Units.map (algebraMap E (Af E)).toMonoidHom).range := hz
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hz'
      rw [MonoidHom.mem_ker, hψ]
      have h2 : finPart χ ((Units.map (algebraMap E (Af E)).toMonoidHom) k) = (χ.inf k)⁻¹ :=
        eq_inv_of_mul_eq_one_left (finPart_mul_inf χ k)
      rw [h2, Units.val_inv_eq_inv_val]
      apply M.inv_mem
      rw [(hasInfRatio_iff χ φ m).1 hm k]
      apply M.prod_mem
      intro i _
      apply M.zpow_mem
      exact M.div_mem (hE (φ i) (k : E)) (hE ((starRingEnd ℂ).comp (φ i)) (k : E))
    · intro z hz
      rw [MonoidHom.mem_ker, hψ, hu z hz, Units.val_one]
      exact M.one_mem
  let ψb : PicO c →* ℂˣ ⧸ H := QuotientGroup.lift _ ψ hker
  have hψb : ∀ z, ψb (QuotientGroup.mk z) = ψ z := fun z => QuotientGroup.lift_mk' _ hker z
  haveI : Finite ψb.range := Finite.of_surjective ψb.rangeRestrict ψb.rangeRestrict_surjective
  have hmem : ψ y ∈ ψb.range := ⟨QuotientGroup.mk y, hψb y⟩
  have key : ∀ r : ψb.range →* ℂˣ, r ⟨ψ y, hmem⟩ = 1 := by
    intro r
    have hrr : ∀ z, ψb.rangeRestrict (QuotientGroup.mk z) = ⟨ψ z, ⟨QuotientGroup.mk z, hψb z⟩⟩ :=
      fun z => Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, hψb])
    have h := GlobalTheory.ToricDistribution.pic_char_eq_finPart hc (r.comp ψb.rangeRestrict) 1 S ?_ y
    · have h1 : finPart (1 : HChar E) y = 1 := by simp [finPart]
      rw [h1, MonoidHom.comp_apply, hrr] at h
      exact h
    · intro P hP
      refine ⟨?_, ?_⟩
      · intro x _
        simp [Formalism.L2.Host.HChar.loc]
      · have hv : ψ (unifAt P) = 1 := by
          rw [hψ, finPart_unifAt]
          exact hS P hP
        have hr1 : ψb.rangeRestrict (QuotientGroup.mk (unifAt P)) = 1 := by
          rw [hrr]
          exact Subtype.ext hv
        rw [MonoidHom.comp_apply, hr1, map_one]
        simp [Formalism.L2.Host.HChar.val, Formalism.L2.Host.HChar.locK, Formalism.L2.Host.HChar.loc]
  have hone : (⟨ψ y, hmem⟩ : ψb.range) = 1 := eq_one_of_chars (Ω := ℂ) key
  exact (hψ y).1 (congrArg Subtype.val hone)

end Values

end GlobalTheory.ToricRational
