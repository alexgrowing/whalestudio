import Mathlib

open NumberField IsDedekindDomain IntermediateField
open scoped Pointwise

noncomputable section

namespace CompanionTheory.PlaceDict

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem int_mem (A : ValuationSubring Ω) (b : 𝓞 Ω) : (b : Ω) ∈ A := by
  have h : IsIntegral A (b : Ω) := b.isIntegral_coe.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

theorem int_le (A : ValuationSubring Ω) (b : 𝓞 Ω) : A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (int_mem A b)

def cen (A : ValuationSubring Ω) : Ideal (𝓞 Ω) where
  carrier := {b | A.valuation (b : Ω) < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show A.valuation ((a : Ω) + b) < 1
    exact A.valuation.map_add_lt ha hb
  smul_mem' := fun c b hb => by
    show A.valuation ((c : Ω) * b) < 1
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (int_le A c) zero_le hb

theorem mem_cen {A : ValuationSubring Ω} {b : 𝓞 Ω} : b ∈ cen A ↔ A.valuation (b : Ω) < 1 := Iff.rfl

instance cen_prime (A : ValuationSubring Ω) : (cen A).IsPrime where
  ne_top' := fun h => by
    have : (1 : 𝓞 Ω) ∈ cen A := h ▸ Submodule.mem_top
    simp [mem_cen] at this
  mem_or_mem' := fun {a b} h => by
    by_contra hn
    rw [not_or, mem_cen, mem_cen, not_lt, not_lt] at hn
    rw [mem_cen, show ((a * b : 𝓞 Ω) : Ω) = (a : Ω) * b from rfl, map_mul,
      le_antisymm (int_le A a) hn.1, le_antisymm (int_le A b) hn.2, one_mul] at h
    exact lt_irrefl _ h

theorem val_eq_one {A : ValuationSubring Ω} {s : 𝓞 Ω} (h : s ∉ cen A) : A.valuation (s : Ω) = 1 :=
  le_antisymm (int_le A s) (not_lt.1 h)

variable (E) in

theorem frac [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) {x : Ω} (hx : x ∈ A) :
    ∃ b s : 𝓞 Ω, s ∉ cen A ∧ x * s = b := by
  obtain ⟨F, hF, y, rfl⟩ : ∃ F : IntermediateField E Ω, FiniteDimensional E F ∧ ∃ y : F, algebraMap F Ω y = x :=
    ⟨E⟮x⟯, adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _), ⟨x, mem_adjoin_simple_self E x⟩, rfl⟩
  have : NumberField F := NumberField.of_module_finite E _
  let i : 𝓞 F →+* 𝓞 Ω := algebraMap _ _
  have hi : ∀ n : 𝓞 F, ((i n : 𝓞 Ω) : Ω) = algebraMap F Ω (algebraMap (𝓞 F) F n) := fun _ => rfl
  by_cases hP : (cen A).comap i = ⊥
  · obtain ⟨n, d, hd, e⟩ := IsFractionRing.div_surjective (A := 𝓞 F) y
    have hd0 := nonZeroDivisors.ne_zero hd
    refine ⟨i n, i d, fun h => hd0 ((Submodule.mem_bot _).1 (hP ▸ (Ideal.mem_comap.2 h))), ?_⟩
    have hd' : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd0
    rw [hi, hi, ← map_mul, ← e, div_mul_cancel₀ _ hd']
  · let v : HeightOneSpectrum (𝓞 F) := ⟨(cen A).comap i, inferInstance, hP⟩
    obtain ⟨n, d, h | h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := F) y
    · refine ⟨i n, i d, d.2, ?_⟩
      rw [hi, hi, ← map_mul, h]
    · have e : algebraMap F Ω y * (i n : 𝓞 Ω) = (i d : 𝓞 Ω) := by
        rw [hi, hi, ← map_mul, h]
      refine ⟨i d, i n, fun hn => ?_, e⟩
      have h1 : A.valuation ((i d : 𝓞 Ω) : Ω) = 1 := val_eq_one d.2
      rw [← e, map_mul] at h1
      exact absurd h1 (mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 hx) zero_le hn).ne

theorem coe_smul (g : Ω ≃ₐ[E] Ω) (b : 𝓞 Ω) : ((g • b : 𝓞 Ω) : Ω) = g b := rfl

theorem map_mem [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω)
    (hg : ∀ b : 𝓞 Ω, g • b ∈ cen A → b ∈ cen A) {x : Ω} (hx : x ∈ A) : g x ∈ A := by
  obtain ⟨b, s, hs, e⟩ := frac E A hx
  have h1 := val_eq_one fun h => hs (hg s h)
  have h2 := int_le A (g • b)
  rw [coe_smul, ← e, map_mul, map_mul, ← coe_smul g s, h1, mul_one] at h2
  exact (A.valuation_le_one_iff _).1 h2

theorem of_cong [Algebra.IsAlgebraic E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω) {q : ℕ} (hq : q ≠ 0)
    (hg : ∀ b : 𝓞 Ω, g • b - b ^ q ∈ cen A) :
    g ∈ A.decompositionSubgroup E ∧ ∀ x ∈ A, g x - x ^ q ∈ A.nonunits := by
  have hiff : ∀ b : 𝓞 Ω, g • b ∈ cen A ↔ b ∈ cen A := fun b => by
    rw [← (cen_prime A).pow_mem_iff_mem (r := b) q (Nat.pos_of_ne_zero hq)]
    exact ⟨fun h => by simpa using (cen A).sub_mem h (hg b), fun h => by simpa using (cen A).add_mem (hg b) h⟩
  refine ⟨?_, fun x hx => ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    refine ⟨fun h => ?_, fun h => map_mem A g⁻¹ (fun b hb => ?_) h⟩
    · simpa using map_mem A g (fun b => (hiff b).1) h
    · simpa using (hiff _).2 hb
  · obtain ⟨b, s, hs, e⟩ := frac E A hx
    have h1 := val_eq_one fun h => hs ((hiff s).1 h)
    have h2 := val_eq_one hs
    have key : (g x - x ^ q) * (((g • s : 𝓞 Ω) : Ω) * (s : Ω) ^ q) =
        (((g • b - b ^ q) * s ^ q - b ^ q * (g • s - s ^ q) : 𝓞 Ω) : Ω) := by
      have e1 : g x * g s = g b := by rw [← map_mul, e]
      show (g x - x ^ q) * (g s * (s : Ω) ^ q) = (g b - (b : Ω) ^ q) * (s : Ω) ^ q - (b : Ω) ^ q * (g s - (s : Ω) ^ q)
      rw [← e1, ← e]
      ring
    have h3 : ((g • b - b ^ q) * s ^ q - b ^ q * (g • s - s ^ q) : 𝓞 Ω) ∈ cen A :=
      (cen A).sub_mem ((cen A).mul_mem_right _ (hg b)) ((cen A).mul_mem_left _ (hg s))
    rw [mem_cen, ← key, map_mul, map_mul, map_pow, h1, h2, one_pow, one_mul, mul_one] at h3
    exact (A.mem_nonunits_iff).2 h3

theorem exists_cen (Q : Ideal (𝓞 Ω)) [hQ : Q.IsMaximal] : ∃ A : ValuationSubring Ω, cen A = Q := by
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring (A := (integralClosure ℤ Ω).toSubring) Q hQ.ne_top
  exact ⟨A, (hQ.eq_of_le (cen_prime A).ne_top fun b hb => (A.mem_nonunits_iff).1 (hA ⟨b, hb, rfl⟩)).symm⟩

theorem lift [IsGalois E Ω] (L : IntermediateField E Ω) [FiniteDimensional E L] [Normal E L] (Q : Ideal (𝓞 Ω))
    [hQ : Q.IsMaximal] (τ : L ≃ₐ[E] L) (θ : 𝓞 Ω ⧸ Q →+* 𝓞 Ω ⧸ Q)
    (hτ : ∀ x : 𝓞 L, Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • x)) =
      θ (Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) x))) :
    ∃ φ : Ω ≃ₐ[E] Ω, AlgEquiv.restrictNormalHom L φ = τ ∧
      ∀ b : 𝓞 Ω, Ideal.Quotient.mk Q (φ • b) = θ (Ideal.Quotient.mk Q b) := by
  let G := L.fixingSubgroup
  let _ : TopologicalSpace (𝓞 Ω) := ⊥
  have : DiscreteTopology (𝓞 Ω) := ⟨rfl⟩
  have : CompactSpace G := isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  have hfix : ∀ (g : G) (a : 𝓞 L), g • algebraMap (𝓞 L) (𝓞 Ω) a = algebraMap (𝓞 L) (𝓞 Ω) a :=
    fun g a => RingOfIntegers.ext ((mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  have : SMulCommClass G (𝓞 L) (𝓞 Ω) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have hopen : ∀ b : 𝓞 Ω, IsOpen (MulAction.stabilizer (Ω ≃ₐ[E] Ω) b : Set (Ω ≃ₐ[E] Ω)) := fun b => by
    have : FiniteDimensional E E⟮(b : Ω)⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    exact Subgroup.isOpen_mono (H₁ := (E⟮(b : Ω)⟯).fixingSubgroup) (fun σ hσ => RingOfIntegers.ext
      ((mem_fixingSubgroup_iff _ _).1 hσ _ (mem_adjoin_simple_self E _))) (E⟮(b : Ω)⟯).fixingSubgroup_isOpen
  have : ContinuousSMul G (𝓞 Ω) := continuousSMul_iff_stabilizer_isOpen.2 fun b =>
    (hopen b).preimage continuous_subtype_val
  have : Algebra.IsInvariant (𝓞 L) (𝓞 Ω) G := ⟨fun b hb => by
    have hmem : (b : Ω) ∈ fixedField L.fixingSubgroup := by
      rw [mem_fixedField_iff]
      intro f hf
      exact congrArg (fun c : 𝓞 Ω => (c : Ω)) (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Ω) (algebraMap L Ω).injective).1 b.isIntegral_coe
    exact ⟨⟨⟨b, hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩⟩
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := L) (E := Ω) τ
  have hgL : ∀ x : 𝓞 L, g • algebraMap (𝓞 L) (𝓞 Ω) x = algebraMap (𝓞 L) (𝓞 Ω) (τ • x) := fun x =>
    RingOfIntegers.ext (by
      rw [← hg]
      exact (AlgEquiv.restrictNormal_commutes g L x).symm)
  let _ : Field (𝓞 Ω ⧸ Q) := Ideal.Quotient.field Q
  have hunder : Q.under (𝓞 L) = (g⁻¹ • Q).under (𝓞 L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff, hgL, ← Ideal.Quotient.eq_zero_iff_mem (I := Q),
      ← Ideal.Quotient.eq_zero_iff_mem (I := Q), hτ, map_eq_zero θ]
  obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 L) (G := G) Q (g⁻¹ • Q) hunder
  set g' : Ω ≃ₐ[E] Ω := g * h with hg'
  have hst : g' • Q = Q := by
    rw [hg', mul_smul]
    exact (congrArg (g • ·) (show (h : Ω ≃ₐ[E] Ω) • Q = g⁻¹ • Q from hh.symm)).trans (smul_inv_smul g Q)
  have hmem : ∀ b : 𝓞 Ω, g'⁻¹ • b ∈ Q ↔ b ∈ Q := fun b => by
    rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hst]
  let u : 𝓞 Ω ⧸ Q →+* 𝓞 Ω ⧸ Q :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ _ g'⁻¹) fun b hb => (hmem b).2 hb
  have hu : ∀ b : 𝓞 Ω, u (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g'⁻¹ • b) := fun _ => rfl
  have hg'L : ∀ x : 𝓞 L, g'⁻¹ • algebraMap (𝓞 L) (𝓞 Ω) (τ • x) = algebraMap (𝓞 L) (𝓞 Ω) x := fun x => by
    rw [inv_smul_eq_iff, hg', mul_smul, ← hgL]
    exact congrArg (g • ·) (hfix h x).symm
  have : Algebra.IsIntegral (𝓞 L) (𝓞 Ω) := ⟨fun b => (RingOfIntegers.isIntegral b).tower_top⟩
  let ψ : (𝓞 Ω ⧸ Q) →ₐ[𝓞 L ⧸ Q.under (𝓞 L)] (𝓞 Ω ⧸ Q) :=
    { θ.comp u with
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ : ∃ y, τ • y = x := ⟨τ⁻¹ • x, smul_inv_smul τ x⟩
        show θ (u (Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • y)))) =
          Ideal.Quotient.mk Q (algebraMap (𝓞 L) (𝓞 Ω) (τ • y))
        rw [hu, hg'L, hτ] }
  have hmax : (Q.under (𝓞 L)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  let _ : Field (𝓞 L ⧸ Q.under (𝓞 L)) := Ideal.Quotient.field _
  have hbij : Function.Bijective ψ := Algebra.IsAlgebraic.algHom_bijective ψ
  obtain ⟨k, hk⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (Q.under (𝓞 L)) Q
    (AlgEquiv.ofBijective ψ hbij)
  refine ⟨((k : G) : Ω ≃ₐ[E] Ω) * g', ?_, fun b => ?_⟩
  · have hker : ∀ s : G, AlgEquiv.restrictNormalHom L (s : Ω ≃ₐ[E] Ω) = 1 := fun s => by
      rw [← MonoidHom.mem_ker, restrictNormalHom_ker]
      exact s.2
    rw [hg', map_mul, map_mul, hker, hker, hg, one_mul, mul_one]
  · have e := DFunLike.congr_fun hk (Ideal.Quotient.mk Q (g' • b))
    rw [mul_smul]
    refine (show _ = ψ (Ideal.Quotient.mk Q (g' • b)) from e).trans ?_
    show θ (u _) = _
    rw [hu, inv_smul_smul]

end CompanionTheory.PlaceDict
