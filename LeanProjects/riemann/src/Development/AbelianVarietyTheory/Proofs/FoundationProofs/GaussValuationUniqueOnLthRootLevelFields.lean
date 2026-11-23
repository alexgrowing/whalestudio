import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGaussStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunctionStatement

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.UniqRoot

theorem exists_finite_field {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (A : Set E) (hfin : A.Finite)
    (hA : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin F {t}) a) :
    ∃ (L : IntermediateField F E) (ht : t ∈ L), A ⊆ L ∧
      FiniteDimensional (IntermediateField.adjoin F {(⟨t, ht⟩ : L)}) L := by
  let K₀ : IntermediateField F E := IntermediateField.adjoin F {t}
  let L' : IntermediateField K₀ E := IntermediateField.adjoin K₀ A
  haveI : Finite A := hfin
  have hL' : FiniteDimensional K₀ L' := IntermediateField.finiteDimensional_adjoin fun a ha => (hA a ha).isIntegral
  let L : IntermediateField F E := L'.restrictScalars F
  have hK : ∀ x : K₀, (x : E) ∈ L := fun x => L'.algebraMap_mem x
  have ht : t ∈ L := hK ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
  refine ⟨L, ht, fun a ha => IntermediateField.subset_adjoin K₀ A ha, ?_⟩
  let K' : IntermediateField F L := IntermediateField.adjoin F {(⟨t, ht⟩ : L)}
  have hmap : K'.map L.val = K₀ := by
    simp only [K', K₀, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ x : K₀, (⟨x, hK x⟩ : L) ∈ K' := by
    intro x
    have hx : (x : E) ∈ K'.map L.val := by rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hK x⟩ := Subtype.ext hyx
    exact this ▸ hy
  let φ : K₀ →+* K' :=
    { toFun := fun x => ⟨⟨x, hK x⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₀ K' := φ.toAlgebra
  letI : Algebra K₀ L := (inferInstance : Algebra K₀ L')
  haveI : Module.Finite K₀ L := hL'
  haveI : IsScalarTower K₀ K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K₀ K' L

theorem valuation_eq_one_iff' {K : Type} [Field K] (W : ValuationSubring K) (x : K) :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by rw [h, inv_one]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 < W.valuation x := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

theorem gauss_comap {F E : Type} [Field F] [Field E] [Algebra F E] {t : E} (L : IntermediateField F E) (ht : t ∈ L)
    {V : ValuationSubring F} {W : ValuationSubring E} (h : Gauss t V W) :
    Gauss (⟨t, ht⟩ : L) V (W.comap (algebraMap L E)) := by
  refine ⟨fun a => ?_, fun P hP hu => ?_⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact h.1 a
  · have h1 := (valuation_eq_one_iff' _ _).1 (h.2 P hP hu)
    have e : algebraMap L E (Polynomial.aeval (⟨t, ht⟩ : L) P) = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply L.val (⟨t, ht⟩ : L) P).symm
    rw [valuation_eq_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, e]
    refine ⟨fun h0 => h1.1 ?_, h1.2⟩
    rw [← e, h0, map_zero]

theorem transcendental_j {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  intro h
  have hd := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible h.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω X.jK hd
  have h1 := X.j_exp.1
  rw [← hc, AlgHom.commutes] at h1
  simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single] at h1

theorem gauss_unique_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  classical
  intro Ω _ _ _ ε X hj l M₀ hl hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halgΩ : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert halgΩ
    exact Subsingleton.elim _ _
  obtain ⟨R, hR⟩ := GlobalTheory.KZ.FinLev.finite_mod_powers ε X ε.injective hj M₀ l hM hl.pos
  obtain ⟨T, -, hT⟩ := GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions ε X hj M₀ hM
  let E := AlgebraicClosure X.K
  let ι : X.K →ₐ[Ω] E := IsScalarTower.toAlgHom Ω X.K E
  let t : E := algebraMap X.K E X.jK
  have hmap : (IntermediateField.adjoin Ω {X.jK}).map ι = IntermediateField.adjoin Ω {t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin Ω {X.jK}, ι c ∈ IntermediateField.adjoin Ω {t} :=
    fun c => hmap ▸ ⟨c, c.2, rfl⟩
  have halg : ∀ f : X.K, IsAlgebraic (IntermediateField.adjoin Ω {t}) (algebraMap X.K E f) := by
    intro f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* IntermediateField.adjoin Ω {t} :=
      (ι.toRingHom.comp (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)).codRestrict
        (IntermediateField.adjoin Ω {t}) hmem
    exact ((X.alg_j f).isIntegral.map_of_comp_eq φ (algebraMap X.K E) (RingHom.ext fun _ => rfl)).isAlgebraic
  let A : Set E := algebraMap X.K E '' (T : Set X.K) ∪
    ⋃ r ∈ (R : Set X.Kˣ), {y : E | y ^ l = algebraMap X.K E (r : X.K)}
  have hAfin : A.Finite := by
    refine (T.finite_toSet.image _).union (R.finite_toSet.biUnion fun r _ => ?_)
    refine (Polynomial.nthRoots l (algebraMap X.K E (r : X.K))).toFinset.finite_toSet.subset fun y hy => ?_
    simpa [Polynomial.mem_nthRoots hl.pos] using hy
  have hAalg : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin Ω {t}) a := by
    rintro a (⟨f, -, rfl⟩ | ha)
    · exact halg f
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ha
      obtain ⟨r, -, hr⟩ := ha
      exact IsAlgebraic.of_pow hl.pos (hr ▸ halg r)
  obtain ⟨L, ht, hAL, hfin⟩ := exists_finite_field (F := Ω) t A hAfin hAalg
  have htr : Transcendental Ω (⟨t, ht⟩ : L) := by
    intro h
    have h1 : IsAlgebraic Ω (ι X.jK) := h.algHom L.val
    exact transcendental_j X ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).1 h1)
  obtain ⟨S, hS⟩ := GlobalTheory.T.gauss_valuationSubring_unique_away_finset (F := Ω) (⟨t, ht⟩ : L) htr hfin
  have hlev : ∀ f : X.K, Lev X M₀ f → algebraMap X.K E f ∈ L := by
    intro f hf
    have hsp := hT f hf
    clear hf
    induction hsp using Submodule.span_induction with
    | mem x hx => exact hAL (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact L.add_mem hx hy
    | smul c x _ hx =>
      have hc : ι c ∈ L := (IntermediateField.adjoin_simple_le_iff.2 ht) (hmem c)
      have e : algebraMap X.K E (c • x) = ι c * algebraMap X.K E x := by
        rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
        rfl
      rw [e]
      exact L.mul_mem hc hx
  have hlevF : levF X M₀ ≤ L := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hlev f hf
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ θ f hf hfl hθ x hx => ?_⟩
  have hW := hS q hq hqS V hV _ _ (gauss_comap L ht h₁) (gauss_comap L ht h₂)
  obtain ⟨r, hr, g, hg, c, hc, hfe⟩ := hR f hf hfl
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hd
    exact hc hd.symm
  let u : E := algebraMap X.K E (g : X.K) * algebraMap Ω E d
  have hu0 : u ≠ 0 := mul_ne_zero ((map_ne_zero _).2 g.ne_zero) ((map_ne_zero _).2 hd0)
  have huL : u ∈ L := L.mul_mem (hlev g hg) (L.algebraMap_mem d)
  have hy : (θ / u) ^ l = algebraMap X.K E (r : X.K) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hu0), hθ, hfe, mul_pow, ← map_pow, ← map_pow, hd, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc]
  have hθL : θ ∈ L := by
    have h1 : θ / u ∈ L := hAL (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hr) hy))
    have := L.mul_mem h1 huL
    rwa [div_mul_cancel₀ _ hu0] at this
  have hxL : x ∈ L := by
    have hle : IntermediateField.adjoin (levF X M₀) {θ} ≤ IntermediateField.extendScalars hlevF :=
      IntermediateField.adjoin_simple_le_iff.2 hθL
    exact hle hx
  have := SetLike.ext_iff.1 hW ⟨x, hxL⟩
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
  exact this

end GlobalTheory.KZ.ES.UniqRoot
