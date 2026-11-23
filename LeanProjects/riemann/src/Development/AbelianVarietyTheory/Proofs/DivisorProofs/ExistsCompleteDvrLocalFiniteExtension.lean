import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitPlace

theorem exists_valuationSubring_of_injective {S K : Type} [CommRing S] [Field K] (f : S →+* K)
    (hf : Function.Injective f) (I : Ideal S) (hI : I ≠ ⊤) :
    ∃ B : ValuationSubring K, ∀ x ∈ I, f x ∈ B.nonunits := by
  have hb : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hI' : I.map f.rangeRestrict ≠ ⊤ := by
    intro h
    apply hI
    rw [← Ideal.comap_map_of_bijective f.rangeRestrict hb (I := I), h, Ideal.comap_top]
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI'
  exact ⟨B, fun x hx => hB ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩⟩

theorem mem_of_forall_prime {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F]
    (O : ValuationSubring F) (h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits) (x : F) : x ∈ O := by
  have h1 : ∀ n : ℕ, (n : F)⁻¹ ∈ O := by
    intro n
    induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime p hp =>
      have := h p hp
      rw [ValuationSubring.mem_nonunits_iff_or] at this
      push Not at this
      exact this.2
    | mul a b ha hb =>
      rw [Nat.cast_mul, mul_inv]
      exact O.mul_mem _ _ ha hb
  have h2 : ∀ q : ℚ, algebraMap ℚ F q ∈ O := by
    intro q
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact O.mul_mem _ _ (intCast_mem O _) (h1 _)
  let g : ℚ →+* O := (algebraMap ℚ F).codRestrict O h2
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hx' : IsIntegral O x := by
    obtain ⟨P, hP, hP0⟩ := hx
    refine ⟨P.map g, hP.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hP0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2

theorem exists_place (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (O : ValuationSubring F) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      ∀ x : F, (x : ℂ) ∈ W → x ∈ O := by
  by_cases h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits
  · obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (Int.castRingHom ℂ) Int.cast_injective
      (Ideal.span {(2 : ℤ)}) (by
        rw [Ne, Ideal.span_singleton_eq_top]
        decide)
    refine ⟨2, B, Nat.prime_two, ?_, fun x _ => mem_of_forall_prime O h x⟩
    simpa using hB 2 (Ideal.mem_span_singleton_self _)
  · push Not at h
    obtain ⟨p, hp, hpO⟩ := h
    obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (F.val.toRingHom.comp O.subtype)
      (fun a b h => Subtype.ext (Subtype.ext h)) (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
    have hB' : ∀ x : F, x ∈ O.nonunits → (x : ℂ) ∈ B.nonunits := fun x hx =>
      hB ⟨x, O.nonunits_subset hx⟩ (ValuationSubring.coe_mem_nonunits_iff.1 hx)
    refine ⟨p, B, hp, by simpa using hB' _ hpO, fun x hx => ?_⟩
    by_contra hxO
    have h0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have h1 : x⁻¹ ∈ O.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or]
      right
      rwa [inv_inv]
    have h2 := hB' _ h1
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    rcases h2 with h2 | h2
    · exact h0 (by simpa using h2)
    · exact h2 (by simpa using hx)

theorem exists_finite_ext (F K : Type) [Field F] [CharZero F] [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  first
  | exact @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | (apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding ..)

theorem exists_place_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (p : ℕ) (hp : p.Prime) (W₀ : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W₀.nonunits) (i : Idx H p) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : R →+* V₁) (b₁ : ↥(i.c.V W₀) →+* V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ρ₁ ∧ Function.Injective b₁ := by
  intro R _ _ _ hR E _ _ _ H
  obtain ⟨h1, h2, h3⟩ := hR
  obtain ⟨l, -, hg, hi⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨⟨l', c, hg2⟩, hl⟩ := hi 2 Nat.prime_two
  have hg' : ∀ p : ℕ, p.Prime → l'.GoodAt p := by
    subst hl
    exact hg
  haveI := c.fin
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨L, _, _, hL, ⟨jF⟩⟩ := exists_finite_ext c.F (FractionRing R)
  obtain ⟨V, _, _, hV, hVc, _, _, _, -, hfin, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) L
  have hVL := IsFractionRing.injective V L
  let O : ValuationSubring c.F := ValuationSubring.ofSubring ((algebraMap V L).range.comap jF) (fun x => by
    rcases ValuationRing.isInteger_or_isInteger V (jF x) with h | h
    · exact Or.inl h
    · right
      change jF x⁻¹ ∈ (algebraMap V L).range
      rw [map_inv₀]
      exact h)
  obtain ⟨p, W, hp, hW, hO⟩ := exists_place c.F O
  let e : V ≃+* (algebraMap V L).range := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hVL (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let g : c.V W →+* (algebraMap V L).range :=
    (jF.comp (c.V W).subtype).codRestrict _ (fun x => hO x.1 x.2)
  refine ⟨p, hp, W, hW, ⟨l', c, hg' p hp⟩, V, inferInstance, inferInstance, inferInstance, algebraMap R V,
    e.symm.toRingHom.comp g, ⟨hV, hVc, charZero_of_injective_algebraMap hinj⟩, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, ?_⟩
  intro a b h
  exact Subtype.ext (jF.injective (congrArg Subtype.val (e.symm.injective h)))

end GlobalTheory.TraitPlace
