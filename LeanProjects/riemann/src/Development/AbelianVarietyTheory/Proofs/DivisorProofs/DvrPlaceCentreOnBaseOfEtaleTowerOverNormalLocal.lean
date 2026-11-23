import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceIsPrimeOfOfHeightOneNormalLocalModelStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem Place.ord_eq_zero_iff_isUnit {L : Type} [Field L] {cL : ℂ →+* L} (P : Place cL) {u : P.ring}
    (hu : u ≠ 0) : P.ord (u : L) = 0 ↔ IsUnit u := by
  refine ⟨fun h => ?_, P.ord_eq_zero⟩
  have hu' : (u : L) ≠ 0 := fun e => hu (Subtype.ext e)
  have hi : (u : L)⁻¹ ∈ P.ring := by
    rw [← P.ord_nonneg_iff (inv_ne_zero hu'), P.ord_inv, h, neg_zero]
  exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hu'))

theorem Place.exists_centre_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (T : Subring L) (P : Place cL), P.IsPrimeOf T →
    ∃ q : Ideal T, q.IsPrime ∧ q.height = 1 ∧ ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := by
  intro L _ cL T P hP
  have hC : ∀ t : T, (t : L) ∈ P.ring := fun t => hP.1 _ t.2
  let f : T →+* P.ring := T.subtype.codRestrict P.ring hC
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap f
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ t : T, t ∉ q ↔ IsUnit (f t) := fun t => by
    simp only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hf : ∀ t : T, ((f t : P.ring) : L) = t := fun t => rfl
  have hord : ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := fun t ht => by
    rw [hmem t]
    have h0 : f t ≠ 0 := by
      intro e
      apply ht
      apply Subtype.ext
      rw [← hf t, e]
      simp
    have h1 := P.ord_eq_zero_iff_isUnit h0
    rw [hf t] at h1
    exact h1
  letI : Algebra T P.ring := f.toAlgebra
  haveI : IsLocalization.AtPrime P.ring q :=
    { map_units := fun y => (hmem y).1 y.2
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        have hb' : (⟨b, hb⟩ : T) ∉ q :=
          (hord ⟨b, hb⟩ (fun e' => hb0 (congrArg Subtype.val e'))).1 hbo
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb'⟩), Subtype.ext e⟩
      exists_of_eq := fun {x y} e => ⟨1, by
        have h' : ((algebraMap T P.ring x : P.ring) : L) = ((algebraMap T P.ring y : P.ring) : L) :=
          congrArg Subtype.val e
        have : x = y := Subtype.ext h'
        rw [this]⟩ }
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q P.ring
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at hd
  refine ⟨q, hq, ?_, hord⟩
  exact_mod_cast hd.symm

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem IsEtTower.flat {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) : IsNoetherianRing R ∧ ι.Flat := by
  letI := (cK.codRestrict R h.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI hR : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  refine ⟨hR, ?_⟩
  let B := MvPolynomial (Fin r) R
  let e : B →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra B T := e.toAlgebra
  letI : Algebra R T := ι.toAlgebra
  haveI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun a => by
    show ι a = e (MvPolynomial.C a)
    exact (MvPolynomial.eval₂_C _ _ _).symm
  haveI : Algebra.FormallyEtale B T := h.etale
  have hc : (cL.codRestrict T h.top.const_mem) = e.comp ((algebraMap R B).comp (cK.codRestrict R h.base.const_mem)) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have h2 : e (MvPolynomial.C (cK.codRestrict R h.base.const_mem a)) = ι ⟨cK a, h.base.const_mem a⟩ :=
      MvPolynomial.eval₂_C _ _ _
    show cL a = ((e ((algebraMap R B) (cK.codRestrict R h.base.const_mem a)) : T) : L)
    rw [MvPolynomial.algebraMap_eq, h2, h.const]
  haveI : Algebra.EssFiniteType B T := by
    have h1 := h.top.essFiniteType
    rw [hc] at h1
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat B T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType B T
  haveI : Module.Flat R T := Module.Flat.trans R B T
  exact RingHom.flat_algebraMap_iff.2 inferInstance

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem centre_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  intro K L _ _ cK cL r R T ι ψ τ P h hP
  obtain ⟨-, hF⟩ := h.flat
  obtain ⟨q, hq, hq1, hqo⟩ := Place.exists_centre_of_isPrimeOf cL T P hP
  letI : Algebra R T := ι.toAlgebra
  haveI : Module.Flat R T := hF
  haveI : Algebra.HasGoingDown R T := Algebra.HasGoingDown.of_flat
  let p : Ideal R := q.comap ι
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : q.LiesOver p := ⟨rfl⟩
  have hinj : Function.Injective ι := fun a b e => by simpa [h.retr] using congrArg ψ e
  have hι : ∀ g : R, g ≠ 0 → (P.ord (ι g : L) = 0 ↔ g ∉ p) := fun g hg =>
    hqo (ι g) ((map_ne_zero_iff ι hinj).2 hg)
  by_cases hp0 : p = ⊥
  · left
    intro g hg
    exact (hι g hg).2 (by rw [hp0]; simpa using hg)
  · right
    have hp1 : p.height = 1 := by
      apply le_antisymm
      · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
        intro p' hp' hlt
        haveI := hp'
        rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot]
        by_contra hne
        obtain ⟨Q, hQq, hQ, hQo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := T) q hlt
        haveI := hQ
        have hQ0 : Q ≠ ⊥ := by
          rintro rfl
          apply hne
          rw [hQo.over]
          ext x
          simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
          exact ⟨fun e => hinj (e.trans (map_zero ι).symm), fun e => by simp [e]⟩
        have h1 : 1 ≤ Q.height := ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hQ0)
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQq
        rw [hq1] at h2
        have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
        exact absurd h3 (by decide)
      · exact ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hp0)
    obtain ⟨P0, h0, h0o⟩ := GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel cK R h.base h.normal p inferInstance hp1
    exact ⟨P0, h0, fun g hg => (h0o g hg).trans (hι g hg).symm⟩

end GlobalTheory.FieldPair
