import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapMaximalIdealEqOfFormallyUnramifiedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.UnramOrd

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem isUnit_iff (E : Place c) (x : E.ring) : IsUnit x ↔ (x : K) ≠ 0 ∧ E.ord x = 0 := by
  constructor
  · intro hx
    exact ⟨fun h => hx.ne_zero (Subtype.ext h), E.ord_eq_zero hx⟩
  · rintro ⟨h0, h1⟩
    have hm : (x : K)⁻¹ ∈ E.ring := by
      rw [← E.ord_nonneg_iff (inv_ne_zero h0), E.ord_inv, h1]; simp
    exact IsUnit.of_mul_eq_one ⟨_, hm⟩ (Subtype.ext (mul_inv_cancel₀ h0))

def incl (E : Place c) {T : Subring K} (h : E.Contains T) : T →+* E.ring :=
  T.subtype.codRestrict E.ring fun x => h x x.2

theorem isLocalization (E : Place c) {T : Subring K} (h : E.IsPrimeOf T) :
    letI := (incl E h.1).toAlgebra
    IsLocalization ((IsUnit.submonoid E.ring).comap (incl E h.1)) E.ring := by
  letI := (incl E h.1).toAlgebra
  refine ⟨fun y => y.2, fun z => ?_, fun {x y} e => ⟨1, ?_⟩⟩
  · obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 z z.2
    have hu : IsUnit (incl E h.1 ⟨b, hb⟩) := (isUnit_iff E _).2 ⟨hb0, hbo⟩
    exact ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, hu⟩⟩, Subtype.ext e⟩
  · have e' : (x : K) = y := congrArg (fun z : E.ring => (z : K)) e
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext e'

end GlobalTheory.FieldPair.UnramOrd

namespace GlobalTheory.FieldPair.UnramOrd

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem mem_comap_iff (E : Place c) {T : Subring K} (h : E.Contains T) (y : T) :
    y ∈ (IsLocalRing.maximalIdeal E.ring).comap (incl E h) ↔ (y : K) = 0 ∨ E.ord y ≠ 0 := by
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  change ¬((y : K) ≠ 0 ∧ E.ord y = 0) ↔ _
  tauto

theorem le_of_isPrimeOf (E : Place c) {T : Subring K} (h : E.IsPrimeOf T) (Q : Ideal T) [hQp : Q.IsPrime]
    (hQ : Q ≠ ⊥) (hle : Q ≤ (IsLocalRing.maximalIdeal E.ring).comap (incl E h.1)) :
    (IsLocalRing.maximalIdeal E.ring).comap (incl E h.1) ≤ Q := by
  obtain ⟨x, hxQ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ
  have hx0' : (x : K) ≠ 0 := fun e => hx0 (Subtype.ext e)
  intro y hy
  by_cases hy0 : (y : K) = 0
  · rw [show y = 0 from Subtype.ext hy0]; exact Q.zero_mem
  have hy1 : E.ord y ≠ 0 := ((mem_comap_iff E h.1 y).1 hy).resolve_left hy0
  have hyn : 0 ≤ E.ord y := (E.ord_nonneg_iff hy0).2 (h.1 _ y.2)
  have hxn : 0 ≤ E.ord x := (E.ord_nonneg_iff hx0').2 (h.1 _ x.2)
  set n := (E.ord x).toNat with hn
  have hnx : (n : ℤ) = E.ord x := Int.toNat_of_nonneg hxn
  have hf0 : (y : K) ^ n / x ≠ 0 := div_ne_zero (pow_ne_zero _ hy0) hx0'
  have hf : (y : K) ^ n / x ∈ E.ring := by
    rw [← E.ord_nonneg_iff hf0, div_eq_mul_inv, E.ord_mul (pow_ne_zero _ hy0) (inv_ne_zero hx0'),
      E.ord_pow, E.ord_inv, ← hnx]
    have hy2 : 1 ≤ E.ord y := by omega
    have hn0 : (0 : ℤ) ≤ n := by positivity
    nlinarith
  obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := h.2 _ hf
  have e' : y ^ n * ⟨b, hb⟩ = ⟨a, ha⟩ * x := by
    apply Subtype.ext
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
    rw [← e]; field_simp
  have hbQ : (⟨b, hb⟩ : T) ∉ Q := by
    intro hbq
    rcases (mem_comap_iff E h.1 _).1 (hle hbq) with h' | h'
    · exact hb0 h'
    · exact h' hbo
  have hm : y ^ n * ⟨b, hb⟩ ∈ Q := e' ▸ Q.mul_mem_left _ hxQ
  exact hQp.mem_of_pow_mem n ((hQp.mem_or_mem hm).resolve_right hbQ)

end GlobalTheory.FieldPair.UnramOrd

namespace GlobalTheory.FieldPair.UnramOrd

theorem ord_eq_of_etTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ)
    (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0)) →
  ∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K) := by
  intro K L _ _ cK cL r R T ι ψ τ P P0 hE hP hP0 hz
  have hinj : Function.Injective ι := fun a b e => by
    have := congrArg ψ e
    rwa [hE.retr, hE.retr] at this
  have hιK : ∀ g : R, (g : K) ≠ 0 → ((ι g : T) : L) ≠ 0 := fun g hg e => hg (by
    have : ι g = ι 0 := by rw [map_zero]; exact Subtype.ext e
    rw [hinj this]; rfl)
  have hz' : ∀ g : R, (g : K) ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) :=
    fun g hg => hz g fun e => hg (by rw [e]; rfl)
  letI : Algebra ℂ R := (cK.codRestrict R hE.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hE.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  have hφC : ∀ g : R, φ (MvPolynomial.C g) = ι g := fun g => MvPolynomial.eval₂Hom_C ι τ g
  letI : Algebra A T := φ.toAlgebra
  haveI : Algebra.FormallyEtale A T := hE.etale
  haveI : Algebra.EssFiniteType A T := by
    have h1 : (φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem))).EssFiniteType := by
      have e : φ.comp (MvPolynomial.C.comp (cK.codRestrict R hE.base.const_mem)) =
          cL.codRestrict T hE.top.const_mem := by
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, hφC]
        exact hE.const a
      rw [e]; exact hE.top.essFiniteType
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat A T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType A T
  let j : T →+* P.ring := incl P hP.1
  letI : Algebra T P.ring := j.toAlgebra
  letI : Algebra A P.ring := (j.comp φ).toAlgebra
  haveI : IsScalarTower A T P.ring := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isLocalization P hP
  haveI : Algebra.FormallyUnramified T P.ring :=
    Algebra.FormallyUnramified.of_isLocalization ((IsUnit.submonoid P.ring).comap j)
  haveI : Algebra.FormallyUnramified A P.ring := Algebra.FormallyUnramified.comp A T P.ring
  haveI : Algebra.EssFiniteType T P.ring :=
    Algebra.EssFiniteType.of_isLocalization P.ring ((IsUnit.submonoid P.ring).comap j)
  haveI : Algebra.EssFiniteType A P.ring := Algebra.EssFiniteType.comp A T P.ring
  have hmax := GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' A P.ring
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap j
  let p : Ideal R := (IsLocalRing.maximalIdeal P0.ring).comap (incl P0 hP0.1)
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hpq : ∀ g : R, g ∈ p ↔ ι g ∈ q := by
    intro g
    rw [mem_comap_iff P0 hP0.1, mem_comap_iff P hP.1]
    by_cases hg : (g : K) = 0
    · have : g = 0 := Subtype.ext hg
      subst this; simp
    · simp only [hg, hιK g hg, false_or]
      exact not_congr (hz' g hg)

  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible P0.ring
  obtain ⟨π, hπR, b, hbR, hb0, hbo, eπ⟩ := hP0.2 t t.2
  have ht0 : (t : K) ≠ 0 := fun e => ht.ne_zero (Subtype.ext e)
  have hπ0 : π ≠ 0 := by rw [← eπ]; exact mul_ne_zero ht0 hb0
  have hπo : P0.ord π = 1 := by
    rw [← eπ, P0.ord_mul ht0 hb0, hbo, P0.ord_irreducible ht, add_zero]
  let π' : R := ⟨π, hπR⟩
  have hdiv : ∀ g : R, (g : K) ≠ 0 → ∀ k : ℕ, (k : ℤ) ≤ P0.ord g →
      ∃ a b : R, (b : K) ≠ 0 ∧ P0.ord b = 0 ∧ g * b = a * π' ^ k := by
    intro g hg k hk
    have hπk : (π : K) ^ k ≠ 0 := pow_ne_zero _ hπ0
    have hf0 : (g : K) / π ^ k ≠ 0 := div_ne_zero hg hπk
    have hf : (g : K) / π ^ k ∈ P0.ring := by
      rw [← P0.ord_nonneg_iff hf0, div_eq_mul_inv, P0.ord_mul hg (inv_ne_zero hπk), P0.ord_inv,
        P0.ord_pow, hπo]
      linarith
    obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP0.2 _ hf
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hb0, hbo, Subtype.ext ?_⟩
    show (g : K) * b = a * π ^ k
    rw [← e]
    field_simp
  have hπp : π' ∈ p := (mem_comap_iff P0 hP0.1 π').2 (Or.inr (by rw [show ((π' : R) : K) = π from rfl, hπo]; simp))

  have hq' : q.comap (algebraMap A T) = Ideal.map (MvPolynomial.C : R →+* A) p := by
    have hle : Ideal.map (MvPolynomial.C : R →+* A) p ≤ q.comap (algebraMap A T) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change φ (MvPolynomial.C g) ∈ q
      rw [hφC]
      exact (hpq g).1 hg
    haveI : (q.comap (algebraMap A T)).IsPrime := Ideal.comap_isPrime _ _
    haveI : q.LiesOver (q.comap (algebraMap A T)) := ⟨rfl⟩
    haveI : (Ideal.map (MvPolynomial.C : R →+* A) p).IsPrime := by
      rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
      exact RingHom.ker_isPrime _
    obtain ⟨Q, hQq, hQp, hQl⟩ := Ideal.exists_ideal_le_liesOver_of_le
      (p := Ideal.map (MvPolynomial.C : R →+* A) p) (q := q.comap (algebraMap A T)) q hle
    have hQ0 : Q ≠ ⊥ := by
      intro hQ
      have hm : MvPolynomial.C π' ∈ Q.comap (algebraMap A T) := by
        rw [← Ideal.under_def, ← hQl.over]
        exact Ideal.mem_map_of_mem _ hπp
      rw [hQ, Ideal.mem_comap, Ideal.mem_bot] at hm
      change φ (MvPolynomial.C π') = 0 at hm
      rw [hφC] at hm
      exact hιK π' hπ0 (by rw [hm]; rfl)
    have hQe := le_antisymm hQq (le_of_isPrimeOf P hP Q hQ0 hQq)
    rw [← hQe, ← Ideal.under_def]
    exact hQl.over.symm

  have hspan : IsLocalRing.maximalIdeal P.ring ≤ Ideal.span {j (ι π')} := by
    have e1 : (IsLocalRing.maximalIdeal P.ring).comap (algebraMap A P.ring) =
        q.comap (algebraMap A T) := by
      rw [IsScalarTower.algebraMap_eq A T P.ring, ← Ideal.comap_comap]
      rfl
    rw [← hmax, e1, hq', Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    change j (φ (MvPolynomial.C g)) ∈ _
    rw [hφC]
    by_cases hg0 : (g : K) = 0
    · rw [show g = 0 from Subtype.ext hg0, map_zero, map_zero]
      exact Ideal.zero_mem _
    have hk : ((1 : ℕ) : ℤ) ≤ P0.ord g := by
      have h1 := ((mem_comap_iff P0 hP0.1 g).1 hg).resolve_left hg0
      have h2 := (P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)
      push_cast
      omega
    obtain ⟨a, b, hb0, hbo, e⟩ := hdiv g hg0 1 hk
    have hu : IsUnit (j (ι b)) := (isUnit_iff P _).2 ⟨hιK b hb0, (hz' b hb0).1 hbo⟩
    have e' : j (ι g) * j (ι b) = j (ι a) * j (ι π') := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, e, pow_one]
    rw [Ideal.mem_span_singleton']
    refine ⟨j (ι a) * ↑hu.unit⁻¹, ?_⟩
    rw [mul_right_comm, ← e', mul_assoc, IsUnit.mul_val_inv, mul_one]
  have hπ1 : P.ord ((ι π' : T) : L) = 1 := by
    obtain ⟨s, hs⟩ := IsDiscreteValuationRing.exists_irreducible P.ring
    have hsm : s ∈ IsLocalRing.maximalIdeal P.ring :=
      (IsLocalRing.mem_maximalIdeal _).2 hs.not_isUnit
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hspan hsm)
    have hs0 : (s : L) ≠ 0 := fun e => hs.ne_zero (Subtype.ext e)
    have hc' : (c : L) * ((ι π' : T) : L) = s := congrArg Subtype.val hc
    have hc0 : (c : L) ≠ 0 := fun e => hs0 (by rw [← hc', e, zero_mul])
    have hπ0' := hιK π' hπ0
    have h1 := P.ord_irreducible hs
    rw [← hc', P.ord_mul hc0 hπ0'] at h1
    have h2 := (P.ord_nonneg_iff hc0).2 c.2
    have h3 : P.ord ((ι π' : T) : L) ≠ 0 :=
      ((mem_comap_iff P hP.1 (ι π')).1 ((hpq π').1 hπp)).resolve_left hπ0'
    have h4 := (P.ord_nonneg_iff hπ0').2 (hP.1 _ (ι π').2)
    omega
  intro g hg
  have hg0 : (g : K) ≠ 0 := fun e => hg (Subtype.ext e)
  have hgn := (P0.ord_nonneg_iff hg0).2 (hP0.1 _ g.2)
  obtain ⟨a, b, hb0, hbo, e⟩ := hdiv g hg0 (P0.ord g).toNat (by rw [Int.toNat_of_nonneg hgn])
  have eK : (g : K) * b = a * π ^ (P0.ord g).toNat := congrArg Subtype.val e
  have ha0 : (a : K) ≠ 0 := by
    intro ha
    rw [ha, zero_mul] at eK
    exact mul_ne_zero hg0 hb0 eK
  have hao : P0.ord a = 0 := by
    have := congrArg P0.ord eK
    rw [P0.ord_mul hg0 hb0, P0.ord_mul ha0 (pow_ne_zero _ hπ0), P0.ord_pow, hπo, hbo,
      Int.toNat_of_nonneg hgn] at this
    linarith
  have eL : ((ι g : T) : L) * ((ι b : T) : L) = ((ι a : T) : L) * ((ι π' : T) : L) ^ (P0.ord g).toNat := by
    have := congrArg (fun x : R => ((ι x : T) : L)) e
    simpa using this
  have := congrArg P.ord eL
  rw [P.ord_mul (hιK g hg0) (hιK b hb0), P.ord_mul (hιK a ha0) (pow_ne_zero _ (hιK π' hπ0)),
    P.ord_pow, hπ1, (hz' b hb0).1 hbo, (hz' a ha0).1 hao, Int.toNat_of_nonneg hgn] at this
  linarith

end GlobalTheory.FieldPair.UnramOrd
