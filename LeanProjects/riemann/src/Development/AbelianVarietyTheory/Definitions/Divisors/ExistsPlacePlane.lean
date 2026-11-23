import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair.Model

variable {k K : Type} [Field k] [Field K] {c : k →+* K} {n : ℕ}

theorem not_contains_top (E : Place c) : ¬ E.Contains ⊤ := fun h =>
  E.ring_ne_top (ValuationSubring.ext _ _ fun x => ⟨fun _ => trivial, fun _ => h x trivial⟩)

theorem klt_top_iff (η : Forms c n) (φ : K →₀ ℚ) : Klt c n ⊤ η φ ↔ η ≠ 0 ∧ φ 0 = 0 :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun E hE => (not_contains_top E hE).elim⟩⟩

theorem disc_smul [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) (E : Place c)
    {η : Forms c n} (hη : η ≠ 0) {f : K} (hf : f ≠ 0) (φ : K →₀ ℚ) :
    E.disc (f • η) (φ + Finsupp.single f 1) = E.disc η φ := by
  rw [Place.disc, Place.disc, E.formOrd_smul hx hη hf, map_add, Place.ordQ_single]
  push_cast
  ring

theorem klt_smul_iff [PerfectField k] {x : Fin n → K} (hx : TrBasis c x) (R : Subring K)
    {η : Forms c n} {f : K} (hf : f ≠ 0) (φ : K →₀ ℚ) :
    Klt c n R (f • η) (φ + Finsupp.single f 1) ↔ Klt c n R η φ := by
  have h0 : (φ + Finsupp.single f 1 : K →₀ ℚ) 0 = φ 0 := by
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hf.symm, add_zero]
  constructor
  · intro h
    have hη : η ≠ 0 := fun e => h.1 (by rw [e, smul_zero])
    exact ⟨hη, h0 ▸ h.2.1, fun E hE => disc_smul hx E hη hf φ ▸ h.lt_disc hE⟩
  · intro h
    exact ⟨smul_ne_zero hf h.1, h0 ▸ h.2.1,
      fun E hE => (disc_smul hx E h.1 hf φ).symm ▸ h.lt_disc hE⟩

theorem disc_single_mul (E : Place c) (η : Forms c n) {f g : K} (hf : f ≠ 0) (hg : g ≠ 0)
    (s : ℚ) : E.disc η (Finsupp.single (f * g) s) =
      E.disc η (Finsupp.single f s + Finsupp.single g s) := by
  rw [Place.disc, Place.disc, map_add, Place.ordQ_single, Place.ordQ_single, Place.ordQ_single,
    E.ord_mul hf hg]
  push_cast
  ring

theorem simple_pole (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    ¬ Klt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 ∧
      EffAt c n E.ring.toSubring ((t : K)⁻¹ • E.toRat n ω) 0 := by
  have h0 : (t : K)⁻¹ ≠ 0 := inv_ne_zero fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_inv, E.ord_irreducible ht]
  norm_num

theorem simple_zero (E : Place c) {ω : Forms E.const n} (hω : IsFreeGen E.ring ω)
    {t : E.ring} (ht : Irreducible t) :
    Klt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 ∧
      ¬ EffAt c n E.ring.toSubring ((t : K) • E.toRat n ω) 0 := by
  have h0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have h1 := smul_ne_zero h0 (E.toRat_ne_zero hω)
  rw [klt_ring_iff E h1 rfl, effAt_ring_iff E h1 rfl, Place.disc, E.formOrd_smul_toRat hω h0,
    E.ord_irreducible ht]
  norm_num

theorem isEmpty_place_self : IsEmpty (Place (RingHom.id k)) :=
  ⟨fun E => not_contains_top E fun f _ => E.const_mem f⟩

section Scheme

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem isPrimeOf_of_isAt {E : DivOver p} {x z : X} (hE : E.IsAt z) (hz : z ⤳ x) :
    (placeEquiv p E).IsPrimeOf (locRing x) := by
  refine ⟨hE.through hz, fun f hf => ?_⟩
  obtain ⟨a, rfl⟩ := (hE f).1 hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hzU : z ∈ U := hz.mem_open U.isOpen hx
  letI := X.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  obtain ⟨⟨r, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl
    (S := X.presheaf.stalk z) a
  have hs : IsUnit (X.presheaf.germ U z hzU s.1) :=
    IsLocalization.map_units (M := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl)
      (X.presheaf.stalk z) s
  have hs' : IsUnit (hE.equiv (X.presheaf.germ U z hzU s.1)) := hs.map hE.equiv.toRingHom
  have ho : (placeEquiv p E).ord
      (algebraMap _ X.functionField (X.presheaf.germ U z hzU s.1)) = 0 :=
    Place.ord_eq_zero (placeEquiv p E) (u := hE.equiv (X.presheaf.germ U z hzU s.1)) hs'
  have h1 (r : Γ(X, U)) :
      algebraMap _ X.functionField (X.presheaf.germ U z hzU r) ∈ locRing x :=
    ⟨X.presheaf.germ U x hx r, (algebraMap_germ hx r).trans (algebraMap_germ hzU r).symm⟩
  have h2 : algebraMap _ X.functionField (X.presheaf.germ U z hzU s.1) ≠ 0 :=
    (hs.map (algebraMap (X.presheaf.stalk z) X.functionField)).ne_zero
  have e' : a * X.presheaf.germ U z hzU s.1 = X.presheaf.germ U z hzU r := e
  refine ⟨_, h1 r, _, h1 s.1, h2, ho, ?_⟩
  rw [← map_mul, e']

theorem nonneg_of_effAt {Δ : X → ℚ} {η : RatForms p n} {x z : X} {m : ℕ}
    {g : X.functionFieldˣ} (h : IsLogEqn p Δ η x m g) (hm : 0 < m)
    (he : EffAt (Cartier.constFn p) n (locRing x) η
      (Finsupp.single (g : X.functionField) (1 / (m : ℚ))))
    {E : DivOver p} (hE : E.IsAt z) (hz : z ⤳ x) : 0 ≤ Δ z := by
  have := he.disc_le (isPrimeOf_of_isAt hE hz)
  rw [disc_placeEquiv, h.discrep_eq_neg hm hz hE] at this
  linarith

theorem exists_klt_smooth [PerfectField k] [SmoothOfRelativeDimension n p]
    (hn : topologicalKrullDim X = n) (x : X) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn p) n (locRing x) η φ := by
  haveI := SmoothOfRelativeDimension.smooth n p
  obtain ⟨η, m, g, -, -, h⟩ := (kltAt_iff_exists_klt (p := p) (n := n) 0 x).1
    (kltAt_zero_of_smooth hn x)
  exact ⟨isLocModel_locRing x, η, _, h⟩

end Scheme

theorem projectiveSpace (d : ℕ) (x : (ProjVar.proj ℂ d).X) :
    IsLocModel (Cartier.constFn (ProjVar.proj ℂ d).str) (locRing x) ∧
      ∃ η φ, Klt (Cartier.constFn (ProjVar.proj ℂ d).str) (ProjVar.proj ℂ d).dim (locRing x) η φ :=
  exists_klt_smooth (ProjVar.Var.topologicalKrullDim_eq _) x

theorem dForm_blowup (c : k →+* K) (t u : K) :
    dForm c ![t, t * u] = t • dForm c ![t, u] := by
  rw [dForm_eq, dForm_eq]
  letI := c.toAlgebra
  have e1 : (fun i => dFun c (![t, t * u] i)) =
      Function.update (fun i => dFun c (![t, u] i)) 1 (t • dFun c u + u • dFun c t) := by
    funext i
    fin_cases i
    · simp
    · simp [dFun, Derivation.leibniz]
  have e2 : Function.update (fun i => dFun c (![t, u] i)) 1 (dFun c u) =
      fun i => dFun c (![t, u] i) := by
    funext i
    fin_cases i <;> simp
  rw [e1, AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
    AlternatingMap.map_update_smul, e2,
    AlternatingMap.map_eq_zero_of_eq _ (Function.update _ 1 (dFun c t)) (i := 0) (j := 1)
      (by simp) (by decide), smul_zero, add_zero]

theorem exists_chart [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ t u : E.ring, Irreducible t ∧ IsUnit u ∧ IsUnit (u - 1) ∧
      IsFreeGen E.ring (dForm E.const ![t, u]) := by
  letI := E.const.toAlgebra
  letI := c.toAlgebra
  haveI : IsScalarTower k E.ring K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType k E.ring := E.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField k E.ring
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  obtain ⟨m, z, b, hz, hb⟩ := exists_basis_kaehler_uniformiser k ht
  have h1 := trdeg_eq_of_basis_kaehler k K b
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := k) hx
  rw [h1, Cardinal.mk_fin] at h2
  obtain rfl : m = 1 := by
    have : 2 = m + 1 := by exact_mod_cast h2
    omega
  have key (w : E.ring) (hw : KaehlerDifferential.D k E.ring w = b 1) : IsUnit w := by
    by_contra hu
    have hm : w ∈ Ideal.span {t} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht]
      exact hu
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hm
    rw [Derivation.leibniz, ← hz, ← hb 0] at hw
    have := congrArg (fun η => b.repr η 1) hw
    simp at this
    exact ht.not_isUnit (IsUnit.of_mul_eq_one _ (hz ▸ this))
  have ez : z = ![t, z 1] := by
    funext i
    fin_cases i
    · exact hz
    · rfl
  refine ⟨t, z 1, ht, key _ (hb 1).symm, key _ (by simp [hb 1]), ?_⟩
  rw [← ez]
  exact isFreeGen_dForm z b hb

theorem three_lines [PerfectField k] (E : Place c) {x : Fin 2 → K} (hx : TrBasis c x) :
    ∃ a b : K, a ∈ E.ring ∧ b ∈ E.ring ∧ dForm c ![a, b] ≠ 0 ∧ ∀ s : ℚ,
      E.disc (dForm c ![a, b])
        (Finsupp.single a s + Finsupp.single b s + Finsupp.single (b - a) s) = 1 - 3 * s ∧
      ∀ R : Subring K, E.Contains R → 2 / 3 ≤ s → ¬ Klt c 2 R (dForm c ![a, b])
        (Finsupp.single a s + Finsupp.single b s + Finsupp.single (b - a) s) := by
  obtain ⟨t, u, ht, hu, hu', hω⟩ := exists_chart E hx
  have h0 : (t : K) ≠ 0 := fun h => ht.ne_zero (Subtype.ext h)
  have e : dForm c ![(t : K), t * u] = (t : K) • E.toRat 2 (dForm E.const ![t, u]) := by
    have e' : E.toRat 2 (dForm E.const ![t, u]) = dForm c fun i => E.ring.subtype (![t, u] i) :=
      formMap_dForm (β := c) E.ring.subtype rfl _
    rw [dForm_blowup, e']
    congr 2
    funext i
    fin_cases i <;> rfl
  have o1 : E.ord ((t : K) * u) = 1 := by
    rw [E.ord_mul (g := u) h0 (hu.map E.ring.subtype).ne_zero, E.ord_irreducible ht, E.ord_eq_zero hu]
    rfl
  have o2 : E.ord ((t : K) * u - t) = 1 := by
    have : (t : K) * u - t = t * ((u - 1 : E.ring) : K) := by push_cast; ring
    rw [this, E.ord_mul (g := (u - 1 : E.ring)) h0 (hu'.map E.ring.subtype).ne_zero,
      E.ord_irreducible ht,
      E.ord_eq_zero hu']
    rfl
  have hd (s : ℚ) : E.disc (dForm c ![(t : K), t * u]) (Finsupp.single (t : K) s +
      Finsupp.single ((t : K) * u) s + Finsupp.single ((t : K) * u - t) s) = 1 - 3 * s := by
    rw [Place.disc, e, E.formOrd_smul_toRat hω h0, map_add, map_add, Place.ordQ_single,
      Place.ordQ_single, Place.ordQ_single, o1, o2, E.ord_irreducible ht]
    push_cast
    ring
  refine ⟨t, t * u, t.2, mul_mem t.2 u.2, e ▸ smul_ne_zero h0 (E.toRat_ne_zero hω),
    fun s => ⟨hd s, fun R hR hs h => ?_⟩⟩
  have := h.lt_disc hR
  rw [hd] at this
  linarith

theorem exists_place_plane :
    Nonempty (Place (Cartier.constFn (spMap (algebraMap k (Polynomial (Polynomial k)))))) ∧
    ∃ x : Fin 2 → (Sp (Polynomial (Polynomial k))).functionField,
      TrBasis (Cartier.constFn (spMap (algebraMap k (Polynomial (Polynomial k))))) x := by
  let z : Sp (Polynomial (Polynomial k)) := ⟨Ideal.span {Polynomial.X},
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X⟩
  have hz : Order.coheight z = 1 := by
    rw [← idealHeight_eq_coheight]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (R := Polynomial (Polynomial k))
      (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero) Polynomial.prime_X.not_unit
  haveI : Algebra.FiniteType k (Polynomial (Polynomial k)) :=
    .trans (S := Polynomial k) inferInstance inferInstance
  haveI : LocallyOfFiniteType (spMap (algebraMap k (Polynomial (Polynomial k)))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have hn : topologicalKrullDim (Sp (Polynomial (Polynomial k))) = (2 : ℕ) := by
    change topologicalKrullDim (PrimeSpectrum (Polynomial (Polynomial k))) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
    norm_num
  obtain ⟨E, -⟩ := DivOver.exists_isAt_of_coheight_eq_one
    (p := spMap (algebraMap k (Polynomial (Polynomial k)))) hz
  exact ⟨⟨placeEquiv _ E⟩, (isLocModel_locRing_and_exists_trBasis _ _ 2 z hn).2⟩

end GlobalTheory.FieldPair.Model
