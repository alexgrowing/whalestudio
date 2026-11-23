import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPointIdealIffEvalCoordsZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiprojectivePrimeEqPointIdeal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticone
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedFormNonzeroOnGenericPoint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHypC
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagOrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinimalPrimesMap

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime divSupp multAt)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn)
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ

namespace GlobalTheory.CompanionTheory.MixZ.CycleRat

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} [IsIntegral X] {i : X ⟶ MP ℤ m n}

section Points

variable [IsClosedImmersion i]

theorem specializes_iff (x y : X) : x ⤳ y ↔ ptIdeal (i x) ≤ ptIdeal (i y) := by
  rw [← Spec.specializes_iff_ptIdeal_le m n (i x) (i y)]
  exact (i.isEmbedding.isInducing.specializes_iff).symm

theorem ptIdeal_injective : Function.Injective fun z : X => ptIdeal (i z) := fun x y h =>
  (((specializes_iff (i := i) x y).2 (le_of_eq h)).antisymm
    ((specializes_iff (i := i) y x).2 (le_of_eq h.symm))).eq

theorem exists_point {W : Ideal (Pol n)} (hW : IsMultiProjPrime W)
    (hle : ptIdeal (i (genericPoint X)) ≤ W) : ∃ z : X, ptIdeal (i z) = W := by
  obtain ⟨x, rfl⟩ := Onto.exists_ptIdeal_eq m n W hW
  have hs : i (genericPoint X) ⤳ x := (Spec.specializes_iff_ptIdeal_le m n _ _).2 hle
  have hr : x ∈ Set.range i :=
    i.isClosedEmbedding.isClosed_range.closure_subset_iff.2 (by simp) (specializes_iff_mem_closure.1 hs)
  obtain ⟨z, rfl⟩ := hr
  exact ⟨z, rfl⟩

end Points

section Krull

theorem eq_or_eq_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A] {P Q W : Ideal A} [hP : P.IsPrime]
    [hQ : Q.IsPrime] {s : A} (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) (hPQ : P ≤ Q) (hQW : Q ≤ W) :
    Q = P ∨ Q = W :=
  _root_.UpperTheory.Reformulated.B.MinimalPrimesMap.eq_or_eq_of_mem_minimalPrimes hW hPQ hQW

end Krull

section Codim

variable [IsClosedImmersion i]

theorem coheight_eq_one_of_mem_minimalPrimes {s : Pol n} (hs : s ∉ ptIdeal (i (genericPoint X))) {z : X}
    (hz : ptIdeal (i z) ∈ (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}).minimalPrimes) :
    Order.coheight z = 1 := by
  have hg (w : X) : w ≤ genericPoint X := genericPoint_specializes w
  have : (ptIdeal (i (genericPoint X))).IsPrime := (isMultiProjPrime_ptIdeal m n _).1
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_)
    (Order.one_le_iff_ne_zero.2 fun h => ?_)
  · have : (ptIdeal (i y)).IsPrime := (isMultiProjPrime_ptIdeal m n _).1
    have h1 : y = genericPoint X := by
      have hle : y ⤳ z := hy.le
      rcases eq_or_eq_of_mem_minimalPrimes hz
        ((specializes_iff (i := i) _ _).1 (genericPoint_specializes y))
        ((specializes_iff (i := i) _ _).1 hle) with e | e
      · exact ptIdeal_injective (i := i) e
      · exact absurd (ptIdeal_injective (i := i) e) hy.ne'
    have h2 : Order.coheight y = 0 := Order.coheight_eq_zero.2 fun w _ => h1 ▸ hg w
    simp [h2]
  · have h1 : z ⤳ genericPoint X := Order.coheight_eq_zero.1 h (hg z)
    have h2 : ptIdeal (i z) ≤ ptIdeal (i (genericPoint X)) := (specializes_iff (i := i) _ _).1 h1
    exact hs (h2 (hz.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))

theorem exists_point_of_mem_divSupp {s : Pol n} {a : Fin (m + 1) → ℕ} (hsa : IsMultiHomog s a)
    (hs : s ∉ ptIdeal (i (genericPoint X))) {W : Ideal (Pol n)}
    (hW : W ∈ divSupp (ptIdeal (i (genericPoint X))) s) : ∃ z : X, Order.coheight z = 1 ∧ ptIdeal (i z) = W := by
  have hh : IsMultiHomogIdeal W :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes (isMultiProjPrime_ptIdeal m n _).2.1 hsa hW.1
  obtain ⟨z, rfl⟩ := exists_point (i := i) (W := W) ⟨hW.1.1.1, hh, hW.2⟩ (le_sup_left.trans hW.1.1.2)
  exact ⟨z, coheight_eq_one_of_mem_minimalPrimes hs hW.1, rfl⟩

theorem mem_divSupp_of_coheight_eq_one {s : Pol n} {a : Fin (m + 1) → ℕ} (hsa : IsMultiHomog s a)
    (hs : s ∉ ptIdeal (i (genericPoint X))) {z : X} (hz : Order.coheight z = 1) (hsz : s ∈ ptIdeal (i z)) :
    ptIdeal (i z) ∈ divSupp (ptIdeal (i (genericPoint X))) s := by
  have hp := isMultiProjPrime_ptIdeal m n (i z)
  have := hp.1
  have hPz : ptIdeal (i (genericPoint X)) ≤ ptIdeal (i z) :=
    (specializes_iff (i := i) _ _).1 (genericPoint_specializes z)
  have hJ : ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s} ≤ ptIdeal (i z) :=
    sup_le hPz ((Ideal.span_singleton_le_iff_mem _).2 hsz)
  obtain ⟨Q, hQ, hQz⟩ := Ideal.exists_minimalPrimes_le hJ
  have hh : IsMultiHomogIdeal Q :=
    Geo.isMultiHomogIdeal_of_mem_minimalPrimes (isMultiProjPrime_ptIdeal m n _).2.1 hsa hQ
  have hrel : IsRelevant Q := fun k => by
    obtain ⟨j, hj⟩ := hp.2.2 k
    exact ⟨j, fun h => hj (hQz h)⟩
  obtain ⟨y, rfl⟩ := exists_point (i := i) (W := Q) ⟨hQ.1.1, hh, hrel⟩ (le_sup_left.trans hQ.1.2)
  have hzy : y ⤳ z := (specializes_iff (i := i) _ _).2 hQz
  have hyz : y = z := by
    by_contra hne
    have hlt : z < y := lt_of_le_not_ge hzy fun e => hne (hzy.antisymm e).eq
    have h1 := Order.coheight_add_one_le hlt
    have h2 := coheight_eq_one_of_mem_minimalPrimes hs hQ
    rw [hz, h2] at h1
    exact absurd h1 (by decide)
  subst hyz
  exact ⟨hQ, hp.2.2⟩

end Codim

section Chart

def phi (i : X ⟶ MP ℤ m n) (c : ∀ k, Bk n k) : Pol n →+* Γ(X, i ⁻¹ᵁ mchart c) :=
  (i.app (mchart c)).hom.comp (dehomog c)

variable (c : ∀ k, Bk n k)

theorem phi_X_chart (k : Fin (m + 1)) : phi i c (MvPolynomial.X ⟨k, c k⟩) = 1 := by
  have h : dehomog c (MvPolynomial.X ⟨k, c k⟩ : Pol n) = 1 := by
    simp [dehomog, pullRatio_self]
  simp [phi, h]

theorem ptCoord_chart_ne_zero (x : MP ℤ m n) (hx : x ∈ mchart c) (k : Fin (m + 1)) : ptCoord x ⟨k, c k⟩ ≠ 0 := by
  intro h0
  have h1 := FnForm.ptCoord_eq_mul_chartCoord c x hx ⟨k, ptChart x k⟩
  have h2 : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
    simp [ptCoord, pullRatio_self]
  simp [h0, h2] at h1

theorem mem_ptIdeal_iff_evaluation {x : MP ℤ m n} (hx : x ∈ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ}
    (hs : IsMultiHomog s a) :
    s ∈ ptIdeal x ↔ ((MP ℤ m n).evaluation (mchart c) x hx).hom (dehomog c s) = 0 := by
  rw [mem_ptIdeal_iff_aeval_ptCoord m n x s a hs, FnForm.aeval_ptCoord_eq_mul c x hx hs, mul_eq_zero]
  refine or_iff_right ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (ptCoord_chart_ne_zero c x hx k)

theorem mem_ptIdeal_iff_evaluation_phi {z : X} (hz : z ∈ i ⁻¹ᵁ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ}
    (hs : IsMultiHomog s a) :
    s ∈ ptIdeal (i z) ↔ (X.evaluation (i ⁻¹ᵁ mchart c) z hz).hom (phi i c s) = 0 := by
  rw [mem_ptIdeal_iff_evaluation c (x := i z) hz hs]
  have e := Scheme.evaluation_naturality_apply i z (show i z ∈ mchart c from hz) (dehomog c s)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine Eq.trans e.symm ?_
    rw [h, map_zero]
  · apply (i.residueFieldMap z).hom.injective
    rw [map_zero]
    exact e.trans h

variable [IsClosedImmersion i]

theorem isAffineOpen_preimage : IsAffineOpen (i ⁻¹ᵁ mchart c) := (Holo.affine_surj c).1.preimage i

theorem phi_surjective : Function.Surjective (phi i c) := fun a => by
  obtain ⟨b, rfl⟩ := i.app_surjective (mchart c) (Holo.affine_surj c).1 a
  obtain ⟨P, rfl⟩ := (Holo.affine_surj c).2 b
  exact ⟨P, rfl⟩

end Chart

section Cone

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.OrbitChartMult

variable {D : Type} [CommRing D] (ε : Pol n →+* D)

def cone : Pol n →+* MvPolynomial (Fin (m + 1)) D :=
  eval₂Hom (Int.castRingHom _) fun p => C (ε (MvPolynomial.X p)) * MvPolynomial.X p.1

theorem cone_of_isMultiHomog {F : Pol n} {d : Fin (m + 1) → ℕ} (hF : IsMultiHomog F d) :
    cone ε F = C (ε F) * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hX : ∏ p : Σ k, Bk n k, (MvPolynomial.X p.1 : MvPolynomial (Fin (m + 1)) D) ^ μ p =
      ∏ k, MvPolynomial.X k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial (Fin (m + 1)) D) ^ μ ⟨k, i⟩ = _
    rw [← hF μ hμ k, Finset.prod_pow_eq_pow_sum]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_prod, map_pow, cone, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, mul_pow,
    Finset.prod_mul_distrib, hX, eq_intCast, map_intCast]
  ring

theorem exists_isMultiHomog_eq (c : ∀ k, Bk n k) (hc : ∀ k, ε (MvPolynomial.X ⟨k, c k⟩) = 1) (t : Pol n) :
    ∃ (d : Fin (m + 1) → ℕ) (t' : Pol n), IsMultiHomog t' d ∧ ε t' = ε t := by
  have hm : ∀ d : Fin (m + 1) → ℕ, ε (chartMonomial c d) = 1 := fun d => by
    simp [chartMonomial, map_prod, hc]
  induction t using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, ?_, rfl⟩
    intro μ hμ k
    have : μ = 0 := by
      by_contra h
      exact (mem_support_iff.1 hμ) (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [this]
  | add p q hp hq =>
    obtain ⟨d₁, p', h₁, e₁⟩ := hp
    obtain ⟨d₂, q', h₂, e₂⟩ := hq
    refine ⟨d₁ + d₂, p' * chartMonomial c d₂ + q' * chartMonomial c d₁, ?_, ?_⟩
    · rw [geoMultiHomog_iff] at h₁ h₂ ⊢
      refine IsWeightedHomogeneous.add (h₁.mul (isWeightedHomogeneous_chartMonomial c d₂)) ?_
      have h := h₂.mul (isWeightedHomogeneous_chartMonomial c d₁)
      rwa [add_comm d₂ d₁] at h
    · simp [hm, e₁, e₂]
  | mul_X p v hp =>
    obtain ⟨d, p', h, e⟩ := hp
    refine ⟨d + coordDeg n v, p' * MvPolynomial.X v, ?_, by simp [e]⟩
    rw [geoMultiHomog_iff] at h ⊢
    exact h.mul (isWeightedHomogeneous_X _ _ _)

theorem cone_eq_zero_iff {P : Ideal (Pol n)} (hh : IsMultiHomogIdeal P)
    (hP : ∀ (s : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog s a → (s ∈ P ↔ ε s = 0)) (F : Pol n) :
    cone ε F = 0 ↔ F ∈ P := by
  classical
  have hfin := weightedHomogeneousComponent_finsupp (w := coordDeg n) F
  set S := hfin.toFinset
  have hsum : F = ∑ e ∈ S, weightedHomogeneousComponent (coordDeg n) e F := by
    conv_lhs => rw [← sum_weightedHomogeneousComponent (w := coordDeg n) F, finsum_eq_sum _ hfin]
  have hcomp : ∀ e, IsMultiHomog (weightedHomogeneousComponent (coordDeg n) e F) e := fun e =>
    (geoMultiHomog_iff _ _).2 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  have hcone : cone ε F = ∑ e ∈ S, C (ε (weightedHomogeneousComponent (coordDeg n) e F)) *
      ∏ k, MvPolynomial.X k ^ e k := by
    conv_lhs => rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun e _ => cone_of_isMultiHomog ε (hcomp e)
  constructor
  · intro h0
    rw [hsum]
    refine Ideal.sum_mem _ fun e he => (hP _ e (hcomp e)).2 ?_
    have := coeff_sum_C_mul_prod_X_pow S (fun e => ε (weightedHomogeneousComponent (coordDeg n) e F)) he
    rw [← hcone, h0, coeff_zero] at this
    exact this.symm
  · intro hF
    rw [hcone]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [(hP _ e (hcomp e)).1 (weightedHomogeneousComponent_mem_of_isMultiHomogIdeal hh hF e), C_0, zero_mul]

end Cone

section Ord

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.OrbitChartMult

variable [IsClosedImmersion i] (c : ∀ k, Bk n k)

abbrev qOf {z : X} (hz : z ∈ i ⁻¹ᵁ mchart c) : Ideal Γ(X, i ⁻¹ᵁ mchart c) :=
  ((isAffineOpen_preimage c).primeIdealOf ⟨z, hz⟩).asIdeal

theorem mem_ptIdeal_iff_mem_qOf {z : X} (hz : z ∈ i ⁻¹ᵁ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ}
    (hs : IsMultiHomog s a) : s ∈ ptIdeal (i z) ↔ phi i c s ∈ qOf c hz :=
  (mem_ptIdeal_iff_evaluation_phi c hz hs).trans
    (ReciprocityTheory.AnForm.R.evaluation_eq_zero_iff_mem_primeIdealOf _ z hz _)

theorem map_ptIdeal_eq {z : X} (hz : z ∈ i ⁻¹ᵁ mchart c) : (ptIdeal (i z)).map (phi i c) = qOf c hz := by
  refine le_antisymm ?_ fun y hy => ?_
  · rw [Ideal.map_le_iff_le_comap]
    obtain ⟨S, hS, e⟩ := (isMultiProjPrime_ptIdeal m n (i z)).2.1
    have hmem : ∀ f ∈ S, f ∈ ptIdeal (i z) := fun f hf => e ▸ Ideal.subset_span hf
    rw [e, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact (mem_ptIdeal_iff_mem_qOf c hz ha).1 (hmem f hf)
  · obtain ⟨t, rfl⟩ := phi_surjective c y
    obtain ⟨d, t', ht, e⟩ := exists_isMultiHomog_eq (phi i c) c (phi_X_chart c) t
    rw [← e] at hy ⊢
    exact Ideal.mem_map_of_mem _ ((mem_ptIdeal_iff_mem_qOf c hz ht).2 hy)

theorem mem_genericPoint_iff (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ}
    (hs : IsMultiHomog s a) : s ∈ ptIdeal (i (genericPoint X)) ↔ phi i c s = 0 :=
  (mem_ptIdeal_iff_evaluation_phi c hc hs).trans
    (map_eq_zero_iff _ (UnderIdeal.evaluation_genericPoint_injective _ hc))

theorem localQuotLength_congr {O : Type} [CommRing O] {q q' : Ideal O} [q.IsPrime] [q'.IsPrime] (e : q = q') (f : O) :
    localQuotLength q f = localQuotLength q' f := by
  subst e
  rfl

theorem multAt_eq {z : X} (hz : z ∈ i ⁻¹ᵁ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ} (hs : IsMultiHomog s a) :
    multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}) (ptIdeal (i z)) =
      localQuotLength (qOf c hz) (phi i c s) := by
  have hη : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem hz
  have hV := isMultiProjPrime_ptIdeal m n (i z)
  have : (ptIdeal (i z)).IsPrime := hV.1
  have e := map_ptIdeal_eq c hz
  have : ((ptIdeal (i z)).map (phi i c)).IsPrime := e ▸ inferInstance
  have hXV : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : Pol n) ∉ ptIdeal (i z) := fun k h => by
    have h1 := (mem_ptIdeal_iff_mem_qOf c hz ((geoMultiHomog_iff _ _).2
      (isWeightedHomogeneous_X ℤ (coordDeg n) ⟨k, c k⟩))).1 h
    rw [phi_X_chart] at h1
    exact (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top inferInstance) h1
  haveI : Nonempty (i ⁻¹ᵁ mchart c) := ⟨⟨z, hz⟩⟩
  have key := multAt_eq_localQuotLength_of (phi i c) (cone (phi i c))
    (fun hF => cone_of_isMultiHomog _ ((geoMultiHomog_iff _ _).2 hF)) (ptIdeal (i z)) (phi_surjective c)
    (ptIdeal (i (genericPoint X)))
    (cone_eq_zero_iff _ (isMultiProjPrime_ptIdeal m n _).2.1 fun s a hs => mem_genericPoint_iff c hη hs)
    (fun v hv e => weightedHomogeneousComponent_mem_of_isMultiHomogIdeal hV.2.1 hv e)
    (fun hF hm => (mem_ptIdeal_iff_mem_qOf c hz ((geoMultiHomog_iff _ _).2 hF)).2 (e ▸ hm))
    c (phi_X_chart c) hXV ((geoMultiHomog_iff s a).1 hs)
  exact key.trans (localQuotLength_congr e _)

variable [IsLocallyNoetherian X]

theorem ord_fnAt {z : X} (h1 : Order.coheight z = 1) (hz : z ∈ i ⁻¹ᵁ mchart c)
    (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c) {s : Pol n} {a : Fin (m + 1) → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ ptIdeal (i (genericPoint X))) :
    Scheme.ord (fnAt i c hc s) z = multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}) (ptIdeal (i z)) := by
  rw [multAt_eq c hz hs]
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : i ⁻¹ᵁ mchart c)
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (qOf c hz) :=
    (isAffineOpen_preimage c).isLocalization_stalk ⟨z, hz⟩
  have e1 : fnAt i c hc s = algebraMap (X.presheaf.stalk z) X.functionField
      (X.presheaf.germ _ z hz (phi i c s)) := (algebraMap_germ hz _).symm
  have ha : X.presheaf.germ _ z hz (phi i c s) ≠ 0 := fun h =>
    FnForm.fnAt_ne_zero_of_notMem_ptIdeal m n X i c hc s a hs hsP (by rw [e1, h, map_zero])
  rw [e1, ord_algebraMap h1 ha, localQuotLength]
  let e := IsLocalization.algEquiv (qOf c hz).primeCompl (Localization.AtPrime (qOf c hz)) (X.presheaf.stalk z)
  have h2 := OrderNorm.length_quot_ringEquiv e.toRingEquiv (algebraMap _ (Localization.AtPrime (qOf c hz)) (phi i c s))
  have h3 : e.toRingEquiv (algebraMap _ (Localization.AtPrime (qOf c hz)) (phi i c s)) =
      X.presheaf.germ _ z hz (phi i c s) := e.commutes _
  rw [h2, h3]

end Ord

section Mult

variable [IsClosedImmersion i] [IsLocallyNoetherian X]

theorem ord_fnOf_of_isUnit {U : X.Opens} {z : X} (hz : z ∈ U) (h : genericPoint X ∈ U) {v : Γ(X, U)} (hv : IsUnit v) :
    Scheme.ord (fnOf U h v) z = 0 :=
  UnitAt.ord_eq_zero ⟨X.presheaf.germ U z hz v, hv.map _, algebraMap_germ hz _⟩

theorem mult_eq {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} {r : (M.restr i).B.ι → X.functionFieldˣ}
    (hr : IsRatSec (M.restr i).B r) {f g : Pol n} (hf : ∀ c (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c), fnAt i c hc f ≠ 0)
    (hg : ∀ c (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c), fnAt i c hc g ≠ 0) (hRat : RatOf M A r f g) (z : X) :
    ∃ (c : ∀ k, Bk n k) (hz : z ∈ i ⁻¹ᵁ mchart c) (hc : genericPoint X ∈ i ⁻¹ᵁ mchart c),
      ((M.restr i).div hr).mult z = Scheme.ord (fnAt i c hc f) z - Scheme.ord (fnAt i c hc g) z := by
  obtain ⟨u, -, hu⟩ := hRat
  obtain ⟨b, hb⟩ := exists_chart M.isLB (i z)
  let c : ∀ k, Bk n k := fun k => ptChart (i z) k
  have hz : z ∈ i ⁻¹ᵁ mchart c := Set.mem_iInter.2 fun k => mem_ptChart (i z) k
  have hzb : z ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := ⟨hb, hz⟩
  have hc : genericPoint X ∈ i ⁻¹ᵁ mchart c := gen_mem hz
  have hη : genericPoint X ∈ i ⁻¹ᵁ (M.B.U b ⊓ mchart c) := gen_mem hzb
  refine ⟨c, hz, hc, ?_⟩
  have e := hu b c hc hη
  have hm : ((M.restr i).div hr).mult z = Scheme.ord ((r fun _ => b : X.functionFieldˣ) : X.functionField) z :=
    ((presents_divOfRatSec _ hr).isEqn (fun _ => b) z (Set.mem_iInter.2 fun _ => hb)).mult_eq
  have hv : IsUnit (i.app _ (u b c).val : Γ(X, i ⁻¹ᵁ (M.B.U b ⊓ mchart c))) := (u b c).isUnit.map (i.app _).hom
  have hv0 : fnOf _ hη (i.app _ (u b c).val) ≠ 0 := (hv.map (fnOf _ hη)).ne_zero
  rw [hm, ← e, Scheme.ord_mul (mul_ne_zero hv0 (Units.ne_zero _)) (hg c hc),
    Scheme.ord_mul hv0 (Units.ne_zero _), ord_fnOf_of_isUnit hzb hη hv]
  ring

end Mult

section Sum

open Classical in

def oS (i : X ⟶ MP ℤ m n) (s : Pol n) (z : X) : ℝ :=
  if Order.coheight z = 1 then (multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}) (ptIdeal (i z)) : ℝ) else 0

variable [IsClosedImmersion i]

theorem sum_divSupp {s : Pol n} {a : Fin (m + 1) → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ ptIdeal (i (genericPoint X))) (u : Ideal (Pol n) → ℝ) :
    (Function.support fun z : X => oS i s z * u (ptIdeal (i z))).Finite ∧
    ∑ᶠ W ∈ divSupp (ptIdeal (i (genericPoint X))) s,
        (multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}) W : ℝ) * u W =
      ∑ᶠ z : X, oS i s z * u (ptIdeal (i z)) := by
  let T : Set X := {z | Order.coheight z = 1 ∧ s ∈ ptIdeal (i z)}
  have hbij : Set.BijOn (fun z : X => ptIdeal (i z)) T (divSupp (ptIdeal (i (genericPoint X))) s) := by
    refine ⟨fun z hz => mem_divSupp_of_coheight_eq_one hs hsP hz.1 hz.2, ptIdeal_injective.injOn, fun W hW => ?_⟩
    obtain ⟨z, h1, rfl⟩ := exists_point_of_mem_divSupp hs hsP hW
    exact ⟨z, ⟨h1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩, rfl⟩
  have hsupp : (Function.support fun z : X => oS i s z * u (ptIdeal (i z))) ⊆ T := fun z hz => by
    by_contra hT
    refine hz ?_
    by_cases h1 : Order.coheight z = 1
    · have hn : s ∉ ptIdeal (i z) := fun h => hT ⟨h1, h⟩
      have hp := (isMultiProjPrime_ptIdeal m n (i z)).1
      have h0 : multAt (ptIdeal (i (genericPoint X)) ⊔ Ideal.span {s}) (ptIdeal (i z)) = 0 :=
        GroundTheory.Heights₂.Heights.Inter.DiagonalOrder.multAt_eq_zero_of_not_le hp fun hle =>
          hn (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
      simp [oS, h1, h0]
    · simp [oS, h1]
  have hT : T.Finite := Set.Finite.of_finite_image
    (hbij.image_eq ▸ Geo.divSupp_finite _ _) hbij.injOn
  refine ⟨hT.subset hsupp, ?_⟩
  have e1 : ∑ᶠ z : X, oS i s z * u (ptIdeal (i z)) = ∑ᶠ z ∈ T, oS i s z * u (ptIdeal (i z)) := by
    rw [← finsum_mem_univ]
    refine finsum_mem_inter_support_eq _ _ _ ?_
    rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
  rw [e1]
  refine (finsum_mem_eq_of_bijOn _ hbij fun z hz => ?_).symm
  simp [oS, hz.1]

end Sum

theorem cycleOfRat : CycleOfRat := by
  intro m n M A _ X _ _ i _ D _ r hr f g hfg hrat u
  obtain ⟨α, β, hf, hg, hfP, hgP, -⟩ := hfg
  have hmult : ∀ z : X, (((M.restr i).div hr).mult z : ℝ) = oS i f z - oS i g z := fun z => by
    obtain ⟨c, hz, hc, e⟩ := mult_eq (i := i) hr
      (fun c hc => FnForm.fnAt_ne_zero_of_notMem_ptIdeal m n X i c hc f α hf hfP)
      (fun c hc => FnForm.fnAt_ne_zero_of_notMem_ptIdeal m n X i c hc g β hg hgP) hrat z
    by_cases h1 : Order.coheight z = 1
    · rw [e, ord_fnAt c h1 hz hc hf hfP, ord_fnAt c h1 hz hc hg hgP]
      simp [oS, h1]
    · rw [e, Scheme.ord_eq_zero_of_coheight_neq_one h1, Scheme.ord_eq_zero_of_coheight_neq_one h1]
      simp [oS, h1]
  obtain ⟨Ff, ef⟩ := sum_divSupp (i := i) hf hfP u
  obtain ⟨Fg, eg⟩ := sum_divSupp (i := i) hg hgP u
  rw [ef, eg, ← finsum_sub_distrib Ff Fg]
  exact finsum_congr fun z => by rw [hmult, sub_mul]

end GlobalTheory.CompanionTheory.MixZ.CycleRat
