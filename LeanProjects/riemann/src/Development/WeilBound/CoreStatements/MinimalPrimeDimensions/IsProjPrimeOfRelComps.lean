import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemMinimalPrimesIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField IsDedekindDomain
open GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.M

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

local notation "φ" => (MvPolynomial.map (algebraMap (𝓞 K) K) : MvPolynomial (Fin m) (𝓞 K) →+* MvPolynomial (Fin m) K)
local notation "CC" => (C : 𝓞 K →+* MvPolynomial (Fin m) (𝓞 K))

theorem disjoint_of_bot {W : Ideal (MvPolynomial (Fin m) (𝓞 K))} (h : W.comap CC = ⊥) :
    Disjoint (((nonZeroDivisors (𝓞 K)).map CC : Submonoid _) : Set (MvPolynomial (Fin m) (𝓞 K))) W := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ hW
  exact nonZeroDivisors.ne_zero ha (Ideal.mem_bot.1 (h ▸ (show a ∈ W.comap CC from hW)))

theorem comap_map {W : Ideal (MvPolynomial (Fin m) (𝓞 K))} (hW : W.IsPrime) (h : W.comap CC = ⊥) :
    (W.map φ).comap φ = W :=
  IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors (𝓞 K)).map CC) (MvPolynomial (Fin m) K) hW
    (disjoint_of_bot h)

theorem isPrime_map {W : Ideal (MvPolynomial (Fin m) (𝓞 K))} (hW : W.IsPrime) (h : W.comap CC = ⊥) :
    (W.map φ).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors (𝓞 K)).map CC) (MvPolynomial (Fin m) K) W hW
    (disjoint_of_bot h)

theorem map_comap (W : Ideal (MvPolynomial (Fin m) K)) : (W.comap φ).map φ = W :=
  IsLocalization.map_under ((nonZeroDivisors (𝓞 K)).map CC) (MvPolynomial (Fin m) K) W

theorem comap_bot {W : Ideal (MvPolynomial (Fin m) K)} (hW : W ≠ ⊤) : (W.comap φ).comap CC = ⊥ := by
  refine le_bot_iff.1 fun a ha => ?_
  by_contra h0
  rw [Ideal.mem_comap, Ideal.mem_comap, map_C] at ha
  exact hW (W.eq_top_of_isUnit_mem ha ((IsUnit.mk0 _ (by simpa using h0)).map C))

theorem map_linForm (u : Fin m → 𝓞 K) : φ (linForm u) = linForm fun j => (u j : K) := by
  simp [linForm]

theorem isProjPrime_map {W : Ideal (MvPolynomial (Fin m) (𝓞 K))} (hW : IsProjPrime W) (h : W.comap CC = ⊥) :
    IsProjPrime (W.map φ) := by
  refine ⟨isPrime_map hW.isPrime h, ?_, (isRelevant_comap_map_iff _ _).1 ((comap_map hW.isPrime h).symm ▸ hW.isRelevant)⟩
  intro f hf d
  refine Submodule.span_induction (p := fun f _ => ∀ d, homogeneousComponent d f ∈ W.map φ) ?_ (by simp)
    (fun a b _ _ ha hb d => by rw [map_add]; exact Ideal.add_mem _ (ha d) (hb d)) ?_ hf d
  · rintro _ ⟨g, hg, rfl⟩ d
    have e : homogeneousComponent d (φ g) = φ (homogeneousComponent d g) := by
      ext n
      rw [coeff_homogeneousComponent, coeff_map, coeff_map, coeff_homogeneousComponent]
      split_ifs <;> simp
    rw [e]
    exact Ideal.mem_map_of_mem _ (hW.isHomog g hg d)
  · intro a b _ hb d
    rw [smul_eq_mul, ← b.sum_homogeneousComponent, ← a.sum_homogeneousComponent, Finset.sum_mul_sum, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous i a).mul
      (homogeneousComponent_isHomogeneous j b))]
    split_ifs
    · exact Ideal.mul_mem_left _ _ (hb j)
    · exact Ideal.zero_mem _

theorem isProjPrime_of_relComps {R : Type} [CommRing R] {J W : Ideal (MvPolynomial (Fin m) R)} (hJ : IsHomogIdeal J)
    (hW : W ∈ relComps J) : IsProjPrime W := by
  have := hW.1.1.1
  obtain ⟨W', h1, h2, h3, h4⟩ := A.exists_core W
  have e : W' = W := le_antisymm h3 (hW.1.2 ⟨h1, fun g hg => h4 g fun d => hW.1.1.2 (hJ g hg d)⟩ h3)
  exact ⟨this, e ▸ h2, hW.2⟩

theorem mem_relComps_map {J : Ideal (MvPolynomial (Fin m) (𝓞 K))} {W : Ideal (MvPolynomial (Fin m) K)} :
    W ∈ relComps (J.map φ) ↔ W.comap φ ∈ relComps J := by
  have h := IsLocalization.minimalPrimes_map ((nonZeroDivisors (𝓞 K)).map CC) (MvPolynomial (Fin m) K) J
  exact and_congr (Set.ext_iff.1 h W) (isRelevant_comap_map_iff _ _).symm

theorem localMult_map' (J : Ideal (MvPolynomial (Fin m) (𝓞 K))) (W : Ideal (MvPolynomial (Fin m) K)) [hW : W.IsPrime] :
    localMult (J.map φ) W = localMult J (W.comap φ) := by
  refine A.localMult_map φ W J (fun b => ?_) ?_
  · obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj ((nonZeroDivisors (𝓞 K)).map CC) b
    exact ⟨a, s, fun h => hW.ne_top (W.eq_top_of_isUnit_mem h
      (IsLocalization.map_units (MvPolynomial (Fin m) K) s)), e⟩
  · rw [(RingHom.injective_iff_ker_eq_bot _).1 (map_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K))]
    exact bot_le

variable {P : Ideal (MvPolynomial (Fin m) (𝓞 K))} {u : Fin m → 𝓞 K} {ι : Type} {S : Finset ι}
  {Pt : ι → Ideal (MvPolynomial (Fin m) (𝓞 K))} {μ : ι → ℤ}

open Classical in
theorem vertTerm_eq (hP : P.IsPrime) (h0 : P.comap CC = ⊥) (hi : Function.Injective Pt)
    (hS : ∀ W, W ∈ relComps (P ⊔ Ideal.span {linForm u}) ↔ ∃ z ∈ S, Pt z = W)
    (hμ : ∀ z ∈ S, μ z = localMult (P ⊔ Ideal.span {linForm u}) (Pt z)) (k : ℕ) (g : ι → ℝ)
    (hg : ∀ z ∈ S, ∀ v : HeightOneSpectrum (𝓞 K), (Pt z).comap CC = v.asIdeal →
      g z = chowDegree (reduceMod v (Pt z)) k * Real.log (Ideal.absNorm v.asIdeal)) :
    vertTerm (P.map φ) k u = ∑ z ∈ S with (Pt z).comap CC ≠ ⊥, (μ z : ℝ) * g z := by
  have hI : integralModel (P.map φ) = P := comap_map hP h0
  have h1 (v : HeightOneSpectrum (𝓞 K)) : vertTermAt (P.map φ) k u v =
      ∑ z ∈ S, if (Pt z).comap CC = v.asIdeal then (μ z : ℝ) * g z else 0 := by
    have e : vertComps (P.map φ) u v = Pt '' (S.filter fun z => (Pt z).comap CC = v.asIdeal : Finset ι) := by
      ext W
      simp only [vertComps, hI, hS, Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter]
      exact ⟨fun ⟨⟨z, hz, e⟩, h⟩ => ⟨z, ⟨hz, e ▸ h⟩, e⟩, fun ⟨z, ⟨hz, h⟩, e⟩ => ⟨⟨z, hz, e⟩, e ▸ h⟩⟩
    rw [vertTermAt, e, finsum_mem_image hi.injOn, finsum_mem_coe_finset, ← Finset.sum_filter, hI]
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [Finset.mem_filter] at hz
    rw [hμ z hz.1, hg z hz.1 v hz.2, Int.cast_natCast, mul_assoc]
  rw [vertTerm, finsum_congr h1, finsum_sum_comm, Finset.sum_filter]
  · refine Finset.sum_congr rfl fun z hz => ?_
    have hp : (Pt z).IsPrime := ((hS _).2 ⟨z, hz, rfl⟩).1.1.1
    split_ifs with h
    · refine (finsum_eq_single _ ⟨(Pt z).comap CC, Ideal.comap_isPrime _ _, h⟩ fun v hv => if_neg fun e => hv ?_).trans
        (if_pos rfl)
      exact HeightOneSpectrum.ext e.symm
    · exact finsum_eq_zero_of_forall_eq_zero fun v => if_neg fun (e : (Pt z).comap CC = v.asIdeal) =>
        h fun e' => v.ne_bot (e.symm.trans e')
  · intro z _
    refine Set.Subsingleton.finite fun v hv w hw => HeightOneSpectrum.ext ?_
    have h1 : (Pt z).comap CC = v.asIdeal := by by_contra h; exact hv (if_neg h)
    have h2 : (Pt z).comap CC = w.asIdeal := by by_contra h; exact hw (if_neg h)
    exact h1.symm.trans h2

open Classical in
theorem divCycle_eq (hi : Function.Injective Pt)
    (hS : ∀ W, W ∈ relComps (P ⊔ Ideal.span {linForm u}) ↔ ∃ z ∈ S, Pt z = W)
    (hμ : ∀ z ∈ S, μ z = localMult (P ⊔ Ideal.span {linForm u}) (Pt z)) (hμ0 : ∀ z ∈ S, μ z ≠ 0) :
    (∀ z ∈ S, (Pt z).comap CC = ⊥ → (Pt z).map φ ∈ (divCycle (P.map φ) fun j => (u j : K)).support) ∧
    ∀ F : Ideal (MvPolynomial (Fin m) K) → ℝ,
      ∑ W ∈ (divCycle (P.map φ) fun j => (u j : K)).support, ((divCycle (P.map φ) fun j => (u j : K)) W : ℝ) * F W =
        ∑ z ∈ S with (Pt z).comap CC = ⊥, (μ z : ℝ) * F ((Pt z).map φ) := by
  have hJ : P.map φ ⊔ Ideal.span {linForm fun j => (u j : K)} = (P ⊔ Ideal.span {linForm u}).map φ := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_linForm]
  have hp (z) (hz : z ∈ S) : (Pt z).IsPrime := ((hS _).2 ⟨z, hz, rfl⟩).1.1.1
  have hval (z) (hz : z ∈ S) (h : (Pt z).comap CC = ⊥) :
      ((divCycle (P.map φ) fun j => (u j : K)) ((Pt z).map φ) : ℤ) = μ z := by
    have := isPrime_map (hp z hz) h
    rw [divCycle, hJ, fundCycle_apply, if_pos (mem_relComps_map.2 (by
      rw [comap_map (hp z hz) h]; exact (hS _).2 ⟨z, hz, rfl⟩)), localMult_map', comap_map (hp z hz) h, hμ z hz]
  have hmem (z) (hz : z ∈ S) (h : (Pt z).comap CC = ⊥) :
      (Pt z).map φ ∈ (divCycle (P.map φ) fun j => (u j : K)).support :=
    Finsupp.mem_support_iff.2 fun e => hμ0 z hz ((hval z hz h).symm.trans (by rw [e]; rfl))
  refine ⟨hmem, fun F => (Finset.sum_bij (fun z _ => (Pt z).map φ) (fun z hz => ?_) (fun z hz z' hz' e => ?_)
    (fun W hW => ?_) fun z hz => ?_).symm⟩
  · rw [Finset.mem_filter] at hz
    exact hmem z hz.1 hz.2
  · rw [Finset.mem_filter] at hz hz'
    exact hi ((comap_map (hp z hz.1) hz.2).symm.trans ((congrArg _ e).trans (comap_map (hp z' hz'.1) hz'.2)))
  · have h1 : W ∈ relComps ((P ⊔ Ideal.span {linForm u}).map φ) := by
      by_contra hn
      refine Finsupp.mem_support_iff.1 hW ?_
      rw [divCycle, hJ, fundCycle_apply, if_neg hn]
    obtain ⟨z, hz, e⟩ := (hS _).1 (mem_relComps_map.1 h1)
    exact ⟨z, Finset.mem_filter.2 ⟨hz, e ▸ comap_bot h1.1.1.1.ne_top⟩, by rw [e, map_comap]⟩
  · rw [Finset.mem_filter] at hz
    rw [← hval z hz.1 hz.2, Int.cast_natCast]

end ChowFormHeightComparison₂.CF.M
