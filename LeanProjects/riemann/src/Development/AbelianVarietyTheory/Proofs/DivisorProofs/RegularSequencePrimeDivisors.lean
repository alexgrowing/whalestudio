import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ClosureFromSpecMemCompsH
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.RegParPrime

open ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages

theorem exists_mul_eq_of_mem_span {A : Type} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
    (R : Type) [CommRing R] [Algebra A R] [IsLocalization.AtPrime R p] {b x : A}
    (h : algebraMap A R x ∈ Ideal.span {algebraMap A R b}) : ∃ t ∉ p, ∃ s, t * x = s * b := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl (S := R) r
  refine ⟨t, t.2, s, ?_⟩
  apply IsLocalization.injective R (M := p.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors p)
  rw [map_mul, map_mul, ← hr, ← mul_assoc, IsLocalization.mk'_spec']

theorem exists_primeDivisors_of_regularParams : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) (U : Y.Opens) (hy : y ∈ U) (c : ℕ) (a : Fin c → Γ(Y, U)), IsRegularLocalRing (Y.presheaf.stalk y) → FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ U y hy (a i)) → ∃ (w : Fin c → Y) (u : Fin c → Y.functionFieldˣ), Function.Injective w ∧ ∀ j, (u j : Y.functionField) = fnOf U (gen_mem hy) (a j) ∧ w j ⤳ y ∧ Order.coheight (w j) = 1 ∧ w j ∉ Y.basicOpen (a j) ∧ Scheme.ord (u j : Y.functionField) (w j) = 1 ∧ ∀ v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → v ∈ Y.basicOpen (a j) := by
  intro Y _ _ y U hy c a hreg hrsp
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  have hVU' : V ≤ U := hVU
  let b : Fin c → Γ(Y, V) := fun i => resG Y hVU' (a i)
  have hgerm : ∀ i, Y.presheaf.germ V y hyV (b i) = Y.presheaf.germ U y hy (a i) := fun i =>
    Y.presheaf.germ_res_apply (homOfLE hVU') y hyV (a i)
  have hrsp' : FinalTheorems.Rsp (Y.presheaf.stalk y) c (fun i => Y.presheaf.germ V y hyV (b i)) := by
    simpa only [hgerm] using hrsp
  haveI := hreg
  obtain ⟨q, hq⟩ := exists_parPrimes hV hyV b hrsp'
  have hprime : ∀ i, Prime (Y.presheaf.germ V y hyV (b i)) :=
    prime_of_regular_params _ hrsp'.1 hrsp'.2
  haveI : Nonempty V := ⟨⟨y, hyV⟩⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hb0 : ∀ i, b i ≠ 0 := fun i h => (hprime i).ne_zero (by rw [h, map_zero])
  have hfn : ∀ i, fnOf U (gen_mem hy) (a i) = fnOf V (gen_mem hyV) (b i) := fun i =>
    (fnOf_resG hVU' (gen_mem hyV) (a i)).symm
  have ha0 : ∀ i, fnOf U (gen_mem hy) (a i) ≠ 0 := fun i h =>
    hb0 i (fnOf_injective V (gen_mem hyV) (by rw [← hfn, h, map_zero]))
  have hbas : ∀ i, Y.basicOpen (b i) ≤ Y.basicOpen (a i) := fun i => by
    have := Scheme.basicOpen_res Y (a i) (homOfLE hVU').op
    intro z hz
    have hz' : z ∈ V ⊓ Y.basicOpen (a i) := by rw [← this]; exact hz
    exact hz'.2

  have hq1 : ∀ j, (q j).asIdeal.height = 1 := by
    intro j
    have hmin : (q j).asIdeal ∈ (Ideal.span {b j}).minimalPrimes := by
      refine ⟨⟨(q j).2, (Ideal.span_singleton_le_iff_mem _).2 (hq.2.1 j)⟩, ?_⟩
      rintro Q ⟨hQp, hQb⟩ hQle
      exact (hq.2.2.1 j ⟨Q, hQp⟩ (le_trans (show (⟨Q, hQp⟩ : PrimeSpectrum Γ(Y, V)) ≤ q j from hQle)
        (hq.1 j))).mp (hQb (Ideal.mem_span_singleton_self _))
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin) ?_
    refine ENat.one_le_iff_ne_zero.2 fun h0 => hb0 j ?_
    have hmin0 := Ideal.height_eq_zero_iff.1 h0
    have hbot : (q j).asIdeal ≤ ⊥ := hmin0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact hbot (hq.2.1 j)
  let w : Fin c → Y := fun j => hV.fromSpec (q j)
  have hwV : ∀ j, w j ∈ V := fun j => fromSpec_mem hV (q j)
  have hpw : ∀ j, hV.primeIdealOf ⟨w j, hwV j⟩ = q j := fun j => pOf_fromSpec hV (q j)
  have hcoh : ∀ j, Order.coheight (w j) = 1 := by
    intro j
    letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI := hV.isLocalization_stalk ⟨w j, hwV j⟩
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨w j, hwV j⟩).asIdeal
      (Y.presheaf.stalk (w j))
    rw [ringKrullDim_stalk_eq_coheight, hpw, hq1] at this
    exact_mod_cast this
  refine ⟨w, fun j => Units.mk0 _ (ha0 j), ?_, fun j => ?_⟩
  · intro i j h
    have key : ∀ {z z' : Y} (hz : z ∈ V) (hz' : z' ∈ V), z = z' →
        hV.primeIdealOf ⟨z, hz⟩ = hV.primeIdealOf ⟨z', hz'⟩ := by
      rintro z z' hz hz' rfl
      rfl
    have h2 : q i = q j := (hpw i).symm.trans ((key (hwV i) (hwV j) h).trans (hpw j))
    exact (hq.2.2.2 i j (h2 ▸ hq.2.1 j)).symm
  have hwb : w j ∉ Y.basicOpen (b j) := by
    intro h'
    have h1 : q j ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := h'
    rw [hV.fromSpec_preimage_basicOpen] at h1
    exact h1 (hq.2.1 j)
  refine ⟨rfl, fromSpec_specializes hq j, hcoh j, ?_, ?_, ?_⟩
  · intro h'
    exact hwb ((Y.basicOpen_res (a j) (homOfLE hVU').op).symm ▸ ⟨hwV j, h'⟩ : w j ∈ Y.basicOpen (b j))
  · letI := Y.presheaf.algebra_section_stalk (⟨w j, hwV j⟩ : V)
    haveI hloc0 := hV.isLocalization_stalk ⟨w j, hwV j⟩
    haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk (w j)) (q j).asIdeal := by
      rw [← hpw j]; exact hloc0
    have hgalg : Y.presheaf.germ V (w j) (hwV j) (b j) = algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := rfl
    have hg0 : Y.presheaf.germ V (w j) (hwV j) (b j) ≠ 0 := fun h0 =>
      ha0 j (by rw [hfn, ← algebraMap_germ (hwV j), h0, map_zero])
    have hmax : Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)} =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (w j)) := by
      refine le_antisymm ?_ ?_
      · rw [Ideal.span_singleton_le_iff_mem,
          ← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)), hgalg]
        exact Ideal.mem_map_of_mem _ (hq.2.1 j)
      · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (q j).asIdeal (Y.presheaf.stalk (w j)),
          Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap]
        letI := Y.presheaf.algebra_section_stalk (⟨y, hyV⟩ : V)
        haveI := hV.isLocalization_stalk ⟨y, hyV⟩
        haveI : (Ideal.span {Y.presheaf.germ V y hyV (b j)}).IsPrime :=
          (Ideal.span_singleton_prime (hprime j).ne_zero).2 (hprime j)
        let P : Ideal Γ(Y, V) := Ideal.comap (algebraMap Γ(Y, V) (Y.presheaf.stalk y))
          (Ideal.span {Y.presheaf.germ V y hyV (b j)})
        have hPp : P.IsPrime := Ideal.IsPrime.comap _
        have hPle : P ≤ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal := by
          intro z hz
          have hz' : algebraMap Γ(Y, V) (Y.presheaf.stalk y) z ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) :=
            (Ideal.span_singleton_le_iff_mem _).2
              ((IsLocalRing.mem_maximalIdeal _).2 (hprime j).not_unit) hz
          rw [← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y)
            (hV.primeIdealOf ⟨y, hyV⟩).asIdeal]
          exact hz'
        have hbP : b j ∈ P := Ideal.mem_span_singleton_self _
        have hqP : q j ≤ ⟨P, hPp⟩ := (hq.2.2.1 j ⟨P, hPp⟩ hPle).mp hbP
        obtain ⟨t, ht, s, hts⟩ := exists_mul_eq_of_mem_span (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
          (Y.presheaf.stalk y) (hqP hx)
        have htq : t ∉ (q j).asIdeal := fun h => ht (hq.1 j h)
        have hu : IsUnit (algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t) :=
          IsLocalization.map_units (Y.presheaf.stalk (w j)) (⟨t, htq⟩ : (q j).asIdeal.primeCompl)
        have e : algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) t * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) x =
            algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) (b j) := by
          rw [← map_mul, ← map_mul, hts]
        refine Ideal.mem_span_singleton'.2 ⟨↑hu.unit⁻¹ * algebraMap Γ(Y, V) (Y.presheaf.stalk (w j)) s, ?_⟩
        rw [hgalg, mul_assoc, ← e, ← mul_assoc, hu.val_inv_mul, one_mul]
    have hlen : Module.length (Y.presheaf.stalk (w j))
        (Y.presheaf.stalk (w j) ⧸ Ideal.span {Y.presheaf.germ V (w j) (hwV j) (b j)}) = 1 := by
      rw [hmax, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal _)
    show Scheme.ord (fnOf U (gen_mem hy) (a j)) (w j) = 1
    rw [hfn, ← algebraMap_germ (hwV j), GlobalTheory.Cartier.ord_algebraMap (hcoh j) hg0, hlen]
    rfl
  · intro v hvy hv1 hvw
    by_contra hva
    have hvV : v ∈ V := hvy.mem_open V.isOpen hyV
    have hbQ : b j ∈ (hV.primeIdealOf ⟨v, hvV⟩).asIdeal := by
      by_contra hn
      apply hva
      have h1 : hV.primeIdealOf ⟨v, hvV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen (b j) := by
        rw [hV.fromSpec_preimage_basicOpen]; exact hn
      have h3 : hV.fromSpec (hV.primeIdealOf ⟨v, hvV⟩) ∈ Y.basicOpen (b j) := h1
      rw [hV.fromSpec_primeIdealOf] at h3
      exact hbas j h3
    have hle : q j ≤ hV.primeIdealOf ⟨v, hvV⟩ :=
      (hq.2.2.1 j _ ((specializes_iff_pOf hV hvV hyV).mp hvy)).mp hbQ
    have hQv1 : (hV.primeIdealOf ⟨v, hvV⟩).asIdeal.height = 1 := by
      letI := Y.presheaf.algebra_section_stalk (⟨v, hvV⟩ : V)
      haveI := hV.isLocalization_stalk ⟨v, hvV⟩
      have := IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨v, hvV⟩).asIdeal
        (Y.presheaf.stalk v)
      rw [ringKrullDim_stalk_eq_coheight, hv1] at this
      exact_mod_cast this.symm
    have heq : q j = hV.primeIdealOf ⟨v, hvV⟩ := by
      by_contra hne
      haveI : (q j).asIdeal.FiniteHeight :=
        (q j).asIdeal.finiteHeight_iff.mpr (Or.inr (by rw [hq1 j]; exact ENat.one_ne_top))
      have hlt : (q j).asIdeal < (hV.primeIdealOf ⟨v, hvV⟩).asIdeal :=
        lt_of_le_of_ne hle (fun h => hne (PrimeSpectrum.ext h))
      have := Ideal.height_strict_mono_of_isPrime hlt
      rw [hq1 j, hQv1] at this
      exact lt_irrefl _ this
    exact hvw (eq_of_pOf_eq hV hvV (hwV j) (by rw [hpw j]; exact heq.symm))

end GlobalTheory.RegParPrime
