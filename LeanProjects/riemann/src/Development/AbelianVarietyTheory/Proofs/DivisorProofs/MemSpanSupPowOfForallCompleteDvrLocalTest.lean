import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallCompleteDvrDominatingStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem dvd_of_forall_mem_span_sup_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {x y : V} (hx : x ≠ 0) (h : ∀ e, y ∈ Ideal.span {x} ⊔ maximalIdeal V ^ e) : x ∣ y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hs : Ideal.span {x} = maximalIdeal V ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hk
  have := h k
  rw [← hs, sup_idem] at this
  exact Ideal.mem_span_singleton.mp this

theorem mem_span_sup_pow_of_forall_complete_dvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (g : O) (b : ℕ → O), g ≠ 0 → (∀ m n, m ≤ n → b m - b n ∈ maximalIdeal O ^ m) → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ ρ : O →+* V, Function.Injective ρ → IsLocalHom ρ → ∀ e, ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e) → ∀ n, b n ∈ Ideal.span {g} ⊔ maximalIdeal O ^ n := by
  intro O _ _ _ _ _ _ g b hg hb hV n
  haveI : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  set m := maximalIdeal O with hm
  let R := AdicCompletion m O
  let ι : O →+* R := algebraMap O R
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O m
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  have fg : m.FG := m.fg_of_isNoetherianRing
  haveI : Module.Flat O R := AdicCompletion.flat_of_isNoetherian m
  haveI : IsLocalHom (algebraMap O R) := AdicCompletion.algebraMap_isLocalHom_of_fg fg
  haveI : Module.FaithfullyFlat O R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective ι := FaithfulSMul.algebraMap_injective O R
  haveI : CharZero R := charZero_of_injective_ringHom hinj
  have hmR : maximalIdeal R = m.map ι := AdicCompletion.maximalIdeal_eq_map

  have hc : IsAdicComplete (m.map ι) R := AdicCompletion.isAdicComplete_self m fg
  obtain ⟨F, hF⟩ := IsPrecomplete.prec hc.toIsPrecomplete (f := fun k => ι (b k)) (by
    intro k l hkl
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← map_sub, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hb k l hkl))
  have hF' : ∀ k, ι (b k) - F ∈ maximalIdeal R ^ k := by
    intro k
    have := hF k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← hmR] at this

  have hgR : ι g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hdvd : ι g ∣ F := by
    refine GlobalTheory.T.dvd_of_forall_complete_dvr_dominating R F (ι g) hgR ?_
    intro V _ _ _ hVc ρ' hρ' _
    let ρ : O →+* V := ρ'.comp ι
    have hρ : Function.Injective ρ := hρ'.comp hinj
    haveI : IsLocalHom ρ := inferInstance
    haveI : CharZero V := charZero_of_injective_ringHom hρ
    have hgV : ρ' (ι g) ≠ 0 := fun h => hgR (hρ' (by rw [h, map_zero]))
    refine dvd_of_forall_mem_span_sup_pow hgV fun e => ?_
    have h1 : ρ (b e) ∈ Ideal.span {ρ g} ⊔ maximalIdeal V ^ e := hV V hVc ρ hρ inferInstance e
    have hmap : ∀ x ∈ maximalIdeal R, ρ' x ∈ maximalIdeal V := by
      intro x hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
      exact fun h => hx (isUnit_of_map_unit ρ' x h)
    have h2 : ρ' (ι (b e) - F) ∈ maximalIdeal V ^ e := by
      have hle : (maximalIdeal R ^ e).map ρ' ≤ maximalIdeal V ^ e := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmap) e
      exact hle (Ideal.mem_map_of_mem _ (hF' e))
    have : ρ' F = ρ (b e) - ρ' (ι (b e) - F) := by
      simp [ρ, map_sub]
    rw [this]
    exact Ideal.sub_mem _ h1 (Ideal.mem_sup_right h2)

  have hmem : ι (b n) ∈ (Ideal.span {g} ⊔ m ^ n).map ι := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_pow, ← hmR]
    have h3 : F ∈ Ideal.span {ι g} := Ideal.mem_span_singleton.mpr hdvd
    have : ι (b n) = F + (ι (b n) - F) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h3) (Ideal.mem_sup_right (hF' n))
  rwa [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem

end GlobalTheory.Poinc
