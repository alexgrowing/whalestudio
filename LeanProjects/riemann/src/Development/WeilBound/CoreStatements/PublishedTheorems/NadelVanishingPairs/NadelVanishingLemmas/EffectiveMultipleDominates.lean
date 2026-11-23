import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierDivisorMultCharacterize

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Domin

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem mult_zero' (z : X) : (0 : CartierDiv X).mult z = 0 := by
  have h₀ := CartierDiv.mult_add (0 : CartierDiv X) 0 z
  rw [add_zero] at h₀
  omega

theorem mult_nsmul'' (E : CartierDiv X) (n : ℕ) (z : X) : (n • E).mult z = n * E.mult z := by
  induction n with
  | zero => rw [zero_nsmul, mult_zero']; simp
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem mult_sub' (D E : CartierDiv X) (z : X) : (D - E).mult z = D.mult z - E.mult z := by
  have h := CartierDiv.mult_add (D - E) E z
  rw [sub_add_cancel] at h
  omega

theorem eq_of_specializes_of_coheight (z z' : X) (h : z' ⤳ z) (hz : Order.coheight z = 1)
    (hz' : Order.coheight z' = 1) : z' = z := by
  by_cases h' : z' ≤ z
  · exact (h.antisymm h').eq
  · exfalso
    have hlt : z < z' := lt_of_le_not_ge h h'
    have h2 := Order.coheight_strictAnti hlt (by simp [hz'])
    rw [hz, hz'] at h2
    exact lt_irrefl _ h2

end GlobalTheory.Domin

private theorem exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : ringKrullDim R ≤ 1) (a p : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hp : p ≠ 0) :
    ∃ N : ℕ, ∃ b : R, a ^ N = p * b := by
  by_cases hpu : IsUnit p
  · exact ⟨0, ↑hpu.unit⁻¹, by simp⟩
  · haveI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by exact_mod_cast hR)
    have hmax : ∀ P : Ideal R, P.IsPrime → p ∈ P → P = IsLocalRing.maximalIdeal R := by
      intro P hP hpP
      rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top (⟨P, hP⟩ : PrimeSpectrum R) with h | h
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simp at h'
        rw [h'] at hpP
        exact absurd ((Submodule.mem_bot R).1 hpP) hp
      · have h' := congrArg PrimeSpectrum.asIdeal h
        simpa using h'
    have hrad : a ∈ (Ideal.span {p}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      rintro P ⟨hPp, hP⟩
      rw [hmax P hP (hPp (Ideal.mem_span_singleton_self p))]
      exact ha
    have hle : Ideal.span {a} ≤ (Ideal.span {p}).radical := (Ideal.span_singleton_le_iff_mem _).2 hrad
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle (Submodule.fg_span_singleton a)
    have : a ^ N ∈ Ideal.span {p} := hN (by rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨N, b, by rw [← hb, mul_comm]⟩

private theorem exists_nsmul_sub_regularAt_of_supp_le {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D E : CartierDiv X) (hE : E.Eff)
    (hsupp : D.supp ≤ E.supp) (z : X) (hz : Order.coheight z = 1) :
    ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → (c • E - D).RegularAt z 1 := by
  obtain ⟨gD, hgD⟩ := D.exists_isEqn z
  obtain ⟨gE, hgE⟩ := E.exists_isEqn z
  have hEq : ∀ c : ℕ, (c • E - D).IsEqn z (gE ^ c / gD) := fun c => (hgE.nsmul c).sub hgD
  obtain ⟨a, ha⟩ := CartierDiv.eff_iff.1 hE z gE hgE
  suffices key : ∃ c0 : ℕ, (z ∉ D.supp → c0 = 0) ∧ ∀ c : ℕ, c0 ≤ c → RegAt z ((gE ^ c / gD : (X.functionField)ˣ) : X.functionField) by
    obtain ⟨c0, h0, hc0⟩ := key
    exact ⟨c0, h0, fun c hc => (hEq c).regularAt_iff.2 (by rw [one_mul]; exact hc0 c hc)⟩
  by_cases hzD : z ∈ D.supp
  · have ha' : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hau
      exact (hgE.mem_supp_iff.1 (hsupp hzD)) ⟨a, hau, ha⟩
    obtain ⟨⟨q, ⟨p, hp⟩⟩, hpq⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (X.presheaf.stalk z))
      ((gD⁻¹ : (X.functionField)ˣ) : X.functionField)
    dsimp only at hpq
    have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
    have hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1 := (ringKrullDim_stalk_le_one_iff z).2 hz.le
    obtain ⟨N, b, hab⟩ := exists_pow_eq_mul_of_mem_maximalIdeal_dim_le_one hdim a p ha' hp0
    refine ⟨N, fun h => absurd hzD h, fun c hc => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
    refine ⟨b * q * a ^ d, ?_⟩
    have hpK : algebraMap (X.presheaf.stalk z) X.functionField p ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hp
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, div_eq_mul_inv,
      ← Units.val_inv_eq_inv_val, ← hpq, IsFractionRing.mk'_eq_div, ← map_pow, pow_add, hab]
    simp only [map_mul]
    field_simp
  · have hu : UnitAt z (gD : X.functionField) := by
      by_contra h
      exact hzD (hgD.mem_supp_iff.2 h)
    obtain ⟨u, hu, hugD⟩ := hu
    refine ⟨0, fun _ => rfl, fun c _ => ⟨a ^ c * ↑hu.unit⁻¹, ?_⟩⟩
    have h1 : algebraMap (X.presheaf.stalk z) X.functionField u *
        algebraMap (X.presheaf.stalk z) X.functionField (↑hu.unit⁻¹) = 1 := by
      rw [← map_mul]; simp
    have hne := left_ne_zero_of_mul_eq_one h1
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, ← ha, ← hugD, map_mul, map_pow,
      eq_div_iff hne, mul_assoc, mul_comm (algebraMap _ _ _) (algebraMap _ _ u), h1, mul_one]

private theorem eq_of_mem_supp_specializes_coheight_one {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (y z : X) (hy : y ∈ D.supp) (h : y ⤳ z)
    (hz : Order.coheight z = 1) : y = z := by
  by_contra hne
  have hzy : z ≤ y := h
  have hnot : ¬ y ≤ z := fun h' => hne (h.antisymm h').eq
  have hlt : z < y := lt_of_le_not_ge hzy hnot
  have hfin : Order.coheight y < ⊤ := lt_of_le_of_lt (Order.coheight_anti hzy) (by simp [hz])
  have h1 := Order.coheight_strictAnti hlt hfin
  rw [hz] at h1
  have h0 : Order.coheight y = 0 := ENat.lt_one_iff_eq_zero.1 h1
  have hη : genericPoint X ⤳ y := genericPoint_specializes y
  by_cases hyη : genericPoint X ≤ y
  · have hyeq : y = genericPoint X := (Specializes.antisymm hyη hη).eq
    exact D.genericPoint_notMem_supp (hyeq ▸ hy)
  · have hlt2 : y < genericPoint X := lt_of_le_not_ge hη hyη
    have h2 := Order.coheight_strictAnti hlt2 (lt_of_le_of_lt (Order.coheight_anti (show y ≤ genericPoint X from hη)) (by simp [h0]))
    rw [h0] at h2
    exact absurd h2 (by simp)

private theorem finite_coheight_one_inter_supp {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] (D : CartierDiv X) :
    {z : X | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨S, hSirr, hSeq⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible D.supp
  refine Set.Finite.subset (S.finite_toSet.biUnion fun k _ => (show {x : X | IsGenericPoint x (k : Set X)}.Subsingleton
    from fun x hx y hy => hx.eq hy).finite) ?_
  rintro z ⟨hz, hzD⟩
  have hzS : z ∈ (S.sup id : TopologicalSpace.Closeds X) := by rw [← hSeq]; exact hzD
  have hex : z ∈ (S.sup id : TopologicalSpace.Closeds X) → ∃ k ∈ S, z ∈ k :=
    Finset.sup_induction (p := fun C : TopologicalSpace.Closeds X => z ∈ C → ∃ k ∈ S, z ∈ k)
      (fun h => by rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h; exact absurd h (Set.notMem_empty z))
      (fun a ha b hb h => by
        rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_sup] at h
        rcases h with h | h
        exacts [ha h, hb h])
      (fun k hk h => ⟨k, hk, h⟩)
  obtain ⟨k, hkS, hzk⟩ := hex hzS
  have hirr := hSirr ⟨k, hkS⟩
  have ht : IsGenericPoint hirr.genericPoint (k : Set X) := hirr.isGenericPoint_genericPoint k.isClosed
  have hkD : (k : Set X) ⊆ D.supp := by
    have : k ≤ D.supp := by rw [hSeq]; exact Finset.le_sup (f := id) hkS
    exact this
  have hteq := eq_of_mem_supp_specializes_coheight_one D _ z (hkD ht.mem) (ht.specializes hzk) hz
  exact Set.mem_biUnion hkS (show IsGenericPoint z (k : Set X) from hteq ▸ ht)

open GlobalTheory.Domin in

theorem GlobalTheory.effDominates : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [CompactSpace X] (D E : CartierDiv X), E.Eff → D.supp ≤ E.supp → ∃ c : ℕ, (c • E - D).Eff := by
  intro X _ _ _ _ D E hE hsupp
  classical
  have hfin := finite_coheight_one_inter_supp D
  let c0 : X → ℕ := fun z =>
    if hz : Order.coheight z = 1 then Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) else 0
  refine ⟨hfin.toFinset.sup c0, ?_⟩
  have hreg : ∀ z : X, Order.coheight z = 1 → (hfin.toFinset.sup c0 • E - D).RegularAt z 1 := by
    intro z hz
    have hspec := Classical.choose_spec (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz)
    apply hspec.2
    have hc0 : c0 z = Classical.choose (exists_nsmul_sub_regularAt_of_supp_le D E hE hsupp z hz) := by simp [c0, hz]
    rw [← hc0]
    by_cases hzD : z ∈ D.supp
    · exact Finset.le_sup (f := c0) (hfin.mem_toFinset.2 ⟨hz, hzD⟩)
    · rw [hc0, hspec.1 hzD]
      exact Nat.zero_le _
  intro x
  obtain ⟨g, hg⟩ := (hfin.toFinset.sup c0 • E - D).exists_isEqn x
  rw [hg.regularAt_iff, one_mul]
  apply regAt_of_forall_coheight_eq_one
  intro z hzx hz
  obtain ⟨U, hxU, hU⟩ := hg.exists_nhds
  have hgz := hU z (hzx.mem_open U.isOpen hxU)
  have h1 := hgz.regularAt_iff.1 (hreg z hz)
  rwa [one_mul] at h1
