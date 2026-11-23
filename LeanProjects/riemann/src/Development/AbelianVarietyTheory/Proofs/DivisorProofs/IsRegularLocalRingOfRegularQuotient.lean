import Mathlib
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

theorem height_add_ringKrullDim_quotient_le {R : Type} [CommRing R] (p : Ideal R) [hp : p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) ≤ ringKrullDim R := by
  let P : PrimeSpectrum R := ⟨p, hp⟩
  haveI : Nonempty (PrimeSpectrum R) := ⟨P⟩
  have h1 : PrimeSpectrum.zeroLocus (p : Set R) = Set.Ici P := by
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici]
    rfl
  have h2 : ringKrullDim (R ⧸ p) = (Order.coheight P : ℕ∞) := by
    rw [ringKrullDim_quotient, h1, Order.coheight_eq_krullDim_Ici]
  have h3 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  rw [h2, h3, ← WithBot.coe_add]
  change _ ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, WithBot.coe_le_coe]
  exact le_iSup (fun x : PrimeSpectrum R => Order.height x + Order.coheight x) P

theorem spanFinrank_maximalIdeal_le {R : Type} [CommRing R] [IsLocalRing R] (p : Ideal R)
    [p.IsPrime] [IsLocalRing (R ⧸ p)] (r : ℕ) (f : Fin r → R) (hf : p = Ideal.span (Set.range f))
    (hfg : (maximalIdeal (R ⧸ p)).FG) :
    (maximalIdeal R).spanFinrank ≤ r + (maximalIdeal (R ⧸ p)).spanFinrank := by
  classical
  obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  choose g hg using Ideal.Quotient.mk_surjective (I := p)
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h1 : Ideal.map (Ideal.Quotient.mk p) (Ideal.span (g '' s)) = maximalIdeal (R ⧸ p) := by
    rw [Ideal.map_span, Set.image_image]
    simpa [hg] using hsp
  have h2 : maximalIdeal R =
      Ideal.span (((s.image g) ∪ Finset.univ.image f : Finset R) : Set R) := by
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk p)) (hmap.trans h1.symm)
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hpm] at h3
    rw [h3, Finset.coe_union, Ideal.span_union, Finset.coe_image, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, ← hf]
  have h4 := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le
    ((s.image g) ∪ Finset.univ.image f)
  rw [← h2] at h4
  have h5 := Finset.card_union_le (s.image g) (Finset.univ.image f)
  have h6 : (s.image g).card ≤ s.card := Finset.card_image_le
  have h7 : (Finset.univ.image f).card ≤ r := Finset.card_image_le.trans (by simp)
  omega

theorem isRegularLocalRing_of_quotient_prime :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
      (r : ℕ) (f : Fin r → R), p = Ideal.span (Set.range f) → p.height = r →
      IsRegularLocalRing (R ⧸ p) → IsRegularLocalRing R := by
  intro R _ _ _ p _ r f hf hh hreg
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hfg : (maximalIdeal (R ⧸ p)).FG := IsNoetherian.noetherian _
  have hs := spanFinrank_maximalIdeal_le p r f hf hfg
  have hq : ((maximalIdeal (R ⧸ p)).spanFinrank : WithBot ℕ∞) = ringKrullDim (R ⧸ p) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd := height_add_ringKrullDim_quotient_le p
  rw [hh, ← hq] at hd
  refine le_trans ?_ hd
  have : (((maximalIdeal R).spanFinrank : ℕ) : WithBot ℕ∞) ≤
      (((r + (maximalIdeal (R ⧸ p)).spanFinrank : ℕ)) : WithBot ℕ∞) := by exact_mod_cast hs
  refine this.trans (le_of_eq ?_)
  push_cast
  rfl

end GlobalTheory.RegularAscent
