import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRCrd

theorem isDominant_spMap_of_injective {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (h : Function.Injective φ) : IsDominant (spMap φ) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot φ).1 h]; exact bot_le)⟩

theorem dualMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    (dualMap ψ).comp (dualMap φ) = dualMap (ψ.comp φ) := by
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem mem_latDR_iff_crd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [X.IsSeparated] (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (φ : Γ(X, L.U i) →+* ↥(intO C)) (x : Sp C ⟶ X) (w : Tn t C), spMap ((intO C).subtype.comp φ) ≫ (aff i).fromSpec = x → IsTanAtG t x w → (w ∈ latDR t x ↔ ∀ r, ‖crd i C ((intO C).subtype.comp φ) w r‖ ≤ 1) := by
  intro E _ _ _ H X _ t L aff M crd h i C _ _ φ x w hx hw
  have hx' : spMap (intO C).subtype ≫ (spMap φ ≫ (aff i).fromSpec) = x := by
    rw [← Category.assoc, spMap_comp', hx]
  constructor
  · rintro ⟨xO, hxO, vO, hv, rfl⟩ r
    have := isDominant_spMap_of_injective (intO C).subtype Subtype.val_injective
    obtain rfl : xO = spMap φ ≫ (aff i).fromSpec :=
      ext_of_isDominant (spMap (intO C).subtype) (hxO.trans hx'.symm)
    rw [h.nat i _ C φ (intO C).subtype vO hv]
    exact (crd i _ φ vO r).2
  · intro hr
    subst hx
    obtain ⟨n, v, D, ⟨hv, hb⟩, hD⟩ := h.split i
    obtain ⟨a, ha, -⟩ := hb C _ w hw
    have hvC := fun j => isTanAtG_map t ((intO C).subtype.comp φ) (hv j)
    have hvO := fun j => isTanAtG_map t φ (hv j)
    have h1 : spMap (RingHom.id Γ(X, L.U i)) = 𝟙 _ := Spec.map_id _
    have hc := h.comb i C _ n _ a w hvC ha
    have hn : ∀ j, crd i C ((intO C).subtype.comp φ) (spMap (dualMap ((intO C).subtype.comp φ)) ≫ v j) =
        ((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j) := fun j =>
      h.nat i _ C (RingHom.id _) ((intO C).subtype.comp φ) (v j) (by rw [h1, Category.id_comp]; exact hv j)
    have hD' := hD.map ((intO C).subtype.comp φ)
    have hmem : ∀ j, a j ∈ intO C := fun j => by
      have e : a j = ∑ r, ((intO C).subtype.comp φ) (D j r) * crd i C ((intO C).subtype.comp φ) w r := by
        rw [hc]
        simp only [hn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        have : ∀ j', ∑ r, ((intO C).subtype.comp φ) (D j r) *
            (a j' * (((intO C).subtype.comp φ) ∘ crd i _ (RingHom.id _) (v j')) r) =
            if j = j' then a j' else 0 := fun j' => by
          have e := hD' j j'
          simp only [mul_left_comm _ (a j'), ← Finset.mul_sum]
          refine (congrArg (a j' * ·) e).trans ?_
          split_ifs <;> simp
        simp only [this]
        simp
      rw [e]
      exact Subring.sum_mem _ fun r _ => Subring.mul_mem _ (φ (D j r)).2 (hr r)
    obtain ⟨wO, hwO, hcO⟩ := exists_comb t hvO fun j => (⟨a j, hmem j⟩ : ↥(intO C))
    refine ⟨_, hx', wO, hwO, ?_⟩
    have hb := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [← Category.assoc, spMap_comp', dualMap_comp'] at hb
    exact comb_unique t hvC hb ha

end GlobalTheory.LatDRCrd
