import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Desc.GaussBC

theorem two_le_coheight_of_chain {X : Scheme.{0}} {x e g : X} (h₁ : e ⤳ x) (h₂ : g ⤳ e) (n₁ : e ≠ x)
    (n₂ : g ≠ e) : (2 : ℕ∞) ≤ Order.coheight x := by
  have l₁ : x < e := lt_of_le_not_ge h₁ (fun h => n₁ (h₁.antisymm h).eq)
  have l₂ : e < g := lt_of_le_not_ge h₂ (fun h => n₂ (h₂.antisymm h).eq)
  have a₁ := Order.coheight_add_one_le l₁
  have a₂ := Order.coheight_add_one_le l₂
  calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
    _ ≤ Order.coheight g + 1 + 1 := by gcongr; exact zero_le
    _ ≤ Order.coheight e + 1 := by gcongr
    _ ≤ Order.coheight x := a₁

theorem not_two_le_coheight_of_ringKrullDim_eq_one {X : Scheme.{0}} (x : X)
    (h : ringKrullDim (X.presheaf.stalk x) = 1) : ¬ (2 : ℕ∞) ≤ Order.coheight x := by
  intro h₂
  rw [ringKrullDim_stalk_eq_coheight] at h
  have : Order.coheight x = 1 := by exact_mod_cast h
  rw [this] at h₂
  exact absurd h₂ (by decide)

theorem apply_genericPoint_ne_closedPoint {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp R) [Flat f] : f (genericPoint X) ≠ closedPoint R := by
  intro h
  let p₀ : Sp R := ⟨⊥, Ideal.bot_prime⟩
  have hs : p₀ ⤳ f (genericPoint X) := by
    rw [h]; exact (PrimeSpectrum.le_iff_specializes p₀ (closedPoint R)).mp bot_le
  obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f hs
  have hw' : w = genericPoint X := (hw.antisymm (genericPoint_specializes w)).eq
  rw [hw', h] at hfw
  exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal hfw)

theorem apply_eq_of_closedFibre_dim_one : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hG hpb _ y y' hy hy' hdy hdy'
  haveI : Smooth H.hom := hG.smooth
  haveI : Flat H'.hom := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat H.hom))
  haveI : Flat (spMap a) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ha
  haveI : Flat π := MorphismProperty.of_isPullback hpb.flip (inferInstanceAs (Flat (spMap a)))
  have hsq : ∀ z, H.hom (π z) = spMap a (H'.hom z) := fun z => by
    have := congrArg (fun f => f.base z) hpb.w
    simpa using this
  have hcl : spMap a (closedPoint D) = closedPoint T := by
    apply PrimeSpectrum.ext
    show Ideal.comap a (maximalIdeal D) = maximalIdeal T
    have hle : maximalIdeal T ≤ Ideal.comap a (maximalIdeal D) := Ideal.map_le_iff_le_comap.mp hm.le
    exact ((maximalIdeal.isMaximal T).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle).symm
  have hback : ∀ p : Sp D, spMap a p = closedPoint T → p = closedPoint D := by
    intro p hp
    by_contra hne
    have hbot : p.asIdeal = ⊥ := by
      by_contra hb
      exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hb)))
    have hker : Ideal.comap a ⊥ = maximalIdeal T := by
      rw [← hbot]; exact congrArg PrimeSpectrum.asIdeal hp
    apply IsDiscreteValuationRing.not_a_field D
    rw [← hm, ← hker]
    exact le_antisymm Ideal.map_comap_le bot_le
  set F : Set H.left := H.hom ⁻¹' {closedPoint T} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint T).preimage H.hom.continuous
  have hFi : IsIrreducible F := by
    haveI := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ H hG _ ((Sp T).fromSpecResidueField (closedPoint T))
    haveI : IrreducibleSpace (H.hom.fiber (closedPoint T)) := this
    have hr := (IrreducibleSpace.isIrreducible_univ (H.hom.fiber (closedPoint T))).image _
      (Scheme.Hom.fiberι H.hom (closedPoint T)).continuous.continuousOn
    rw [Set.image_univ] at hr
    convert hr using 1
    exact (Scheme.Hom.range_fiberι H.hom (closedPoint T)).symm
  have hξ₀ := hFi.isGenericPoint_genericPoint_closure
  rw [hFc.closure_eq] at hξ₀
  set ξ₀ := hFi.genericPoint
  have hgH := apply_genericPoint_ne_closedPoint H.hom
  have hgH' := apply_genericPoint_ne_closedPoint H'.hom
  have hyξ₀ : y = ξ₀ := by
    by_contra hne
    refine not_two_le_coheight_of_ringKrullDim_eq_one y hdy
      (two_le_coheight_of_chain (hξ₀.specializes hy) (genericPoint_specializes ξ₀) (Ne.symm hne) ?_)
    intro h; apply hgH; rw [h]; exact hξ₀.mem
  have hzξ₀ : π y' = ξ₀ := by
    by_contra hne
    have hz : π y' ∈ F := by
      show H.hom (π y') = closedPoint T
      rw [hsq, hy', hcl]
    obtain ⟨w, hw, hπw⟩ := Flat.generalizingMap π (hξ₀.specializes hz)
    refine not_two_le_coheight_of_ringKrullDim_eq_one y' hdy'
      (two_le_coheight_of_chain hw (genericPoint_specializes w) ?_ ?_)
    · rintro rfl; exact hne hπw
    · intro h; apply hgH'; apply hback; rw [← hsq, h, hπw]; exact hξ₀.mem
  rw [hzξ₀, hyξ₀]

end GlobalTheory.Desc.GaussBC
