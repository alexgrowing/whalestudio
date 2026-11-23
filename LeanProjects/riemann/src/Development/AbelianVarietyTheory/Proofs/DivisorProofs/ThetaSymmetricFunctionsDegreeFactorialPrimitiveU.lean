import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem symTup_unit_of_prim : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (e : Fin N → FractionRing V), Prim (io.comp (algebraMap V (FractionRing V))) c → (∀ j, io (e j) = symTup c j) → ∃ e' : Fin N → V, (∀ j, algebraMap V (FractionRing V) (e' j) = e j) ∧ ∃ j, IsUnit (e' j) := by
  intro V K _ _ _ _ _ io N c e hP he
  set i := io.comp (algebraMap V (FractionRing V)) with hi
  have hio : Function.Injective io := io.injective
  have hinj : Function.Injective i := hio.comp (IsFractionRing.injective V (FractionRing V))
  letI : Algebra V K := i.toAlgebra
  have hcI : ∀ a, IsIntegral V (c a) := hP.1
  have hsI : ∀ j, IsIntegral V (symTup c j) := by
    intro j
    have : symTup c j ∈ integralClosure V K := by
      unfold symTup
      refine Subalgebra.pow_mem _ ?_ _
      rw [Finset.esymm_map_val]
      exact Subalgebra.sum_mem _ fun t _ => Subalgebra.prod_mem _ fun b _ => hcI b
    exact this
  let φ : FractionRing V →ₐ[V] K := { io with commutes' := fun r => rfl }
  have heI : ∀ j, IsIntegral V (e j) := fun j =>
    (isIntegral_algHom_iff φ hio).1 (by rw [show φ (e j) = io (e j) from rfl, he j]; exact hsI j)
  choose e' he' using fun j => IsIntegrallyClosed.isIntegral_iff.1 (heI j)
  refine ⟨e', he', ?_⟩
  obtain ⟨a₀, hc0, hinv⟩ := hP.2
  obtain ⟨W, hle⟩ := (LocalSubring.range i).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.1 hle
  have memW : ∀ x : K, i.IsIntegralElem x → x ∈ W := by
    intro x ⟨p, hp, hx⟩
    have : IsIntegral W x := by
      let g : V →+* W := i.codRestrict W (fun v => hle ⟨v, rfl⟩)
      refine ⟨p.map g, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]; exact hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    rw [← hy]; exact y.2
  have hcW : ∀ a, c a ∈ W := fun a => memW _ (hP.1 a)
  have hc0W : (c a₀)⁻¹ ∈ W := memW _ hinv
  let y : Fin N → W := fun a => ⟨c a * (c a₀)⁻¹, mul_mem (hcW a) hc0W⟩
  have hy0 : y a₀ = 1 := Subtype.ext (mul_inv_cancel₀ hc0)
  obtain ⟨k, hk1, hkN, hu⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) y a₀ hy0
  rw [Fintype.card_fin] at hkN
  set E := (Finset.univ.val.map y).esymm k with hE
  let u0 : W := ⟨c a₀, hcW a₀⟩
  have hu0 : IsUnit u0 := isUnit_iff_exists_inv.2 ⟨⟨(c a₀)⁻¹, hc0W⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩
  let Z : W := (u0 ^ k * E) ^ (N.factorial / k)
  have hZ : IsUnit Z := ((hu0.pow k).mul hu).pow _
  let j : Fin N := ⟨k - 1, by omega⟩
  have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
  have hZj : (Z : K) = i (e' j) := by
    have : i (e' j) = io (e j) := by rw [hi, RingHom.comp_apply, he' j]
    rw [this, he j]
    simp only [Z, symTup, hjk, hE, Finset.esymm_map_val]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_powersetCard.1 ht).2.symm, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [y, u0]
    field_simp
  refine ⟨j, ?_⟩
  have hmem : i (e' j) ∈ (LocalSubring.range i).toSubring := ⟨e' j, rfl⟩
  have h1 : IsUnit (Subring.inclusion hle ⟨i (e' j), hmem⟩) := by
    have h0 : Subring.inclusion hle ⟨i (e' j), hmem⟩ = Z := by apply Subtype.ext; exact hZj.symm
    rw [h0]; exact hZ
  obtain ⟨u, hu'⟩ := hloc.map_nonunit _ h1
  obtain ⟨w, hw⟩ := ((u⁻¹ : Units _) : (LocalSubring.range i).toSubring).2
  refine isUnit_iff_exists_inv.2 ⟨w, hinj ?_⟩
  have h3 : ((u : (LocalSubring.range i).toSubring) : K) * (((u⁻¹ : Units _) : (LocalSubring.range i).toSubring) : K) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [map_mul, map_one, hw, ← h3, hu']

end GlobalTheory.UMin
