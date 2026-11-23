import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PFinite
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FiniteCohomologyRootsZMod
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FinrankH2EulerFormula
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.PUnits
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.CastSumAddMul
import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.FinrankKerSubOneAddFinrankKerAddOne

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem sum_eq_card_mul_sub {ι : Type*} [Fintype ι] (a b : ι → ℤ) (m : ℤ) (h : ∀ i, a i = m - b i) :
    ∑ i, a i = Fintype.card ι * m - ∑ i, b i := by
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

open scoped Classical in

theorem altSum [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hPn : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) (hK : ℓ ≠ 2 ∨ IsTotallyComplex L.1)
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
    (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m) :
    (Module.finrank (ZMod ℓ) (cohomology M 0) : ℤ) - Module.finrank (ZMod ℓ) (cohomology M 1) +
        Module.finrank (ZMod ℓ) (cohomology M 2) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ) -
        Fintype.card (InfinitePlace K.1) * Module.finrank (ZMod ℓ) M := by
  have : Normal K.1 L.1 := normal_of_gsOpenSubgroup_normal hL hPn
  have hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ := by rw [card_gal_eq_index hL]; exact hcop
  have := finite_modN_AA (ℓ := ℓ) hL 0 (by norm_num)
  have := finite_torsN_AA (ℓ := ℓ) hL 0 (by norm_num)
  have := finite_modN_AA (ℓ := ℓ) hL 1 le_rfl
  have := finite_torsN_AA (ℓ := ℓ) hL 1 le_rfl
  have e0 := h0_eq hL hζ M hM hΓ hℓS hcop
  have e1 := finrank_H1_euler_formula hL hζ M hM hΓ hℓS hcop
  have e2 := finrank_H2_euler_formula hL hζ M hM hΓ hℓS hcop hK
  have u0 := S_units_euler_difference hL (dN hL hζ M hM hΓ)
  have u1 := class_group_mod_eq_torsion hL (dN hL hζ M hM hΓ)
  have ei := dInf_eq hL hζ M hM hΓ ιr hℓS
  have hsr := sum_eq_card_mul_sub
    (fun v : {v : InfinitePlace K.1 // v.IsReal} =>
      (Module.finrank (ZMod ℓ) (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0) : ℤ))
    (fun v : {v : InfinitePlace K.1 // v.IsReal} => (Module.finrank (ZMod ℓ) (Representation.invariants
          ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) : ℤ))
    (Module.finrank (ZMod ℓ) M : ℤ) fun v => by linarith [real_place_H0_finrank hL hζ M hM ιr hℓS hcop hK v]
  have hc : (Fintype.card (InfinitePlace K.1) : ℤ) = Fintype.card {v : InfinitePlace K.1 // v.IsReal} +
      Fintype.card {v : InfinitePlace K.1 // v.IsComplex} := by exact_mod_cast card_infinitePlace_eq K
  linear_combination e0 - e1 + e2 - hsr + (Module.finrank (ZMod ℓ) M : ℤ) * hc - u0 + u1 - ei

end PositivityTheory.Lit1.GEN.X
