import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem cast_sum_add_mul {ι : Type*} [Fintype ι] (f : ι → ℕ) (c n m : ℕ) (h : n = m) :
    (((∑ i, f i) + c * n : ℕ) : ℤ) = ∑ i, (f i : ℤ) + (c : ℤ) * (m : ℤ) := by
  subst h; push_cast; rfl

open scoped Classical in

theorem dInf_eq (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    dInf (dN hL hζ M hM hΓ) =
      ∑ v : {v : InfinitePlace K.1 // v.IsReal},
          (Module.finrank (ZMod ℓ) (Representation.invariants
            ((nRep hL hζ M hM).comp (gsRealDecompGroup S ιr hL v).subtype)) : ℤ) +
        Fintype.card {v : InfinitePlace K.1 // v.IsComplex} * Module.finrank (ZMod ℓ) M := by
  have : IsGalois K.1 L.1 := ⟨⟩
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN : Module.finrank (ZMod ℓ) (homRep (gsRootsZMod S ℓ) M) = Module.finrank (ZMod ℓ) M := by
    change Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ →ₗ[ZMod ℓ] M) = _
    rw [Module.finrank_linearMap, hT, one_mul]
  have key := finrank_invariants_funPermRep_infinitePlace (k := ZMod ℓ) S ιr hL (nRep hL hζ M hM)
  have e1 : dInf (dN hL hζ M hM hΓ) = (Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (NumberField.InfinitePlace L.1)).tprod (nRep hL hζ M hM)).invariants : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact e1.trans ((congrArg (Nat.cast (R := ℤ)) key).trans (cast_sum_add_mul _ _ _ _ hN))

end PositivityTheory.Lit1.GEN.X
