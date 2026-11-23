import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlatBaseChangeTensorInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelOfIsAlgClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem isRapoport_of_level (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) (R : Type) [CommRing R] (hNR : IsUnit (N : R))
    (hd : IsUnit ((NumberField.discr F : ℤ) : R)) (X : Obj F 𝔠 (Sp R)) (α : X.Level N) : X.IsRapoport := by
  obtain ⟨M, s, U, α₀, hfine, -, -, -, -, -, ⟨V, hV, -, hbasic, -⟩, -, -⟩ := hDP F 𝔠 N hN
  have hNZ : IsUnit (algebraMap ℤ R (N : ℤ)) := by simpa using hNR
  let ρ : Localization.Away (N : ℤ) →+* R := IsLocalization.Away.lift (N : ℤ) hNZ
  obtain ⟨b, ⟨-, φ, hpull, -⟩, -⟩ := hfine (Sp R) (spMap ρ) X α
  have hunit : IsUnit (b.appTop ((NumberField.discr F : ℤ) : Γ(M, ⊤))) := by
    rw [map_intCast]
    have := hd.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    simpa using this
  have hpre : b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤)) = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact Scheme.basicOpen_of_isUnit _ hunit
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun x K _ t ⟨p, hp⟩ Y ψ hY ↦ ?_
  have hx : b x ∈ (V : Set M) := by
    apply hbasic
    change x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤))
    rw [hpre]; trivial
  rw [hV] at hx
  refine hx K (t ≫ b) ⟨p, ?_⟩ Y (ψ ≫ φ) (hY.comp hpull)
  rw [← hp]
  first | rfl | exact Scheme.Hom.comp_apply t b p | simp

theorem isRapoport_of_field (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) (K : Type) [Field K] (hNK : IsUnit (N : K))
    (hd : IsUnit ((NumberField.discr F : ℤ) : K)) (X : Obj F 𝔠 (Sp K)) : X.IsRapoport := by
  let σ := algebraMap K (AlgebraicClosure K)
  obtain ⟨X', φ, h⟩ := Obj.exists_isPullBy X (spMap σ)
  have hN' : IsUnit (N : AlgebraicClosure K) := by simpa using hNK.map σ
  obtain ⟨α⟩ := nonempty_level_of_isAlgClosed F 𝔠 N (AlgebraicClosure K) hN'.ne_zero X'
  have hX' : X'.IsRapoport := isRapoport_of_level hDP F 𝔠 N hN _ hN' (by simpa using hd.map σ) X' α
  obtain ⟨e, -, he⟩ := Obj.exists_lieEquiv (R' := AlgebraicClosure K) h
  exact GlobalTheory.invertible_of_faithfullyFlat_baseChange_tensor_int K (AlgebraicClosure K) (𝓞 F) X.Lie X'.Lie e he hX'

theorem isRapoport_of_isUnit_discr : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R],
  IsUnit ((NumberField.discr F : ℤ) : R) → ∀ X : Obj F 𝔠 (Sp R), X.IsRapoport := by
  intro hDP F _ _ _ 𝔠 R _ hd X
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
  have hdK : IsUnit ((NumberField.discr F : ℤ) : K) := by simpa using hd.map σ
  by_cases h3 : (3 : K) = 0
  · have h4 : IsUnit ((4 : ℕ) : K) := by
      refine IsUnit.mk0 _ ?_
      have : ((4 : ℕ) : K) = 3 + 1 := by push_cast; ring
      rw [this, h3, zero_add]; exact one_ne_zero
    exact isRapoport_of_field hDP F 𝔠 4 (by norm_num) K h4 hdK Y
  · exact isRapoport_of_field hDP F 𝔠 3 le_rfl K (IsUnit.mk0 _ (by exact_mod_cast h3)) hdK Y

end GlobalTheory.RealMult
