import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstAffineLine

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]

theorem spMap_section {k : Type} [Field k] (φ : Polynomial k →+* k)
    (hφ : φ.comp (algebraMap k (Polynomial k)) = RingHom.id k) :
    spMap φ ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
  rw [spMap_comp', hφ, spMap_id']

theorem eq_of_const_nonzero : ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) [IsSeparated q] [LocallyOfFiniteType q] (f : Sp (Polynomial k) ⟶ Y), f ≫ q = spMap (algebraMap k (Polynomial k)) → (∀ c : k, c ≠ 0 → spMap (Polynomial.evalRingHom c) ≫ f = spMap (Polynomial.evalRingHom 1) ≫ f) → ∀ a b : Polynomial k →ₐ[k] k, spMap a.toRingHom ≫ f = spMap b.toRingHom ≫ f := by
  intro k _ _ Y q _ _ f hq hc a b
  have h1 : (Polynomial.evalRingHom (1 : k)).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
    ext x; simp
  have hs1 := spMap_section _ h1
  set f' := spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom (1 : k)) ≫ f with hf'
  have hlft : LocallyOfFiniteType (f ≫ q) := by
    rw [hq]; exact HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  have key : f = f' := by
    refine ext_of_apply_eq (K := k) q
      ((PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) : Set (PrimeSpectrum (Polynomial k))))
      (PrimeSpectrum.basicOpen _).isOpen.isLocallyClosed ?_ ?_ ?_
    · refine IsOpen.dense (X := PrimeSpectrum (Polynomial k)) (PrimeSpectrum.basicOpen _).isOpen
        ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
      simp [PrimeSpectrum.mem_basicOpen, Polynomial.X_ne_zero]
    · intro x hx hcl
      have hp := pointOfClosedPoint_comp (f ≫ q) x hcl
      have hpx := pointOfClosedPoint_apply (f ≫ q) x hcl (IsLocalRing.closedPoint k)
      generalize pointOfClosedPoint (f ≫ q) x hcl = p at hp hpx
      rw [hq] at hp
      obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = p := ⟨Spec.preimage p, Spec.map_preimage p⟩
      have hφ : φ.hom.comp (algebraMap k (Polynomial k)) = RingHom.id k := by
        have := Spec.map_injective (show Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)) ≫ φ)
          = Spec.map (𝟙 _) by rw [Spec.map_comp, Spec.map_id]; exact hp)
        simpa using congrArg CommRingCat.Hom.hom this
      have hev : φ = CommRingCat.ofHom (Polynomial.evalRingHom (φ.hom Polynomial.X)) := by
        apply CommRingCat.hom_ext
        apply Polynomial.ringHom_ext
        · intro a
          rw [Polynomial.algebraMap_eq] at hφ
          simpa using RingHom.congr_fun hφ a
        · simp
      have hc0 : φ.hom Polynomial.X ≠ 0 := by
        intro h0
        rw [← hpx] at hx
        apply (PrimeSpectrum.mem_basicOpen _ _).1 hx
        show φ.hom Polynomial.X ∈ IsLocalRing.maximalIdeal k
        rw [h0]; exact zero_mem _
      have e : Spec.map φ ≫ f = Spec.map φ ≫ f' := by
        rw [hf', reassoc_of% hp, hev]
        exact hc _ hc0
      rw [← hpx]
      exact congrArg (fun g : Sp k ⟶ Y => g (IsLocalRing.closedPoint k)) e
    · rw [hf', Category.assoc, Category.assoc, hq, hs1, Category.comp_id]
  have ha : ∀ a : Polynomial k →ₐ[k] k,
      spMap a.toRingHom ≫ f = spMap (Polynomial.evalRingHom (1 : k)) ≫ f := by
    intro a
    have hsa : spMap a.toRingHom ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ :=
      spMap_section _ (by
        ext x; have := a.commutes x; rw [Polynomial.algebraMap_eq] at this; simpa using this)
    conv_lhs => rw [key]
    rw [hf', reassoc_of% hsa]
  rw [ha a, ha b]

end GlobalTheory.ConstAffineLine
