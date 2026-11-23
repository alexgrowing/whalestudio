import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionCoordinateVectorExistsLocallyStatement
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.DenseFib

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) :
    ∃ φ : A →+* B, spMap φ = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eval₂_scale {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eq_zero_of_dense {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by
  by_contra ha
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)).Nonempty := by
    by_contra hn
    refine ha (IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff a).1 ?_))
    exact eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim
  obtain ⟨q, hqa, hqD⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hne
  let q' : PrimeSpectrum A := q
  let K := AlgebraicClosure q'.asIdeal.ResidueField
  let κ : A →+* K := (algebraMap q'.asIdeal.ResidueField K).comp (algebraMap A _)
  have hker : ∀ z, κ z = 0 ↔ z ∈ q'.asIdeal := fun z => by
    simp only [κ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap q'.asIdeal.ResidueField K).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  have h0 := h K κ (by
    rintro _ ⟨p, rfl⟩
    have : spMap κ p = q := by
      apply PrimeSpectrum.ext
      ext z
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := p.isPrime)
      change κ z ∈ p.asIdeal ↔ z ∈ q'.asIdeal
      rw [hp, ← hker]; rfl
    rwa [this])
  exact hqa ((hker a).1 h0)

theorem mem_idealOf_of_dense : ∀ (R σ : Type) [CommRing R] (Y : Scheme.{0}) (s : Y ⟶ Sp R) (N : LB Y) (ty : σ → N.Sec) (Sg : Set (Sp R)) (F : MvPolynomial σ R) (e : ℕ), IsReduced Y → Flat s → LocallyOfFinitePresentation s → N.IsLB → Dense Sg → F.IsHomogeneous e → (∀ (K : Type) [Field K] [IsAlgClosed K] (β : R →+* K) (y : Sp K ⟶ Y) (v : σ → K), y ≫ s = spMap β → Set.range (spMap β) ⊆ Sg → SecCoord N ty y v → MvPolynomial.eval₂ β v F = 0) → F ∈ idealOf s N ty (𝟙 Y) := by
  intro R σ _ Y s N ty Sg F e hred hflat hlfp hN hSg hF H
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id]
  rintro R' _ β y v ⟨hy, hv⟩
  refine eq_zero_of_localization _ fun J hJ => ?_
  let L := Localization.AtPrime J
  let φ : R' →+* L := algebraMap R' L
  let yL : Sp L ⟶ Y := spMap φ ≫ y
  obtain ⟨A, _, x, w, hx, hp, hw⟩ := (GlobalTheory.T.sectionCoordinateVector_exists_locally Y N σ ty hN).2.2 (yL (IsLocalRing.closedPoint L))
  have hrange : Set.range yL ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := L) p).map yL.continuous).mem_open
      x.isOpenEmbedding.isOpen_range hp
  obtain ⟨ψ, hψ⟩ := exists_spMap (IsOpenImmersion.lift x yL hrange)
  have hψx : spMap ψ ≫ x = yL := by rw [hψ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := exists_spMap (x ≫ s)
  have hcomp : ψ.comp α = φ.comp β := by
    apply spMap_inj
    rw [← sp_comp, ← sp_comp, hα, ← Category.assoc, hψx, ← hy, Category.assoc]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 L ψ
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty R' y v hN hv).1 L φ
  rw [hψx] at h1
  obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty L yL _ hN h1).2.2 _ h2
  have hredA : IsReduced (Sp A) := isReduced_of_isOpenImmersion x
  have hredA' : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 hredA
  have hD : Dense ((x ≫ s) ⁻¹' Sg) := hSg.preimage (x ≫ s).isOpenMap
  have hA : MvPolynomial.eval₂ α w F = 0 := by
    refine eq_zero_of_dense _ hD _ fun K _ _ κ hκ => ?_
    rw [MvPolynomial.eval₂_comp_left]
    refine H K (κ.comp α) (spMap κ ≫ x) _ ?_ ?_
      ((GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 K κ)
    · rw [Category.assoc, ← hα, sp_comp]
    · rintro _ ⟨p, rfl⟩
      rw [← sp_comp, hα, Scheme.Hom.comp_apply]
      exact hκ ⟨p, rfl⟩
  change φ (MvPolynomial.eval₂ β v F) = 0
  rw [MvPolynomial.eval₂_comp_left, ← hcomp]
  have : (φ ∘ v) = fun i => (u : L) * (ψ ∘ w) i := funext hu
  rw [this, eval₂_scale _ _ _ hF, ← MvPolynomial.eval₂_comp_left, hA, map_zero, mul_zero]

end GlobalTheory.ZM.DenseFib
