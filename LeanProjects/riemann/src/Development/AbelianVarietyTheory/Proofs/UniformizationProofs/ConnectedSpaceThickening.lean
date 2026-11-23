import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusHomPullbackLocalTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory

namespace EndTorus

theorem idempotent_trivial {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) [IsAdicComplete I R]
    (e : ℕ) (x : R ⧸ I ^ (e + 1)) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hle : I ^ (e + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero e)
  have h0 : a₀ * a₀ - a₀ ∈ I := hle (Ideal.Quotient.eq.1 hx)
  have hm : (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic := by monicity!
  obtain ⟨a, ha, hI⟩ := HenselianRing.is_henselian (I := I) _ hm a₀ (by simpa [sq] using h0) (by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (2 * a₀ - 1)) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    convert I.mul_mem_left 4 h0 using 1
    simp
    ring)
  have hnil : ∀ y ∈ I, IsNilpotent (Ideal.Quotient.mk (I ^ (e + 1)) y) := fun y hy =>
    ⟨e + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hy _)⟩
  have ha' : a * (a - 1) = 0 := by
    have := ha.eq_zero
    simp at this
    linear_combination this
  rcases mul_eq_zero.1 ha' with h | h
  · left
    refine hx.eq_zero_of_isNilpotent (hnil _ ?_)
    simpa [h] using hI
  · right
    have h1 : a = 1 := sub_eq_zero.1 h
    have := hx.one_sub.eq_zero_of_isNilpotent (by simpa [h1] using hnil _ hI)
    exact (sub_eq_zero.1 this).symm

theorem connectedSpace_thickening {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)
    [hC : IsAdicComplete I R] (e : ℕ) : ConnectedSpace (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := by
  have hI : I ≠ ⊤ := by
    rintro rfl
    have : Subsingleton R := IsHausdorff.subsingleton hC.toIsHausdorff
    exact false_of_nontrivial_of_subsingleton R
  have hJ : I ^ (e + 1) ≠ ⊤ := fun h =>
    hI (top_le_iff.1 (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))
  have : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hJ
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))) := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨x, hx, rfl⟩ := PrimeSpectrum.isClopen_iff.1 hU
    rcases idempotent_trivial I e x hx with rfl | rfl <;> simp
  exact ({ toNonempty := inferInstance } : ConnectedSpace (PrimeSpectrum (R ⧸ I ^ (e + 1))))

theorem torusEndOf_iff_appTop {S : Scheme.{0}} {X : Type} [AddCommGroup X] (h : X → X)
    (t : splitTorus S X ⟶ splitTorus S X) : TorusEndOf X h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem isMonHom_of_mono {S : Scheme.{0}} {A B C : Over S} [MonObj A] [MonObj B] [MonObj C]
    (t : A ⟶ B) (i : B ⟶ C) [Mono i] [IsMonHom i] [IsMonHom (t ≫ i)] : IsMonHom t := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc]

end EndTorus

open EndTorus in

theorem gtCoord_end_torus_abelian : LL → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G), IsMonHom a → (∃! h : D.X →+ D.X, ∃ t, TorusEndOf D.X h t ∧ g.i ≫ a = t ≫ g.i) ∧ ∃! b : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A, IsMonHom b ∧ a ≫ g.q = g.q ≫ b := by
  intro _ R _ _ I hR D e G _ _ g a ha
  obtain ⟨hN, -, -, hC⟩ := hR
  have := connectedSpace_thickening I e
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have hB : IsAbelianScheme (thickObj R I e D.P.A) :=
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }
  have h1 : g.i ≫ a ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] :=
    (splitTorus_hom_abelian_eq_one _ D.X _ hB (g.i ≫ a ≫ g.q) inferInstance).trans (Hom.one_def)
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  constructor
  · let t := hk.lift (g.i ≫ a) (toUnit _) (by rw [Category.assoc, h1])
    have ht : t ≫ g.i = g.i ≫ a := hk.lift_fst _ _ _
    have : IsMonHom (t ≫ g.i) := ht ▸ inferInstance
    have : IsMonHom t := isMonHom_of_mono t g.i
    obtain ⟨h, hh⟩ := SplitTorusHom.exists_addMonoidHom t
    refine ⟨h, ⟨t, (torusEndOf_iff_appTop _ _).2 hh, ht.symm⟩, ?_⟩
    rintro h' ⟨t', h₁, h₂⟩
    obtain rfl : t' = t := by rw [← cancel_mono g.i, ht, h₂]
    ext χ
    exact SplitTorusHom.charUnit_injective (S := Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (((torusEndOf_iff_appTop _ _).1 h₁ χ).symm.trans (hh χ))
  · obtain ⟨b, hb, hq⟩ := FlatQuotient.exists_desc g.q g.i (a ≫ g.q) hk h1
    have := FlatQuotient.epi_of_flat_surjective g.q
    refine ⟨b, ⟨hb, hq.symm⟩, ?_⟩
    rintro b' ⟨-, h⟩
    rw [← cancel_epi g.q, ← h, hq]

end GlobalTheory
