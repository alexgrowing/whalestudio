import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

theorem existsUnique_smul_of_basis {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [Subsingleton κ]
    (c : Module.Basis κ R M) (k : κ) (s : M) : ∃! r : R, s = r • c k := by
  have := uniqueOfSubsingleton k
  obtain rfl : k = default := Subsingleton.elim _ _
  refine ⟨c.repr s default, ?_, fun r hr => ?_⟩
  · have e := c.sum_repr s
    rw [Fintype.sum_unique] at e
    exact e.symm
  · rw [hr]; simp

theorem exists_univBasis_field (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K]
    (y : Sp K ⟶ S) : ∃ b : SecM P.A P.L ((1 : ℕ) : ℤ) (Over.mk y), ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ Over.mk y)
      (s : SecM P.A P.L ((1 : ℕ) : ℤ) T), ∃! c : Γ(T.left, ⊤), s = c • VVRank.pullM P.A P.L _ h b := by
  obtain ⟨V, hV, b, hb⟩ := ThetaReal.exists_univBasis hS P 1 le_rfl (y (closedPoint K))
  have hr : Set.range y ⊆ Set.range V.ι := by
    rintro _ ⟨q, rfl⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    rw [Subsingleton.elim q (closedPoint K)]
    exact ⟨⟨_, hV⟩, rfl⟩
  let u : Over.mk y ⟶ overRes (T := baseOver S) V := Over.homMk (IsOpenImmersion.lift V.ι y hr)
    ((congrArg (_ ≫ ·) (Category.comp_id V.ι)).trans (IsOpenImmersion.lift_fac V.ι y hr))
  have h1 : 1 ^ P.g = 1 := one_pow _
  let k₀ : Fin (1 ^ P.g) := Fin.cast h1.symm 0
  have : Subsingleton (Fin (1 ^ P.g)) := ⟨fun a a' => Fin.ext (by have := a.2; have := a'.2; omega)⟩
  refine ⟨VVRank.pullM P.A P.L _ u (b k₀), fun T _ h s => ?_⟩
  obtain ⟨c, hc⟩ := hb T (h ≫ u)
  rw [VVRank.pullM_comp _ P.isLB, ← hc]
  exact existsUnique_smul_of_basis c k₀ s

theorem exists_univBasis_of_fibre : Laws2 → ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (P : PolAV S') (f : S' ⟶ S) (φ : P.A.left ⟶ G.left), IsGrpPullback P.A G f φ → LBIso P.L (L.pull φ) →
    ∀ (K : Type) [Field K] (y : Sp K ⟶ S') (x : Sp K ⟶ S), y ≫ f = x → ∃ e, UnivBasis G L x e := by
  intro hL S S' G _ L hL₀ P f φ hp hw K _ y x hx
  obtain ⟨w, hw⟩ := hw
  obtain ⟨b, hb⟩ := exists_univBasis_field hL.secBaseChangeAny P y
  have hτ : (𝟙 (Sp K) : (Over.mk y).left ⟶ (Over.mk x).left) ≫ (Over.mk x).hom = (Over.mk y).hom ≫ f :=
    (Category.id_comp _).trans hx.symm
  have : IsIso (C := Scheme.{0}) (X := (Over.mk y).left) (Y := (Over.mk x).left) (𝟙 (Sp K)) := IsIso.id _
  obtain ⟨e, he⟩ := UnivBasisMove.exists_rel_up hp (T := Over.mk y) (T₀ := Over.mk x) (𝟙 (Sp K)) hτ hw hL₀ P.isLB b
  refine ⟨SecM.toSec G e, fun K' _ i x' h s => ?_⟩
  obtain rfl : (spMap i ≫ y) ≫ f = x' := by rw [Category.assoc, hx, h]
  let T : Over S' := Over.mk (spMap i ≫ y)
  have : IsAffine T.left := inferInstanceAs (IsAffine (Spec _))
  obtain ⟨E, hE⟩ := UnivBasisMove.exists_linearEquiv hp hw hL₀ P.isLB ((1 : ℕ) : ℤ) T
  let u : T ⟶ Over.mk y := Over.homMk (spMap i) rfl
  let u₀ : Over.mk (T.hom ≫ f) ⟶ Over.mk x := Over.homMk (spMap i) h
  have key : E (VVRank.pullM G L _ u₀ e) = VVRank.pullM P.A P.L _ u b :=
    (hE _).unique_down hL₀ P.isLB (he.pull _ _ u u₀ ((Category.id_comp _).trans (Category.comp_id _).symm))
  obtain ⟨c, hc, hu⟩ := hb T u (E s)
  refine ⟨c, E.injective (hc.trans ?_), fun r hr => hu r ?_⟩
  · rw [← key]
    exact (E.map_smul c _).symm
  · rw [← key]
    exact (congrArg E hr).trans (E.map_smul r _)

end GlobalTheory.Ex.OneGen
end
