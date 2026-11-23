import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntLatGEqCanLatOfSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS GlobalTheory.LogDR GlobalTheory.CanExtM
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLocalBasis

theorem exists_isLieBasis_of_isLocalRing : ∀ (R : Type) [CommRing R] [IsLocalRing R] (B : Over (Sp R)) [GrpObj B]
    [IsCommMonObj B], Smooth B.hom → ∃ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y := by
  intro R _ _ B _ _ hs
  haveI := hs
  obtain ⟨C⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_chart B
  obtain ⟨g, hg, n, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_lieBasis_away C (IsLocalRing.maximalIdeal R)
  have hu : IsUnit g := by
    by_contra h
    exact hg ((IsLocalRing.mem_maximalIdeal g).2 h)
  let L := Localization.Away g
  let f' : L →+* R := IsLocalization.Away.lift (g := RingHom.id R) g hu
  have hf' : f'.comp (algebraMap R L) = RingHom.id R := RingHom.ext fun r => IsLocalization.Away.lift_eq (g := RingHom.id R) g hu r
  let G' := ReciprocityTheory.ChartRestriction.G.Chart.Gs B g
  have hpb : IsGrpPullback G' B (ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (pullback.fst B.hom _) :=
    isGrpPullback_pullback B _
  have hcomp : spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L = 𝟙 (Sp R) := by
    simp only [spMap, ReciprocityTheory.ChartRestriction.G.Chart.fB]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf']
    exact Spec.map_id _
  let φ' : B.left ⟶ G'.left := pullback.lift (𝟙 _) (B.hom ≫ spMap f') (by rw [Category.assoc, hcomp]; simp)
  have hφ : φ' ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _
  have hw : φ' ≫ G'.hom = B.hom ≫ spMap f' := pullback.lift_snd _ _ _
  haveI : IsMonHom (Iso.refl B).hom := inferInstanceAs (IsMonHom (𝟙 B))
  have hid : IsGrpPullback B B (𝟙 (Sp R)) (𝟙 B.left) := (isGrpPullback_of_iso (Iso.refl B)).congr rfl rfl
  have hn : IsGrpPullback B B (spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Chart.fB R L) (φ' ≫ pullback.fst _ _) :=
    hid.congr hcomp.symm hφ.symm
  have hB : IsGrpPullback B G' (spMap f') φ' := hpb.cancel hn hw
  have hs' : Smooth G'.hom := by
    show Smooth (pullback.snd B.hom _)
    infer_instance
  obtain ⟨v', hv', -⟩ := GlobalTheory.exists_isLieBasis_baseChange L R f' G' B φ' hB hs' n v hv
  exact ⟨n, v', hv'⟩

end GlobalTheory.LieLocalBasis
