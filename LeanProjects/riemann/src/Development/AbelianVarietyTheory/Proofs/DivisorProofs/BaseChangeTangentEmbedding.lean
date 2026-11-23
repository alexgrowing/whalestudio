import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsChartIndependence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingPointFiniteDescentStatement
open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts GlobalTheory.LieMet

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtDescent

open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open CategoryTheory.Limits

theorem dualMap_fst {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by
  show (TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) : DualNumber T).fst = _
  simp

theorem dualMap_snd {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by
  show (TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) : DualNumber T).snd = _
  simp

theorem descend_local_pt : ∀ {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] {T : Type} [CommRing T] [IsLocalRing T] (v : Spec (CommRingCat.of T) ⟶ X), ∃ s : Finset T, ∀ (S : Type) [CommRing S] (φ : S →+* T), Function.Injective φ → (↑s : Set T) ⊆ Set.range φ → ∃ w : Spec (CommRingCat.of S) ⟶ X, Spec.map (CommRingCat.ofHom φ) ≫ w = v := GlobalTheory.T.local_ring_point_finite_descent

theorem dualMap_eq_dualMapR {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) : dualMap φ = dualMapR φ := by
  apply RingHom.ext; intro x; ext <;> simp [dualMap, dualMapR]

theorem fd_fieldRange {A : Type} [Field A] [CharZero A] [FiniteDimensional ℚ A] (f : A →+* Qb) :
    FiniteDimensional ℚ f.toRatAlgHom.fieldRange := by
  let g : A →ₗ[ℚ] f.toRatAlgHom.fieldRange :=
    (f.toRatAlgHom.codRestrict f.toRatAlgHom.fieldRange.toSubalgebra (fun x => ⟨x, rfl⟩)).toLinearMap
  refine Module.Finite.of_surjective g ?_
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

theorem exists_descent : ∀ (D : D7) (O : Setup D) (y : Pt O.s) (K₀ : Type) [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (io : K →+* Qb) (j : K₀ →+* K) (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z) (hio : spMap io ≫ yK = y.y) (b : Pad.Letter O.S.Dw → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G), io.comp j = io₀ ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧ ∀ l, (tv (bcTan io (by rw [← Category.assoc, hio]) (b l))).left = y.u l.1 l.2 := by
  intro D O y K₀ _ _ io₀
  classical
  haveI hQ : IsAlgClosure ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgClosure ℚ ℂ
  haveI : Algebra.IsAlgebraic ℚ Qb := hQ.isAlgebraic
  haveI : IsProper O.s.T.Z.s := GlobalTheory.CommonModel.isProper_of_isProjOver O.s.T.Z.proj
  haveI : Smooth O.s.T.Z.t.G.hom := O.s.T.Z.t.semi.smooth
  obtain ⟨s₀, hs₀⟩ := descend_local_pt O.s.T.Z.s (y.y ≫ genι O.s.T.Z)
  choose s hs using fun l : Letter O.S.Dw => descend_local_pt (O.s.T.Z.t.G.hom ≫ O.s.T.Z.s) (y.u l.1 l.2)
  let A : Finset Qb := s₀ ∪ Finset.univ.biUnion
    (fun l => (s l).image TrivSqZeroExt.fst ∪ (s l).image TrivSqZeroExt.snd)
  let K : IntermediateField ℚ Qb :=
    IntermediateField.adjoin ℚ (A : Set Qb) ⊔ io₀.toRatAlgHom.fieldRange ⊔ y.fK.toRatAlgHom.fieldRange
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (A : Set Qb)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  haveI := fd_fieldRange io₀
  haveI := fd_fieldRange y.fK
  haveI : FiniteDimensional ℚ K := inferInstance
  haveI : NumberField K := { }
  have hl1 : IntermediateField.adjoin ℚ (A : Set Qb) ≤ K := le_sup_left.trans le_sup_left
  have hl2 : io₀.toRatAlgHom.fieldRange ≤ K := le_sup_right.trans le_sup_left
  have hl3 : y.fK.toRatAlgHom.fieldRange ≤ K := le_sup_right
  have hA : ∀ a ∈ A, a ∈ K := fun a ha => hl1 (IntermediateField.subset_adjoin ℚ _ ha)
  have h₀ : ∀ x, io₀ x ∈ K := fun x => hl2 ⟨x, rfl⟩
  have hF : ∀ x, y.fK x ∈ K := fun x => hl3 ⟨x, rfl⟩
  let io : K →+* Qb := algebraMap K Qb
  have hinj : Function.Injective io := Subtype.val_injective
  let j : K₀ →+* K := io₀.codRestrict K h₀
  let fK : O.κ.c.F →+* K := y.fK.codRestrict K hF
  have hj : io.comp j = io₀ := RingHom.ext fun _ => rfl
  have hfK : io.comp fK = y.fK := RingHom.ext fun _ => rfl
  haveI : Epi (spMap io) := GlobalTheory.TanDescent.epi_spMap_field io

  obtain ⟨xK, hxK⟩ := hs₀ K io hinj fun a ha => ⟨⟨a, hA a (Finset.mem_union_left _ ha)⟩, rfl⟩
  have hw : xK ≫ O.s.T.Z.s = spMap fK ≫ spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F) := by
    apply (cancel_epi (spMap io)).1
    have e1 : spMap io ≫ xK = y.y ≫ genι O.s.T.Z := hxK
    rw [← Category.assoc, e1, Category.assoc, genι, pullback.condition, ← Category.assoc]
    rw [show y.y ≫ pullback.snd _ _ = y.y ≫ genStr O.s.T.Z from rfl, y.y_over, ← hfK,
      ← GlobalTheory.TanDescent.sp_comp, Category.assoc]
  let yK : Sp K ⟶ gen O.s.T.Z := pullback.lift xK (spMap fK) hw
  have hio : spMap io ≫ yK = y.y := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]; exact hxK
    · rw [Category.assoc, pullback.lift_snd, GlobalTheory.TanDescent.sp_comp, hfK]
      exact y.y_over.symm
  have hyK : yK ≫ genStr O.s.T.Z = spMap fK := pullback.lift_snd _ _ _

  have hsub : ∀ l, (↑(s l) : Set (DualNumber Qb)) ⊆ Set.range (dualMap io) := by
    intro l d hd
    have h1 : d.fst ∈ K := hA _ (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨l, Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hd)⟩))
    have h2 : d.snd ∈ K := hA _ (Finset.mem_union_right _ (Finset.mem_biUnion.2
      ⟨l, Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hd)⟩))
    refine ⟨((⟨d.fst, h1⟩ : K), (⟨d.snd, h2⟩ : K)), ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_
    · exact dualMap_fst io _
    · exact dualMap_snd io _
  have hdinj : Function.Injective (dualMap io) := by
    intro a b h
    have h1 := congrArg TrivSqZeroExt.fst h
    have h2 := congrArg TrivSqZeroExt.snd h
    refine TrivSqZeroExt.ext ?_ ?_
    · exact hinj ((dualMap_fst io a).symm.trans (h1.trans (dualMap_fst io b)))
    · exact hinj ((dualMap_snd io a).symm.trans (h2.trans (dualMap_snd io b)))
  choose v hv using fun l : Letter O.S.Dw => hs l (DualNumber K) (dualMap io) hdinj (hsub l)
  have hT : ∀ l, IsTanAtG O.s.T.Z.t (yK ≫ genι O.s.T.Z) (v l) := fun l =>
    GlobalTheory.TanDescent.isTan_desc O.s.T.Z.t io (by
      rw [← dualMap_eq_dualMapR, ← Category.assoc, hio]
      have e2 := hv l
      erw [e2]
      exact y.tan l.1 l.2)
  refine ⟨K, inferInstance, inferInstance, io, j, fK, yK, hio, fun l => tanOf (hT l), hj, hyK, fun l => ?_⟩
  refine (left_bcTan _ _ _).trans ?_
  erw [left_tanOf]
  exact hv l

end GlobalTheory.PtDescent

end
