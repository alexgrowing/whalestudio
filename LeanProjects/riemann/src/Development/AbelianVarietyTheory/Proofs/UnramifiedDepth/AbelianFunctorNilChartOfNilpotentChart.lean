import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f φ) {Z : Scheme.{0}}
    (t' : Z ⟶ S') (t : Z ⟶ S) (ht : t' ≫ f = t) :
    ∃ P : (Over.mk t' ⟶ G') →* (Over.mk t ⟶ G), (∀ x, (P x).left = x.left ≫ φ) ∧ Function.Bijective P := by
  subst ht
  let p : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      have := Over.w x
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, h.1.w, ← Category.assoc, this])
  refine ⟨MonoidHom.mk' p fun x y => Over.OverMorphism.ext (h.2 (Over.mk t') x y (p x) (p y) rfl rfl).symm,
    fun _ => rfl, fun x y hxy => ?_, fun z => ?_⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  · refine ⟨Over.homMk (h.1.lift z.left t' (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _

private theorem spec_comp {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact s.1.comp_algebraMap

theorem bxChart_of_nilChart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  intro R₀ _ G _ _ B e hb hm hn O G' _ _ φ hφ g F X hX
  have h0 : ∀ R, e R 0 = 1 := fun R => by
    have := hm R 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  choose P hP hPb using fun (R : LAlg R₀) (s : LHom O R) => exists_push hφ _ _ (spec_comp s)
  let X' : ∀ R : LAlg R₀, ∀ s : LHom O R, (Fin g → (R : Type)) →
      (Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') := fun R s a =>
    @X R _ s.1.toRingHom.toAlgebra a
  choose Y hY using fun (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) => (hb R).2 (P R s (X' R s a))
  have hYl : ∀ R s a, (e R (Y R s a)).left = (X' R s a).left ≫ φ := fun R s a => by rw [hY, hP]
  refine ⟨Y, ⟨fun R s => ?_, fun R R' s f a ha => ?_, fun R s a b ha hb' hab => ?_,
    fun R S s π σ hπσ hσ hπ x hx => ?_, fun R s a b ha hb' => ?_⟩, fun f α A hr hA R s a ha => ?_⟩
  · apply (hb R).1
    rw [hY, h0]
    letI := s.1.toRingHom.toAlgebra
    have : X' R s 0 = 1 := hX.zero R
    rw [this, map_one]
  · apply (hb R').1
    apply Over.OverMorphism.ext
    rw [hn, Over.comp_left, hYl, hYl]
    letI := s.1.toRingHom.toAlgebra
    letI := (f.comp s).1.toRingHom.toAlgebra
    let f' : (R : Type) →ₐ[(O : Type)] (R' : Type) := ⟨f.1.toRingHom, fun _ => rfl⟩
    have := congrArg (fun z => z.left ≫ φ) (hX.nat R R' f' a ha)
    exact (Category.assoc _ _ _).symm.trans this
  · letI := s.1.toRingHom.toAlgebra
    refine hX.inj R a b ha hb' ((hPb R s).1 ?_)
    exact (hY R s a).symm.trans ((congrArg (e R) hab).trans (hY R s b))
  · obtain ⟨z, hz⟩ := (hPb R s).2 (e R x)
    letI := s.1.toRingHom.toAlgebra
    letI := (π.comp s).1.toRingHom.toAlgebra
    let ρ : (R : Type) →ₐ[(O : Type)] (S : Type) := ⟨π.1.toRingHom, fun _ => rfl⟩
    let σ' : (S : Type) →ₐ[(O : Type)] (R : Type) :=
      ⟨σ.1.toRingHom, fun r => congrArg (fun u : LHom O R => u.1 r) hσ⟩
    have h1 : ρ.comp σ' = AlgHom.id _ _ := AlgHom.ext fun r => congrArg (fun u : LHom S S => u.1 r) hπσ
    have h2 : IsNilpotent (RingHom.ker ρ) := ⟨2, hπ.2⟩
    have h3 : spMap ρ ≫ z = 1 := by
      apply (hPb S (π.comp s)).1
      refine Eq.trans ?_ (map_one (P S (π.comp s))).symm
      rw [← h0, ← hx, hn, ← hz]
      apply Over.OverMorphism.ext
      rw [hP, Over.comp_left, Over.comp_left, hP]
      exact Category.assoc _ _ _
    obtain ⟨a, ha, hza⟩ := hX.surj R S ρ σ' h1 h2 z h3
    refine ⟨a, ha, (hb R).1 ?_⟩
    rw [hY, ← hz, hza]
  · apply (hb R).1
    letI := s.1.toRingHom.toAlgebra
    rw [hm, hY, hY, hY, ← map_mul]
    exact congrArg (P R s) (hX.law R a b ha hb')
  · apply (hb R).1
    apply Over.OverMorphism.ext
    letI := s.1.toRingHom.toAlgebra
    rw [← hA s (Y R s a) (X' R s a) (hYl R s a).symm, hYl]
    exact congrArg (fun z => z.left ≫ φ) (hr.2 R a ha)

end GlobalTheory.ChF
