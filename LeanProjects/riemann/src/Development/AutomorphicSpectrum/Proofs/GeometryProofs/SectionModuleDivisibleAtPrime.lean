import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LeWchartOne
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv

theorem mem_map_of_mem_primes {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]
    (m : Ideal R) [hm : m.IsMaximal] (a : A)
    (h : ∀ P : Ideal A, P.IsPrime → m.map (algebraMap R A) ≤ P → a ∈ P) : a ∈ m.map (algebraMap R A) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have hr : _root_.IsReduced ((R ⧸ m) ⊗[R] A) := isReduced_of_smooth_alg (R ⧸ m) _
  have hr' : _root_.IsReduced (A ⊗[R] (R ⧸ m)) :=
    isReduced_of_injective (Algebra.TensorProduct.comm R A (R ⧸ m)).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm R A (R ⧸ m)).injective
  have hq : _root_.IsReduced (A ⧸ m.map (algebraMap R A)) :=
    isReduced_of_injective (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).toRingEquiv.toRingHom
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A m).injective
  have hrad : (m.map (algebraMap R A)).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hq
  refine hrad ?_
  rw [Ideal.radical_eq_sInf]
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨hP, hPp⟩
  exact h P hPp hP

theorem dvd_mul_of_mem_map {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (m : Ideal R) {c e : R}
    (h : ∀ π ∈ m, e ∣ c * π) {a : A} (ha : a ∈ m.map (algebraMap R A)) :
    algebraMap R A e ∣ algebraMap R A c * a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨π, hπ, rfl⟩ := hx
    rw [← map_mul]
    exact map_dvd _ (h π hπ)
  | zero => rw [MulZeroClass.mul_zero]; exact dvd_zero _
  | add x y _ _ hx hy => rw [mul_add]; exact dvd_add hx hy
  | smul t x _ hx => rw [smul_eq_mul, mul_left_comm]; exact hx.mul_left _

theorem mem_basicOpen_map {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem mem_basicOpen_top_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) :
    x ∈ X.basicOpen ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  have hmem : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    have e := basicOpen_eq_of_affine (R := CommRingCat.of R) r
    exact (congrArg (fun U : (Sp R).Opens => p x ∈ U) e).mpr hx
  rw [← Scheme.preimage_basicOpen]
  exact hmem

theorem isUnit_cst_of_notMem (p : X ⟶ Sp R) (x : X) {r : R} (hx : r ∉ (p x).asIdeal) : IsUnit (cst p x r) := by
  have hu := (Scheme.mem_basicOpen X ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) x
    (show x ∈ p ⁻¹ᵁ ⊤ from trivial)).1 (mem_basicOpen_top_of_notMem p x hx)
  rw [cst, gs_eq p x ⊤ (show p x ∈ (⊤ : (Sp R).Opens) from trivial)]
  exact hu

theorem cst_mul (p : X ⟶ Sp R) (x : X) (a b : R) : cst p x (a * b) = cst p x a * cst p x b := by
  simp only [cst, map_mul]
  exact gs_mul p x ⊤ trivial _ _

theorem exists_smul_eq_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  intro R _ _ X p _ M b hb u hu c e he hdiv
  have key : ∀ j, ∀ x ∈ M.U j, cst p x e ∣ gs (𝟙 X) x (M.U j) (LB.Sec.f (c • u : SecMod p M) j) := by
    intro j x hx
    rw [smul_f, gs_mul _ x _ hx, gs_constFn p _ _ x hx, Category.id_comp]
    by_cases hxb : b.asIdeal ≤ (p x).asIdeal
    ·
      obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := M.U j) (x := x) hx
      have hle : V ≤ M.U j := hVU
      have sm := HasRingHomProperty.appLE @Smooth p ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
      have sm' : RingHom.Smooth ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
        RingHom.Smooth.comp
          (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) sm
      letI := ((p.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).toAlgebra
      have : Algebra.Smooth R Γ(X, V) := sm'
      have hconst : ∀ r : R, algebraMap R Γ(X, V) r = constFn p V r := fun _ => rfl
      have hmem : (X.presheaf.map (homOfLE hle).op).hom (LB.Sec.f u j) ∈ b.asIdeal.map (algebraMap R Γ(X, V)) := by
        have := hb
        refine mem_map_of_mem_primes b.asIdeal _ fun P hP hbP => ?_
        let y : X := hV.fromSpec (⟨P, hP⟩ : PrimeSpectrum Γ(X, V))
        have hbo : ∀ f : Γ(X, V), y ∈ X.basicOpen f ↔ f ∉ P := fun f => by
          have e := hV.fromSpec_preimage_basicOpen f
          have e' := congrArg (fun O : (Spec Γ(X, V)).Opens => (⟨P, hP⟩ : PrimeSpectrum Γ(X, V)) ∈ O) e
          exact iff_of_eq e'
        have hyV : y ∈ V := by
          have h4 : y ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
          rw [hV.range_fromSpec] at h4
          exact h4
        have hcl : p y = b := by
          have hle' : b.asIdeal ≤ (p y).asIdeal := fun π hπ => by
            by_contra hn
            have h2 := mem_basicOpen_top_of_notMem p y hn
            have h3 : y ∈ X.basicOpen (constFn p V π) := by
              have e : constFn p V π = (X.presheaf.map (homOfLE le_top).op).hom
                  ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)) := rfl
              rw [e]
              exact (mem_basicOpen_map le_top _ y).2 ⟨hyV, h2⟩
            exact (hbo _).1 h3 (hbP (Ideal.mem_map_of_mem _ hπ))
          exact PrimeSpectrum.ext (hb.eq_of_le (p y).isPrime.ne_top hle').symm
        by_contra hn
        have h1 := (hbo _).2 hn
        exact hu y hcl (TopologicalSpace.Opens.mem_iSup.2 ⟨j, ((mem_basicOpen_map hle _ y).1 h1).2⟩)
      obtain ⟨t, ht⟩ := dvd_mul_of_mem_map b.asIdeal hdiv hmem
      refine ⟨gs (𝟙 X) x V t, ?_⟩
      have e' := congrArg (gs (𝟙 X) x V) ht
      rw [hconst, hconst, gs_mul _ x _ hxV, gs_mul _ x _ hxV, gs_constFn p _ _ x hxV, gs_constFn p _ _ x hxV,
        gs_res _ x _ hxV, Category.id_comp] at e'
      exact e'
    ·
      obtain ⟨π, hπ, hπx⟩ := Set.not_subset.1 hxb
      have hunit := isUnit_cst_of_notMem p x hπx
      obtain ⟨t, ht⟩ := hdiv π hπ
      have h1 : cst p x e ∣ cst p x c * cst p x π := by
        rw [← cst_mul, ht, cst_mul]
        exact dvd_mul_right _ _
      exact ((hunit.dvd_mul_right).1 h1).mul_right _
  obtain ⟨s', hs'⟩ := exists_div_sec p he (show LB.Sec M from (c • u : SecMod p M)) key
  exact ⟨s', SecMod.ext fun j => (hs' j).symm⟩

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv
