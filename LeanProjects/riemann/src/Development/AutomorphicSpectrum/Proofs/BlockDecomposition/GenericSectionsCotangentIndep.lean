import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.InterNumEqSumLengthMulInterNumRed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodStalks
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel GlobalTheory.QCoh
open IsLocalRing
open GlobalTheory.CompanionTheory.KoszulCount
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KoszulCount

theorem cotangent_independent_unit_mul {R : Type} [CommRing R] [IsLocalRing R] {d : ℕ}
    (a a' : Fin d → R) (w : Rˣ) (h : ∀ j, a' j = w * a j)
    (hl : LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R))) :
    LinearIndependent (ResidueField R) (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) := by
  classical
  have hmem : ∀ j, a' j ∈ maximalIdeal R ↔ a j ∈ maximalIdeal R := fun j => by
    rw [h j]; exact Ideal.unit_mul_mem_iff_mem _ w.isUnit
  let e : {j : Fin d // a j ∈ maximalIdeal R} ≃ {j : Fin d // a' j ∈ maximalIdeal R} :=
    Equiv.subtypeEquivRight (fun j => (hmem j).symm)
  have hu : IsUnit (IsLocalRing.residue R (w : R)) := w.isUnit.map _
  have key : (fun j : {j : Fin d // a' j ∈ maximalIdeal R} =>
      ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) =
      (fun j => hu.unit • ((maximalIdeal R).toCotangent ⟨_, (e.symm j).2⟩ : CotangentSpace R)) := by
    funext j
    obtain ⟨j, hj⟩ := j
    have hj' : a j ∈ maximalIdeal R := (hmem j).1 hj
    have hsub : (⟨a' j, hj⟩ : maximalIdeal R) = (w : R) • (⟨a j, hj'⟩ : maximalIdeal R) :=
      Subtype.ext (by simp [h j])
    show (maximalIdeal R).toCotangent ⟨a' j, hj⟩ = hu.unit • (maximalIdeal R).toCotangent ⟨a j, hj'⟩
    rw [hsub, map_smul, Units.smul_def, IsUnit.unit_spec, ← IsLocalRing.ResidueField.algebraMap_eq,
      algebraMap_smul]
  rw [key]
  exact (hl.units_smul (fun _ => hu.unit)).comp e.symm e.symm.injective

theorem germ_chart_eq {X : Scheme.{0}} {L : LB X} (s : L.Sec) (i c : L.ι) {x : X}
    (hi : x ∈ L.U i) (hc : x ∈ L.U c) :
    X.presheaf.germ (L.U i) x hi (s.f i) =
      X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩ (L.g i c : Γ(X, L.U i ⊓ L.U c)) *
        X.presheaf.germ (L.U c) x hc (s.f c) := by
  have e1 := congrArg (X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩) (s.compat i c)
  rw [map_mul] at e1
  have r1 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_left : L.U i ⊓ L.U c ⟶ L.U i).op (s.f i)) =
      X.presheaf.germ (L.U i) x hi (s.f i) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_left) x ⟨hi, hc⟩ (s.f i)
  have r2 : X.presheaf.germ (L.U i ⊓ L.U c) x ⟨hi, hc⟩
      (X.presheaf.map (homOfLE inf_le_right : L.U i ⊓ L.U c ⟶ L.U c).op (s.f c)) =
      X.presheaf.germ (L.U c) x hc (s.f c) :=
    X.presheaf.germ_res_apply (homOfLE inf_le_right) x ⟨hi, hc⟩ (s.f c)
  rw [← r1, ← r2]
  exact e1

theorem sum_smul_f {X : Scheme.{0}} {L : LB X} {n : ℕ} (a : Fin n → Γ(X, ⊤)) (b : Fin n → L.Sec)
    (c : L.ι) : (∑ p, a p • b p).f c = ∑ p, resG X le_top (a p) * (b p).f c := by
  let φ : L.Sec →+ Γ(X, L.U c) :=
    { toFun := fun s => s.f c, map_zero' := rfl, map_add' := fun _ _ => rfl }
  exact (map_sum φ (fun p => a p • b p) Finset.univ).trans (Finset.sum_congr rfl fun p _ => rfl)

theorem resG_algebraMap (Y : Var ℂ) (V : Y.X.Opens) (a : ℂ) :
    resG Y.X (le_top : V ≤ ⊤) (algebraMap ℂ Γ(Y.X, ⊤) a) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V a := by
  rfl

theorem algX_smooth (Y : Var ℂ) {V : Y.X.Opens} (hV : IsAffineOpen V) :
    (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).Smooth := by
  haveI := Y.smooth_str
  have hsm : Smooth Y.str := SmoothOfRelativeDimension.smooth Y.dim Y.str
  have e : V ≤ Y.str ⁻¹ᵁ ⊤ := by simp
  have happ := HasRingHomProperty.appLE @Smooth Y.str hsm ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ e
  have heq : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V =
      (Y.str.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    ext a
    rw [← resG_algebraMap, GlobalTheory.ProjVar.Var.algebraMap_Γ]
    rfl
  rw [heq]
  exact (RingHom.Smooth.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv
    (Y.str.appLE ⊤ V e)).mpr happ

theorem bertini_on_affine (Y : Var ℂ) (L : LB Y.X) (n d : ℕ) (b : Fin n → L.Sec) (c : L.ι)
    {V : Y.X.Opens} (hV : IsAffineOpen V) (hVc : V ≤ L.U c) :
    ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧
      ∀ u : Fin d × Fin n → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (x : Y.X) (hx : x ∈ V), (∃ p, x ∈ nonzeroLocus (b p)) →
        LinearIndependent (ResidueField (Y.X.presheaf.stalk x))
          (fun j : {j : Fin d // Y.X.presheaf.germ (L.U c) x (hVc hx)
              ((∑ p, algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)) • b p).f c) ∈
                maximalIdeal (Y.X.presheaf.stalk x)} =>
            ((maximalIdeal (Y.X.presheaf.stalk x)).toCotangent ⟨_, j.2⟩ :
              CotangentSpace (Y.X.presheaf.stalk x))) := by
  classical
  letI : Algebra ℂ Γ(Y.X, V) := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V).toAlgebra
  haveI : Algebra.Smooth ℂ Γ(Y.X, V) := algX_smooth Y hV
  obtain ⟨Q, hQ, hQu⟩ := GlobalTheory.bertini_cotangent_independent ℂ Γ(Y.X, V)
    (fun p : Fin n => resG Y.X hVc ((b p).f c)) d
  refine ⟨Q, hQ, fun u hu x hx hnz => ?_⟩
  have hgres : ∀ {U W : Y.X.Opens} (h : W ≤ U) (hxW : x ∈ W) (z : Γ(Y.X, U)),
      Y.X.presheaf.germ W x hxW (resG Y.X h z) = Y.X.presheaf.germ U x (h hxW) z :=
    fun h hxW z => Y.X.presheaf.germ_res_apply (homOfLE h) x hxW z
  have hgs : ∀ {U : Y.X.Opens} (hxU : x ∈ U) (z : Γ(Y.X, U)),
      gs (𝟙 Y.X) x U z = Y.X.presheaf.germ U x hxU z := by
    intro U hxU z
    simp [gs, hxU]
    rfl
  let x' : V := ⟨x, hx⟩
  let q := (hV.primeIdealOf x').asIdeal
  letI : Algebra Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) :=
    TopCat.Presheaf.algebra_section_stalk Y.X.presheaf x'
  haveI := hV.isLocalization_stalk x'
  have hf : ∃ p, resG Y.X hVc ((b p).f c) ∉ q := by
    obtain ⟨p, hp⟩ := hnz
    obtain ⟨k, hk, hunit⟩ := (mem_nonzeroLocus (b p) x).1 hp
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.gs_sec L (b p) k c x hk (hVc hx)] at hunit
    have hu2 : IsUnit (Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c)) := by
      rw [← hgs (hVc hx)]; exact isUnit_of_mul_isUnit_right hunit
    refine ⟨p, fun hmem => ?_⟩
    have h0 := (GlobalTheory.residue_algebraMap_eq_zero_iff_mem (R := Y.X.presheaf.stalk (x' : Y.X)) q _).2 hmem
    have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
        Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
    rw [e2, IsLocalRing.residue_eq_zero_iff] at h0
    exact h0 hu2
  have hLI := hQu u hu q (Y.X.presheaf.stalk (x' : Y.X)) hf
  refine cotangent_independent_unit_mul _ _ 1 (fun j => ?_) hLI
  rw [Units.val_one, one_mul, sum_smul_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Algebra.smul_def, map_mul, map_mul]
  have e1 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (algebraMap ℂ Γ(Y.X, V) (u (j, p))) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) (resG Y.X le_top (algebraMap ℂ Γ(Y.X, ⊤) (u (j, p)))) := by
    show Y.X.presheaf.germ V x hx (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX Y.str V (u (j, p))) = _
    rw [← resG_algebraMap, hgres, hgres]
  have e2 : algebraMap Γ(Y.X, V) (Y.X.presheaf.stalk (x' : Y.X)) (resG Y.X hVc ((b p).f c)) =
      Y.X.presheaf.germ (L.U c) x (hVc hx) ((b p).f c) := hgres hVc hx _
  rw [e1, e2]

theorem bertini_cotIndep : ∀ (Y : Var ℂ) (L : LB Y.X), L.IsLB → ∀ (n d : ℕ) (b : Fin n → L.Sec), (⨆ j, nonzeroLocus (b j) = ⊤) → ∃ Q : MvPolynomial (Fin d × Fin n) ℂ, Q ≠ 0 ∧ ∀ C : Fin d → Fin n → ℂ, MvPolynomial.eval (fun p => C p.1 p.2) Q ≠ 0 → CotIndep (fun k => ∑ j, algebraMap ℂ Γ(Y.X, ⊤) (C k j) • b j) := by
  intro Y L hL n d b hb
  classical
  haveI : CompactSpace Y.X := (Var.isNoetherian_X Y).toCompactSpace
  obtain ⟨m, V, c, hVa, hVc, hcov⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_affine_chart_cover L hL
  choose Q hQ hQu using fun k : Fin m => bertini_on_affine Y L n d b (c k) (hVa k) (hVc k)
  refine ⟨∏ k, Q k, Finset.prod_ne_zero_iff.2 fun k _ => hQ k, fun C hC => ?_⟩
  intro x i hx
  have hCk : ∀ k, MvPolynomial.eval (fun p => C p.1 p.2) (Q k) ≠ 0 := by
    intro k
    rw [map_prod] at hC
    exact Finset.prod_ne_zero_iff.1 hC k (Finset.mem_univ _)
  have hxV : x ∈ ⨆ k, V k := by rw [hcov]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hxV
  have hnz : ∃ p, x ∈ nonzeroLocus (b p) := by
    have : x ∈ ⨆ j, nonzeroLocus (b j) := by rw [hb]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have h6 := hQu k (fun p => C p.1 p.2) (hCk k) x hk hnz
  refine cotangent_independent_unit_mul _ _
    (IsUnit.map (ConcreteCategory.hom (Y.X.presheaf.germ (L.U i ⊓ L.U (c k)) x ⟨hx, hVc k hk⟩))
      (L.g i (c k)).isUnit).unit (fun j => ?_) h6
  rw [IsUnit.unit_spec]
  exact germ_chart_eq _ i (c k) hx (hVc k hk)

end GlobalTheory.CompanionTheory.KoszulCount
