import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

noncomputable section

namespace GlobalTheory.FlagQ

open GlobalTheory.FlagBundle GlobalTheory.ProjVar GlobalTheory.FlagZ GlobalTheory.Cartier

theorem regAt_eventually {X : Scheme.{0}} [IsIntegral X] {y : X} {f : X.functionField} (h : RegAt y f) :
    ∀ᶠ z in 𝓝 y, RegAt z f := by
  obtain ⟨U, hy, a, rfl⟩ := h.exists_fnOf
  filter_upwards [U.isOpen.mem_nhds hy] with z hz
  exact regAt_fnOf hz _ a

theorem exists_isFrame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N),
    IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) → ∀ y : Y.X,
    ∃ (U : Y.X.Opens) (A : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) Y.Fn), y ∈ U ∧ ∀ z ∈ U, GlobalTheory.FlagQ.IsFrame j z A := by
  intro ι _ N Y j _ y
  have hloc : IsLocalRing (Y.X.presheaf.stalk y) := Y.X.toLocallyRingedSpace.isLocalRing y
  obtain ⟨g, hg⟩ := @exists_eq_flagPt_of_isLocalRing ι (ι × Fin (N + 1)) _ _ N Prod.fst Prod.snd
    (Y.X.presheaf.stalk y) _ hloc (Y.X.fromSpecStalk y ≫ j)
  set φ : Y.X.presheaf.stalk y →+* Y.Fn := algebraMap _ _ with hφ
  set g' : ι → GL (Fin N) Y.Fn := fun τ => Matrix.GeneralLinearGroup.map φ (g τ) with hg'
  set A : Mat (fun _ : ι => N) Y.Fn := fun τ => (g' τ).1.transpose with hA
  have hgen : flagPt Prod.fst Prod.snd (genMat j) = flagPt Prod.fst Prod.snd g' := by
    rw [← flagPt_genMat, ← spMap_flagPt, ← hg, ← Category.assoc]
    exact congrArg (· ≫ j) (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)).symm
  have hb := (flagPt_eq_iff_below ι _ N Prod.fst Prod.snd Y.Fn (genMat j) g').1 hgen

  have hdet (τ : ι) : (A τ).det = φ (g τ).1.det := by
    rw [hA, Matrix.det_transpose, RingHom.map_det]
    rfl
  have hent (τ : ι) (i k : Fin N) : A τ i k = φ ((g τ).1 k i) := rfl
  have hunit (τ : ι) : UnitAt y (A τ).det := ⟨_, (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit, (hdet τ).symm⟩
  have hev : ∀ᶠ z in 𝓝 y, (∀ τ i k, RegAt z (A τ i k)) ∧ ∀ τ, RegAt z (A τ).det⁻¹ := by
    refine (eventually_all.2 fun τ => eventually_all.2 fun i => eventually_all.2 fun k => ?_).and
      (eventually_all.2 fun τ => ?_)
    · exact regAt_eventually ⟨_, (hent τ i k).symm⟩
    · exact regAt_eventually (hunit τ).inv.regAt
  have hkey (τ : ι) : (A * (genFrame j)⁻¹) τ = (((genMat j τ)⁻¹ * g' τ).1).transpose := by
    rw [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv, Matrix.transpose_mul]
    show (g' τ).1.transpose * ((genMat j τ).1.transpose)⁻¹ = _
    rw [Matrix.transpose_nonsing_inv]
  obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
  refine ⟨⟨t, hto⟩, A, hyt, fun z hz => ⟨fun τ => ⟨fun i k => ?_, ?_, ?_, fun i k hi _ => absurd hi (Nat.not_lt_zero _)⟩,
    fun τ => ⟨fun _ _ => trivial, ?_, trivial, fun i k _ hik => ?_⟩⟩⟩
  · exact mem_O_ratOf.2 ((ht hz).1 τ i k)
  · exact (hunit τ).ne_zero
  · exact mem_O_ratOf.2 ((ht hz).2 τ)
  · rw [hkey, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 ((genMat j τ)⁻¹ * g' τ).isUnit).ne_zero
  · rw [hkey, Matrix.transpose_apply]
    exact hb τ k i ⟨(τ, ⟨k, Nat.lt_succ_of_lt k.isLt⟩), rfl, hik, le_refl _⟩

end GlobalTheory.FlagQ
