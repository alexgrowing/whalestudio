import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem stalkClosedPointTo_ger {V : Type} [CommRing V] [IsLocalRing V] {Y : Scheme.{0}} (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = GlobalTheory.TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [GlobalTheory.TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_eq_lift_residue {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
    H0.val x i hO hi f = IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom
      ((Y.residue (ptOf x)).hom (germ i (ptOf x) hy hj f)) := by
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm.trans
    (IsLocalRing.ResidueField.lift_residue_apply _ _).symm

open GlobalTheory.CompHt (genVal)
open GlobalTheory.AllWt (exOf secZ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ratGen_of_birOn : ∀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw),
    Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  intro Y X Z r U la ⟨M⟩ hB
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hgen := isGenericPoint_of_lift M h hz hO
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hη : ptOf (z ≫ M.σ) ∈ U₀ X Z := (le_iff_ptOf_mem _ _).1 hU
  have hdense : closure (M.σ '' Set.univ) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (dense_U₀ X Z).closure_eq]
    refine closure_mono fun u hu => ?_
    have hu' : ⊤ ≤ resPt u ⁻¹ᵁ U₀ X Z := (le_iff_ptOf_mem _ _).2 ((ptOf_resPt u).symm ▸ hu)
    obtain ⟨w, hw, -⟩ := M.existsUnique_lift (resPt u) hu'
    refine ⟨ptOf w, trivial, ?_⟩
    rw [← ptOf_comp, hw, ptOf_resPt]
  have hgen' : IsGenericPoint (ptOf (z ≫ M.σ)) Set.univ := by
    have := hgen.image M.σ.continuous
    rwa [hdense] at this
  refine ⟨ptOf (z ≫ M.σ), hη, hgen', ?_⟩
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := Om Z) (z ≫ M.σ)
  set ψ := IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom
    with hψ
  have e₁ : (z ≫ M.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  have hO₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have key : ∀ (i : (L₀ X Z la).ι) (hi : ptOf (z ≫ M.σ) ∈ (L₀ X Z la).U i), ∃ T : Om Z, T ≠ 0 ∧
      ∀ g : Cusp Z U la, ψ (((Y₀ X Z).residue (ptOf (z ≫ M.σ))).hom
        (germ i (ptOf (z ≫ M.σ)) hη hi (cuspSec X Z U la g))) = T * genVal Z g.1 := by
    intro i hi
    have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ X Z la).U i := (le_iff_ptOf_mem _ _).2 hi
    have hk₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) := (le_iff_ptOf_mem _ _).2 (mem_pull.1 hi)
    have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
    obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
    have hQ₂ : X.F.ChartFr (i PUnit.unit) ((z ≫ M.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
    refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
    have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
    have v₅ : H0.val (z ≫ M.σ) i hU hi' (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
        ((z ≫ M.σ) ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
      H0.val_pull (inc₀ X Z) le_rfl (z ≫ M.σ) i hU hi' hO₂ hk₂ _
    have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
    rw [← val_eq_lift_residue (z ≫ M.σ) i hU hi' hη hi, v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]
  have hmap : ∀ v w : Cusp Z U la, ∃ q ∈ ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη,
      ψ q = genVal Z v.1 / genVal Z w.1 := by
    intro v w
    obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) (ptOf (z ≫ M.σ))
    obtain ⟨T, hT, hv⟩ := key i hi
    refine ⟨_, Subfield.subset_closure ⟨i, hi, _, _, ⟨v, rfl⟩, ⟨w, rfl⟩, rfl⟩, ?_⟩
    refine (map_div₀ ψ _ _).trans ?_
    rw [hv, hv, mul_div_mul_left _ _ hT]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Cusp Z U la, genVal Z v₀.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB.1 (LinearMap.ext fun v => hc v)
  have hsub : (⊤ : IntermediateField c.F (Om Z)).toSubfield ≤
      (ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη).map ψ := by
    rw [← hB.2, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      obtain ⟨q, hq, e⟩ := hmap ⟨a • v₀.1, Submodule.smul_mem _ a v₀.2⟩ v₀
      refine ⟨q, hq, e.trans ?_⟩
      show genVal Z (a • v₀.1) / genVal Z v₀.1 = _
      rw [map_smul, Algebra.smul_def, mul_div_cancel_right₀ _ hv₀]
    · rintro _ ⟨v, w, rfl⟩
      exact hmap v w
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨q', hq', e⟩ := hsub (show ψ q ∈ (⊤ : IntermediateField c.F (Om Z)).toSubfield from trivial)
  exact (ψ.injective e) ▸ hq'

example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw), Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := @ratGen_of_birOn

end GlobalTheory.HSApp
