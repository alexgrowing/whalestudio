import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionValueZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntEval

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem hRed_pGl {U : UnifPre I D A G} {h : 𝟙_ (Over (Sp R)) ⟶ G} {g : GtPt D.toPre (𝟙_ (Over (Sp R)))}
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g) (e : ℕ) : hRed I h e ≫ pGl U e = thick R I e ≫ g.b.left := by
  have a : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ (fstG I e (𝟙_ (Over (Sp R)))).left = thick R I e :=
    (hRed_fst _ e).trans (Category.comp_id _)
  have b : hRed I (𝟙 (𝟙_ (Over (Sp R)))) e ≫ ((Over.pullback (thick R I e)).map h).left = hRed I h e := by
    have := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
    rw [← cancel_mono (fstG I e G).left, hRed_fst, Category.assoc]
    have c : ((Over.pullback (thick R I e)).map h).left ≫ (fstG I e G).left =
        (fstG I e (𝟙_ (Over (Sp R)))).left ≫ h.left := pullback.lift_fst _ _ _
    rw [c, ← Category.assoc, a]
  exact (congrArg (· ≫ pGl U e) b).symm.trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (hg e).1.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ g.b.left) a))))

theorem exists_tRel [IsLocalRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) {U : UnifPre I D A G}
    {h : 𝟙_ (Over (Sp R)) ⟶ G} {b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A}
    (hb : ∀ e, hRed I h e ≫ pGl U e = thick R I e ≫ b.left)
    (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, b.left] (DegPre.lineε 1)),
      t.IsGen ∧ ∀ e : ℕ, TRel U h b f t e := by
  obtain ⟨ν, ν', hν, hν', v⟩ := GlobalTheory.TorsionTranslate.exists_matching U hI (K := Fin 1) (fun _ => 1)
    (fun _ => b.left) (fun _ => h.left) (fun e _ => hRed I h e) (fun e _ => hb e) (fun e _ => hRed_fst h e)
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio U.LG.isLB rfl f ν' hf hν'
  obtain ⟨μ₁, hμ, vμ⟩ := GlobalTheory.TorsionTranslate.exists_scale ν hν ρ
  obtain ⟨t, ht, vt⟩ := exists_gen D.toPre.P.isLB (φ' := ![(η[D.toPre.P.A]).left, b.left]) (ε' := DegPre.lineε 1)
    (fun W _ k => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_unique]
      rfl)
    (LB.mulGen D.toPre.P.L (K := PUnit) _ _ _ _ D.toPre.rig (LB.invGen D.toPre.P.L _ _ μ₁))
    (mulGen_isGen _ _ _ _ _ _ _ D.toPre.rig_gen (invGen_isGen _ _ _ _ hμ))
  refine ⟨t, ht, fun e Z r z J JG hJ hJG => ?_⟩
  have k := v e Z r z J JG hJ hJG
  rw [Fintype.prod_unique, zpow_one] at k
  have w : wv U e (r ≫ hRed I h e) z (J (r ≫ hRed I h e ≫ pGl U e)) (JG (r ≫ hRed I h e ≫ fGl I G e)) =
      GlobalTheory.TorusInvariance.wVal U e z J JG (r ≫ hRed I h e) := by
    rw [← Category.assoc, ← Category.assoc]; rfl
  have k₁ := (vt _ (r ≫ thick R I e) z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg (_ * ·)
    ((val_inv _ _).trans (congrArg (·⁻¹) ((vμ _ _ z J hJ).trans (congrArg (_ * ·) k))))))
  have k₂ := hρ _ (r ≫ thick R I e) z JG hJG
  refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) k₁ w) k₂).trans ?_
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end

theorem exists_integral_frame : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (h : 𝟙_ (Over (Sp V)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp V)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1)), f.IsGen → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1)), t.IsGen ∧ ∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U h g.b f t e := by
  intro V _ _ _ hV D A G _ _ U h g hg f hf
  have := hV.2.2.1
  exact exists_tRel (maximalIdeal.isMaximal V).ne_top (hRed_pGl hg) f hf

end GlobalTheory.Poinc.IntEval
