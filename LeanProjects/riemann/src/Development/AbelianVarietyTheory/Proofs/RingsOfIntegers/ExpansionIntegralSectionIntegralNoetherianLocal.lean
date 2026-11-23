import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtDvdOfSecIsMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemSpanCstOfCstMulEqZero

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralExpansionLocal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

theorem dvd_gs_of_dvd_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {c : Z.presheaf.stalk z}
    (h : ∀ J, Good L z J → c ∣ sval s r z J) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) :
    c ∣ gs r z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  rw [sec_trans s r z hj (hJ.mem φ r)]
  exact dvd_mul_of_dvd_right (h J hJ) _

theorem isUnit_cst_of_ne_zero {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {r : R} (hr : r ≠ 0) :
    IsUnit (cst (p ≫ jK R) z r) := by
  have hne : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have key : cst (p ≫ jK R) z r = cst p z (algebraMap R (FractionRing R) r) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp p (algebraMap R (FractionRing R)) z r
  rw [key]
  refine isUnit_iff_exists_inv.2 ⟨cst p z (algebraMap R (FractionRing R) r)⁻¹, ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, mul_inv_cancel₀ hne, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

private theorem injective_app_pullback_fst_of_flat {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK R)).app W).hom := by
  haveI : QuasiCompact (pullback.fst G.hom (jK R)) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (jK R) := by
    unfold jK
    exact SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap _ (IsFractionRing.injective R (FractionRing R))
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) := inferInstance
  exact Scheme.Hom.app_injective _ W

private theorem isUnit_gs_scal_of_ne_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : (D.BF (FractionRing R)).left)
    {r : R} (hr : r ≠ 0) : IsUnit (gs (𝟙 _) y ⊤ (scal (D.BF (FractionRing R)).hom r)) := by
  unfold scal
  erw [gs_pull (𝟙 _) (D.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp]
  unfold DegPre.BF
  change IsUnit (cst (TF (FractionRing R) ⊗ D.P.A).hom y r)
  rw [← Over.w (fst (TF (FractionRing R)) D.P.A)]
  unfold TF
  simp only [Over.mk_hom]
  rw [← Category.assoc]
  exact isUnit_cst_of_ne_zero _ y hr

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  intro R _ _ _ _ I hI D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ', f, hσ', hf, hexp⟩ := hE
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hP : D.toPre.P.L.IsLB := D.toPre.P.isLB
  haveI : Smooth G.hom := U.smooth
  have hinj : ∀ W : G.left.Opens, Function.Injective ((pullback.fst G.hom (jK R)).app W).hom :=
    fun W => injective_app_pullback_fst_of_flat G W
  have hσ'' : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK R))
      (scal (pullback.fst G.hom (jK R) ≫ G.hom) r) := by
    rw [pullback.condition]
    exact hσ'
  have h2 : SecIsMul G.hom r σ' σ := GlobalTheory.IntegralExpansion.secIsMul_of_secScal hLG G.hom hinj hs hσ''
  have h3 := fun e => GlobalTheory.expandsAt_dvd_of_secIsMul R I D A G U e k r σ' σ f h2 (hexp e)
  haveI : Smooth D.toPre.P.A.hom := D.toPre.P.isAb.smooth
  haveI : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  have h4 : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom r (f α) g := by
    intro α
    refine GlobalTheory.GermDiv.main R I (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
      D.toPre.P.A _ (linComb_isLB _ hP _ _) (f α) r hr ?_
    intro n x j hx
    exact dvd_gs_of_dvd_sval hP (f α) (fstG I n D.toPre.P.A).left x (fun J hJ => h3 n α x J hJ) j hx
  choose g hg using h4
  refine ⟨g, fun e => expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ' g f h2 hg hexp e, ?_⟩
  intro α
  have hga := hg α
  unfold SecIsMul at hga
  refine ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval hP (fun y J hJ => ?_)
  have e1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (𝟙 _) y hJ
  have hm := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left)
  have e2 : sval (f α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J =
      gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) *
        sval (g α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J := by
    unfold sval
    erw [hga, gs_mul _ _ _ hm, gs_res _ _ le_top hm]
  rw [e2] at e1
  have e3 : gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) =
      gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r) := by
    unfold scal
    rw [Category.id_comp]
    erw [gs_pull (D.toPre.prB (FractionRing R)).left D.toPre.P.A.hom y ⊤ trivial,
      gs_pull (𝟙 _) (D.toPre.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp, Over.w]
  rw [e3] at e1
  have hu : IsUnit (gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r)) := isUnit_gs_scal_of_ne_zero D.toPre y hr
  exact hu.mul_left_cancel e1

end GlobalTheory.IntegralExpansionLocal
