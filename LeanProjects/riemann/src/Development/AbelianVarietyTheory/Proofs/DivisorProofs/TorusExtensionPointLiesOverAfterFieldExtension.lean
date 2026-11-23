import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientFamilyPullbackFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuePulledBackSectionEqImageFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Poinc.Tors.LiesOverExt

theorem sumF_algebraMap {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {Ix : Type} (x : Ix → FractionRing R) (s : FractionRing R)
    (h : SumF I (FractionRing R) x s) :
    SumF I F (fun i => algebraMap (FractionRing R) F (x i)) (algebraMap (FractionRing R) F s) := by
  letI : Module R (FractionRing R) := Module.compHom (FractionRing R) (algebraMap R (FractionRing R))
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hS⟩ := h
  let φ : FractionRing R →ₗ[R] F :=
    { toFun := algebraMap (FractionRing R) F
      map_add' := map_add _
      map_smul' := fun r y => by
        show algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r • y) =
          algebraMap R (FractionRing R) r • algebraMap (FractionRing R) F y
        rw [smul_eq_mul, map_mul, Algebra.smul_def] }
  refine ⟨N.map φ, hN.map φ, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := φ) (hS T hT)
  rw [Submodule.map_smul''] at this
  simpa [φ, map_sub, map_sum] using this

theorem exists_frm_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} (g : GtPtF D (FractionRing R)) (w : Frm D (FractionRing R) k g.b)
    (hw : w.IsGen) :
    ∃ w' : Frm D F k (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b, w'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
        val w' r z J = val w (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  have hb := GlobalTheory.TorusExt.gtExt_b (D := D) (algebraMap (FractionRing R) F) (RingHom.comp_id _) g
  have h0 : spMap (algebraMap (FractionRing R) F) ≫ (DegPre.zeroF D (FractionRing R)).left =
      (DegPre.zeroF D F).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A)
      (GlobalTheory.TorusExt.extMap (R := R) (algebraMap (FractionRing R) F) (RingHom.comp_id _)))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB
    (φ' := DegPre.lineφ D F (GlobalTheory.TorusExt.gtExt D (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b)
    (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) (congrArg (fun q => q.left) hb).symm)
    (LB.pullGen D.P.L _ _ w (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frAt_pull {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x)
    (hfr : fr.IsGen) (x' : TFK (R := R) F ⟶ A.A) (hx : x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left) :
    ∃ fr' : FrAt x', fr'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F).left) (z : Z) (J), Good A.L z J →
      val fr' r z J = val fr (r ≫ spMap (algebraMap (FractionRing R) F)) z J := by
  obtain ⟨fr', hfr', hv⟩ := exists_gen A.isLB (φ' := fun _ : Fin 1 => x'.left) (ε' := fun _ => 1)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [hx])
    (LB.pullGen A.L _ _ fr (spMap (algebraMap (FractionRing R) F))) (pullGen_isGen _ _ _ _ hfr _)
  exact ⟨fr', hfr', fun Z r z J hJ => (hv Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_frm_pow {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F 1 b) (hw : w.IsGen) (k : ℕ) :
    ∃ wk : Frm D F k b, wk.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TF (R := R) F).left) (z : Z) (J), Good D.P.L z J →
      val wk r z J = val w r z J ^ k := by
  obtain ⟨wk, hwk, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by fin_cases i <;> simp [DegPre.lineε])
    (GeneratorPullback.powGen D.P.L _ _ w k) (powGen_isGen _ _ _ _ hw k)
  exact ⟨wk, hwk, fun Z r z J hJ => (hv Z r z J hJ).trans (val_pow _ _ _ _ _)⟩

open GlobalTheory.TorsionExt GlobalTheory.FieldBaseChange in

theorem liesOver_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (g : GtPtF D.toPre (FractionRing R)) (w : Frm D.toPre (FractionRing R) 1 g.b) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x), w.IsGen → fr.IsGen → GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ g w x fr → ∀ (x' : TFK (R := R) F ⟶ A.A), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → ∃ (w' : Frm D.toPre F 1 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g).b) (fr' : FrAt x'), w'.IsGen ∧ fr'.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) w' x' fr' := by
  intro R _ _ _ I hI D A G _ _ hGs U F _ _ _ w₀ hw₀ g w x fr hw hfr hlies x' hx'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨w', hw', hvw'⟩ := exists_frm_pull D.toPre F g w hw
  obtain ⟨fr', hfr', hvfr'⟩ := exists_frAt_pull x fr hfr x' hx'
  refine ⟨w', fr', hw', hfr', ?_⟩
  intro k hk wk' hwk'v hwk' s s'' v hexp hval
  obtain ⟨wk, hwk, hwkv⟩ := exists_frm_pow w hw k
  obtain ⟨wkF, hwkF, hvwkF⟩ := exists_frm_pull D.toPre F g wk hwk
  have hc : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ := fun χ =>
    GlobalTheory.UT.ThetaSum.coef_congr _ hwkF (fun z J hJ => by
      rw [hwk'v z J hJ, hvw' _ _ z J hJ, hvwkF _ _ z J hJ, hwkv _ _ z J hJ]) s'' χ
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U (FractionRing R) hk w₀ hw₀
  obtain ⟨e', he'⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  have cc : ∀ t, e' (abPull (FractionRing R) F A k t) = famPull D.toPre (FractionRing R) F hG k (e t) := fun t =>
    (he' _ _).1 (expandsF_pull U.toUnifPre hG ((he _ _).2 rfl))
  obtain ⟨n, c, σ, hσ⟩ := (isExtension_famPull D.toPre (FractionRing R) F hG hk).exists_sum s''
  choose a ha using fun i => GlobalTheory.ZH.SecComb.exists_valAt (e.symm (σ i)) hfr
  have sK : ∀ i, SumF I (FractionRing R) (coef (σ i) g wk) (a i) := fun i =>
    hlies k hk wk (fun z J hJ => hwkv _ _ z J hJ) hwk (e.symm (σ i)) (σ i) (a i)
      ((he _ _).2 (e.apply_symm_apply _)) (ha i)
  have comb := GlobalTheory.UT.EvalZero.sumF_comb hI F Finset.univ c _ _ fun i => sumF_algebraMap I F _ _ (sK i)
  have lin := ((GlobalTheory.UT.CoefBasic.coef_basic R D.toPre F k
    (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g)).2.2 wkF hwkF).2.1
  have hcoef : ∀ χ, coef s'' (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wk' χ =
      ∑ i, c i * algebraMap (FractionRing R) F (coef (σ i) g wk χ) := fun χ => by
    have h0 : coef 0 (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ = 0 := by
      have := lin 0 0 1 χ
      rw [smul_zero, add_zero, _root_.one_mul] at this
      exact left_eq_add.1 this
    let Lc : Fam D.toPre F k →ₗ[F] F :=
      { toFun := fun s => coef s (GlobalTheory.TorusExt.gtExt D.toPre (algebraMap (FractionRing R) F) (RingHom.comp_id _) g) wkF χ
        map_add' := fun s s' => by simpa using lin s s' 1 χ
        map_smul' := fun c s => by simpa [h0] using lin s 0 c χ }
    rw [hc χ, hσ]
    show Lc _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]
    exact congrArg (c i * ·) (GlobalTheory.T.fourierCoefficient_familyPullback_fractionField R D.toPre F hG k (σ i) g wk wkF hwk hwkF
      (fun z J hJ => hvwkF _ _ z J hJ) χ)

  let u : Fin n → AbSec A F k := fun i => abPull (FractionRing R) F A k (e.symm (σ i))
  have hs : (s : AbSec A F k) = ∑ i, c i • u i := by
    apply e'.injective
    rw [(he' _ _).1 hexp, map_sum, hσ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, cc, e.apply_symm_apply]
  have hcomb : IsComb u c s := fun j => by
    rw [hs]
    exact (map_sum (chartLin (abelianBase A F) _ j) (fun i => c i • u i) Finset.univ).trans rfl
  have hvu : ∀ i, ValAt (u i) x' fr' (algebraMap (FractionRing R) F (a i)) := fun i =>
    GlobalTheory.T.value_pulledBackSection_eq_image_fieldExtension R A F k _ x fr x' fr' hx' hfr (fun z J hJ => hvfr' _ _ z J hJ) _ (ha i)
  have hval' := ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).2 (Fin n) c u).2 s hcomb |>.1 x' fr' _ hvu
  have hv : v = ∑ i, c i * algebraMap (FractionRing R) F (a i) :=
    ((GlobalTheory.ZH.SecComb.lin_comb_value_act R A F k).1 s x' fr' hfr').unique hval hval'
  rw [hv, funext hcoef]
  exact comb

end GlobalTheory.Poinc.Tors.LiesOverExt
