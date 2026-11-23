import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointEqAdicSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFrameRatioIntegralFrameChartIndepende
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem frames_mul_eq_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∀ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g → f.IsGen → t.IsGen → (∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good U.LG.L z JG → Good D.toPre.P.L z JB → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h).left) (fun _ => JA (x).left) * val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA * val w (𝟙 _) z JB = val f (toUnit (TF (R := V) (FractionRing V))).left z JG * val t (toUnit (TF (R := V) (FractionRing V))).left z JB := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hL h g' f t hF hExt hP hf ht htl z JA JG JB hJA hJG hJB
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨JA₀, hA₀⟩ := CoefBasic.exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := CoefBasic.exists_good' U.LG.isLB z₀
  obtain ⟨l, hl⟩ := CoefBasic.cstH_surj z₀ (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀
    (x.left ≫ U.gen.inv.left) z₀ (JG₀ (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA₀ x.left) *
      val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z₀ JA₀ *
      (val f (toUnit (TF (R := V) (FractionRing V))).left z₀ JG₀)⁻¹).val
  have hl0 : l ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  have hfv : ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val := by
    intro z' JA' JG' hA hG'
    obtain rfl := CoefBasic.pt_eq z₀ z'
    have ind := GlobalTheory.Poinc.FrameIndep.frame_ratio_indep V _ D A G U.toUnifPre w₀ hw₀ x fr hfr h f hf hExt z₀ JA' JA₀ JG' JG₀
      hA hG' hA₀ hG₀
    rw [mul_inv_eq_iff_eq_mul] at ind
    rw [← Units.val_mul, ind, Units.val_mul, CoefBasic.cst_eq, hl]
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g'.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w', hw', hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl0)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w' (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl0, map_one, _root_.one_mul]
  have hLies : LiesOver U.toUnifPre w₀ g w' x fr := by
    intro k hk wk hwk hwkg s s' v hExp hVal
    obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
    choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
      (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
    have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
        sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
      fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
    choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g' t ht k α (fs i α)
    have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x fr h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
    have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
      intro z J hJ
      rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
        GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
    have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g' g hP t l hl0 k wk hwkg hwk' s' n c fs hs a ha
    have hI := admissibleBase_of_completeNormalLocalCharZero hV
    have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
      EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
        GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g' hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
          (a i) (ha i)
    have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl0
    convert key using 1
    · funext α
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
    · simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  haveI : CharZero V := hV.2.2.2
  have heq := LiesUniq.frame_unique (admissibleBase_of_completeNormalLocalCharZero hV) hG U hw₀ hw hw' hfr hL hLies z JB hJB
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hfv z JA JG hJA hJG, ← hwt z JB hJB, heq]
  ring

end GlobalTheory.Poinc.IntEval
