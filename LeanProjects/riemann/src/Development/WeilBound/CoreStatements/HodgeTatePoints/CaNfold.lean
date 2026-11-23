import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdAd
import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft

noncomputable section

namespace PositivityTheory.HtPt.Ca

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd ReciprocityTheory.ChartRestriction.G.DVR

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem exists_kappa (t : SAB H X0) (n : ℕ) :
    ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧
      ∀ (T : Over X0) (p q : T ⟶ t.G) (z : T.left) (J), Good t.PP.L z J →
        val κ (lift p q).left z J = cubN (cubV t.cub z J) n 1 p q := by
  obtain ⟨t₀, ht₀, hv₀⟩ := exists_cubN t.cub (1 : t.G ⊗ t.G ⟶ t.G) (fst t.G t.G) (snd t.G t.G) n
  obtain ⟨κ, hκ, hv⟩ := exists_gen t.PP.isLB
    (φ' := Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G]))
    (ε' := Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I)) (fun U _ h => by
      have a := prod_cube₂ (fst t.G t.G ^ n) (snd t.G t.G) h
      have b := prod_cube₂ (fst t.G t.G) (snd t.G t.G) h
      have b' : ∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (-((n : ℤ) * cε 2 I)) =
          (∏ I, h (cφG t ![fst t.G t.G, snd t.G t.G] I) ^ (cε 2 I)) ^ (-(n : ℤ)) := by
        rw [← Finset.prod_zpow]
        exact Finset.prod_congr rfl fun I _ => by rw [← zpow_mul]; congr 1; ring
      refine Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) a
        (b'.trans (congrArg (· ^ (-(n : ℤ))) b)))).symm
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_pow]
      module) t₀ ht₀
  refine ⟨κ, hκ, fun T p q z J hJ => (hv _ _ z J hJ).trans ((hv₀ T (lift p q) z J hJ).trans ?_)⟩
  rw [MonObj.comp_one, lift_fst, lift_snd]

variable [StarRing (𝓞 E)] {t : SAB H X0} {S : Type} [CommRing S] {x : Sp S ⟶ X0} {d : ℕ} (g : GermAt t x d) {m k : ℕ}

theorem ac_zero (u : Q S d k) : ac (AQ g.B.A 0) u = 0 :=
  (congrArg (sq ![u]) (show AQ g.B.A 0 = 0 from Subtype.ext (act_zero_eq g.B))).trans (map_zero _)

theorem ac_succ (n : ℕ) (u : Q S d k) :
    ac (AQ g.B.A ((n + 1 : ℕ) : 𝓞 E)) u = op (FQ g.B.G) (ac (AQ g.B.A (n : 𝓞 E)) u) u := by
  rw [Nat.cast_succ, ac_add, ac_one]

theorem PP_nat (n : ℕ) (u : Q S d k) : PP m g.x (ac (AQ g.B.A (n : 𝓞 E)) u) = PP m g.x u ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, ac_zero, PP_zero g.chart, pow_zero]
  | succ n ih => rw [ac_succ, PP_op g.chart, ih, pow_succ]

theorem value_first_power {y : (jOG x d m 2).left} {J : ((jOG x d m 2).left ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L y J)
    (n : ℕ) : VV m y (pow1 g.B n) = (cubN (cubV t.cub y J) n 1 (PP m g.x (gen 0)) (PP m g.x (gen 1)) *
      (ee g.x g.e y J (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1))⁻¹ * ee g.x g.e y J (gen 0) (gen 1) ^ n).val := by
  induction n with
  | zero =>
    rw [pow1, Finset.prod_range_zero, VV_one, Nat.cast_zero, ac_zero, (dict_ax hJ g.axes _).1]
    simp [cubN]
  | succ n ih =>
    have e : pow1 g.B (n + 1) = pow1 g.B n * E3 g.B.ph1 (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 0) (gen 1) := by
      simp only [formalSeriesValueAtThreePoints_eq_ev, ac_val, gen_val]
      exact Finset.prod_range_succ _ _
    rw [e, VV_mul, ih, frame_biext_dictionary_first_partial_law hJ g.frame, ← Units.val_mul, ac_succ, PP_nat]
    refine congrArg Units.val (Additive.ofMul.injective ?_)
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul, pow_succ, ofMul_mul, ofMul_inv]
    abel

theorem homAt_gen : (homAt x (jQ m ![(gen 0 : Q S d 2), gen 1])).left = 𝟙 _ := by
  have e : jQ m ![(gen 0 : Q S d 2), gen 1] = AlgHom.id S _ := GermD.jet_hom_ext fun s => by
    obtain ⟨j, s⟩ := s
    rw [jQ_X]
    fin_cases j <;> exact psJet_X m _
  rw [e]
  exact Spec.map_id _

end SlopeTestRemainingChoices

open ReciprocityTheory.ChartRestriction.G.TB.Canon Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdAd in

theorem nfold_law : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (n : ℕ), ∃ κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ n, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((n : ℤ) * cε 2 I))), κ.IsGen ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (1 : t.G ⟶ t.G) (𝟙 t.G)).left) (LB.oneGen t.PP.L) ∧ ∀ (S : Type) [CommRing S] (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d) (m : ℕ), ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ κ (lift (jptG t x d g.x m (0 : Fin 2)) (jptG t x d g.x m (1 : Fin 2))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x d g.x g.e m ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (LB.invGen t.PP.L _ _ (genPowG t _ _ (g.e m) n)))) := by
  intro E _ _ _ H _ _ X0 t n
  obtain ⟨κ, hκ, hv⟩ := exists_kappa t n
  refine ⟨κ, hκ, corr_of_val t.PP.isLB fun y J hJ => ?_, fun S _ x d g m => ?_⟩
  · refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, val_one, hv _ _ _ y J hJ]
    exact Finset.prod_eq_one fun i _ => (isCub_cubV t.cub hJ).face₂ _ _
  · have hc : MvPowerSeries.constantCoeff (pow1 g.B n) = 1 := by
      rw [← cc_ev ZZa, ((act_zero S d _ g.B).2.2.2 n).1.1, map_one]
    obtain ⟨w, hw⟩ : IsUnit (pow1 g.B n) := MvPowerSeries.isUnit_iff_constantCoeff.2 (hc ▸ isUnit_one)
    let u : (Jet S (Fin 2 × Fin d) m)ˣ := ⟨psJet m w.val, psJet m w.inv,
      by rw [← FBIdJet.psJet_mul, w.val_inv, FBIdJet.psJet_one], by rw [← FBIdJet.psJet_mul, w.inv_val, FBIdJet.psJet_one]⟩
    have hu : (u : Jet S (Fin 2 × Fin d) m) = psJet m (pow1 g.B n) := congrArg (psJet m) hw
    refine ⟨u, hu, corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    refine (val_pull hJ _ _ _).trans ?_
    rw [Category.id_comp, hv _ _ _ y J hJ]
    have h0 := gm_unit (x0 := x) (y := y) u ![gen 0, gen 1] _ hu
    have h1 := val_peG g.x hJ g.e ![gen 0, gen 1]
      ![fun j => psIn d m ![0] (g.B.A.act (n : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]
      (ac (AQ g.B.A (n : 𝓞 E)) (gen 0)) (gen 1)
      (by rintro ⟨l, j⟩; fin_cases l; exacts [hA _ 0 j, hX 1 j])
      (by rintro ⟨l, j⟩; fin_cases l; exacts [(FBIdPh.cc_psIn d m _ _).trans (g.B.A.const _ j),
        MvPolynomial.constantCoeff_X _ _])
    rw [sq_ac, sq_gen, sq_gen, homAt_gen] at h1
    have h2 : val (genPowG t _ _ (g.e m) n) (𝟙 _) y J = ee g.x g.e y J (gen 0) (gen 1) ^ n := by
      rw [ee, homAt_gen]; exact map_pow _ _ _
    have h3 : sb ![(gen 0 : Q S d 2), gen 1] (pow1 g.B n) = pow1 g.B n := formalSeriesValueAtTwoPoints_genericPoints _
    rw [h3, value_first_power g hJ, homAt_gen] at h0
    refine Eq.trans ?_ ((val_scale hJ _ _ _).trans (congrArg₂ (· * ·) (Units.ext h0) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) h1 ((val_inv _ _).trans (congrArg (·⁻¹) h2)))))).symm
    rw [PP_gen, PP_gen]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, Matrix.cons_val]
    abel

end PositivityTheory.HtPt.Ca
