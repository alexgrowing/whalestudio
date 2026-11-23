import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVecStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPrimGenerator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsTorusPointsFramesFamilyTerms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamCoefVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtFormalTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ShortestVectorStrictOfMul
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionValueInFrameLinearUniqueExistsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusOperatorEigenOfExpansionSingleClassStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScaleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValLeOfValuedSumAgainstCharactersStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttainedStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

theorem val_lt_of_shortest {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 2 ≤ r) (z : D.toPre.X) (hz : ∀ m, Q z ≤ Q (z + n • m)) (m : D.toPre.X)
    (hm : (n * r) • m ≠ 0) : Q z < Q (z + (n * r) • m) := by
  let B : D.toPre.X →+ D.toPre.X →+ ℤ := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => QForm.bOf D.toPre Q a b)
    (fun b b' => by
      rw [QForm.bOf_comm D (Q := Q) a, QForm.bOf_add_left hϖ D hQ, QForm.bOf_comm D (Q := Q) b,
        QForm.bOf_comm D (Q := Q) b']))
    (fun a a' => AddMonoidHom.ext fun b => QForm.bOf_add_left hϖ D hQ a a' b)
  refine shortest_vector_strict_of_mul _ Q B (fun a b => ?_) (fun a => ?_) (fun a ha => QForm.Q_pos hϖ D hQ ha)
    n r hn hr z hz m hm
  · show _ = Q a + Q b + QForm.bOf D.toPre Q a b
    rw [QForm.bOf]; ring
  · show _ = QForm.bOf D.toPre Q a a
    have h := QForm.bOf_add_left hϖ D hQ a (-a) a
    simp only [QForm.bOf, add_neg_cancel, neg_add_cancel, zero_add, QForm.Q_neg hϖ D hQ, QForm.Q_zero hϖ D hQ] at h ⊢
    linarith

theorem exists_origin (hLL : LL) (hT : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hTW : TWStatement)
    (hUU : UUStatement) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hadm : AdmBase V (IsLocalRing.maximalIdeal V))
    {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) (k : ℕ) : ∃ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero ∧ FrmOne w ∧
      GtV hϖ hv g (fun _ => 0) ∧ GenV hϖ hv w 0 := by
  obtain ⟨-, -, h₁, -, h₂⟩ := gt_onto_divisible_kernel hLL V _ hadm D F
  obtain ⟨g, hg, -⟩ := h₁ 1
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic V D.toPre F k g).2.1 hg.1
  obtain ⟨⟨l, hl, hu⟩, -, h₃, h₄, -⟩ := CoefVal.main hLL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv g
  have hadd : g.IsAdd g g := (h₂ 1 1 g g g hg hg).2 (by rwa [_root_.mul_one])
  have e : l + l = l := hu (l + l) (h₄ g g l l hadd hl hl)
  have e₀ : l = 0 := by simpa using e
  refine ⟨g, w, (isZero_iff g).2 ⟨hg.1, fun χ y J hJ => Units.ext ?_⟩, hw, ?_, h₃ k w hw hg.1⟩
  · refine (hg.2 χ y J hJ).trans ?_
    rw [CoefBasic.cst_eq]
    exact map_one _
  · rw [e₀] at hl
    exact hl

set_option maxHeartbeats 1000000 in

theorem exists_norm_FF_eq : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ p _ y₀ u l hint α hα
  obtain ⟨hLL, hT, hVR, hTW, hUU⟩ := laws_all hL hL2
  obtain ⟨hch, -, hadm, hN', hζ, ϖ, Q, v, lam, hϖ, hv, hnorm⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hint
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing hL o Ω S ρ p y₀ u
  obtain ⟨rig, e, th, s, hs⟩ := GlobalTheory.T.exists_thetaSystem_test_sections_on_geometric_fibre hL o Ω S ρ p y₀ u x hx
  have hle : S.perp l.yy.ker ≤ l.yy.ker :=
    l.isoFree.1.trans ((thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 _).le
  refine GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained o Ω S p y₀ hint _ (l.wt α) _
    (fun t i => GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hU o Ω S ρ p y₀ u l hint α hα t (hle t.2) i) ?_
  obtain ⟨w₀, hw₀⟩ := (EvalZero.value_at_origin hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p)).2.1 rig hs.1
  obtain ⟨th', ϑ, hϑ, hprim, hgen⟩ := exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hnorm.2.1
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1
  obtain ⟨c₀, hc₀⟩ := hgen th
  obtain ⟨c, rfl⟩ : ∃ c : PadicAlgCl p, cF u.V c = c₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom.hom c₀,
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom_inv_id_apply c₀⟩
  have hδ : S.delta y₀ ≤ ‖c‖ := ciSup_le
    (GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm w₀ th' ϑ c hw₀ hϑ hprim hc₀)
  by_cases hc : c = 0
  · rw [hc, norm_zero] at hδ
    exact ⟨0, ρ.i₀, (mul_nonpos_of_nonpos_of_nonneg hδ (Real.exp_pos _).le).trans (norm_nonneg _)⟩
  obtain ⟨hlam, hQ, hq, hge, heq⟩ := id hnorm
  have hN0 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  have hrN : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos hN0
  have hN4 : 4 ≤ S.N := by
    have : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]; nlinarith
  have hr2 : 2 ≤ S.r := by
    obtain ⟨j, hj, hr⟩ := ρ.r_eq
    rw [hr]
    exact ρ.n_prime.two_le.trans (Nat.le_self_pow (by omega) _)
  haveI : NeZero (S.r * S.N) := ⟨by omega⟩
  haveI : Fintype (S.perp l.yy.ker) := Fintype.ofFinite _
  obtain ⟨g, w₁, hg, hw₁, hgv, hwv⟩ := exists_origin hLL hT hVR hTW hUU u.complete hadm hϖ u.D hQ hv S.N
  obtain ⟨Φ, hΦ, hsupp, hval⟩ := CoefUnit.exists_fam_coef_val hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv S.N hN4 g w₁ _ 0 hw₁.1 hgv hwv α
  obtain ⟨b, σ, hb, hσ, hσΦ⟩ := GlobalTheory.T.exists_integral_basis_combination_of_integral_family hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm
    w₀ th' ϑ c hw₀ hϑ hprim hc₀ hc Φ hΦ
  choose τ q hqy hτ hqx hτv using GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points hL hL2 hU o Ω S ρ p y₀ u l hint x hx
  have key : ∀ t : S.perp l.yy.ker, ∃ ζ : PadicAlgCl p, v ζ = 0 ∧
      SumV v (fun β => (τ t (Multiplicative.ofAdd β)).val * coef Φ g w₁ β)
        (ζ * ∑ j, b j * y₀ ⟨S.ev t j, S.ev_mem t j⟩) := fun t => by
    obtain ⟨ζ, hζ, H⟩ := WeightValue.value_at_formal_torsion hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
      (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ rig hw₀ (S.r * S.N) S.N hrN hN0 (q t) (x t) (hqy t) (hqx t) (e t)
      (hs.2.1 t)
    exact ⟨ζ, hζ, (H σ Φ _ hσΦ ((GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists hL u.V u.A (PadicAlgCl p) S.N (x t) (e t)).1 S.J s b _ σ hσ
      fun i => hs.2.2.2.1 i t)).2 _ (hτ t) g w₁ hg hw₁⟩
  choose ζ hζv hsum using key
  have v1 : ∀ z : PadicAlgCl p, ‖z‖ = 1 → v z = 0 := fun z hz => (heq z 0).2 (by simpa using hz)
  have hζ1 : ‖y₀ (algebraMap o S.R S.ζ)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero 2 (NeZero.ne (S.r * S.N)))).1
      (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_val_le_of_valuedSum_against_characters (PadicAlgCl p) v u.D.toPre.X (S.perp l.yy.ker)
    (fun t β => (τ t (Multiplicative.ofAdd β)).val) (coef Φ g w₁) ζ _ α ((Q α : ℚ) / S.N) hsum hζv
    (fun t β => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk β)
      exact v1 _ (by rw [hτv t a β ha, norm_pow, hζ1, one_pow]))
    (by
      obtain ⟨d, ⟨E⟩⟩ := l.isoFree.2
      refine v1 _ ?_
      rw [Fintype.card_congr E.toEquiv, Fintype.card_fun, ZMod.card, Nat.cast_pow, norm_pow, hN', one_pow])
    (by simpa using hval)
    (fun β hβ => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (β - α))
      by_cases hk : a ∈ l.yy.ker
      · right
        rw [AddMonoidHom.mem_ker, ha, QuotientAddGroup.eq_zero_iff] at hk
        obtain ⟨m, hm⟩ := hk
        have hm' : (S.N * S.r) • m = β - α := by rw [Nat.mul_comm]; exact hm
        have hlt := val_lt_of_shortest hϖ u.D hQ hN0 hr2 α (fun m => by
          have := hα m
          rw [hq, hq] at this
          exact_mod_cast le_of_mul_le_mul_left this hlam) m (by rw [hm']; exact sub_ne_zero.2 hβ)
        rw [hm', add_sub_cancel] at hlt
        refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_)
          ((((CoefVal.main hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv g).2.2.2.2.2.2
            S.N hN0 w₁ Φ hw₁.1).2 _ 0 0 hgv hwv hΦ β))
        have : (0 : ℚ) < S.N := by exact_mod_cast hN0
        simp only [zero_add, add_zero]
        exact div_lt_div_of_pos_right (by exact_mod_cast hlt) this
      · left
        refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero o Ω S _ _ hζ l.yy.ker a hk)
        rw [← hτv t a _ ha, ofAdd_sub, map_div, Units.val_div_eq_div_val, div_eq_inv_mul])
  rw [← GlobalTheory.T.thetaSystem_weightProjector_fixes_eigenvector o Ω S (PadicAlgCl p) (y₀.comp (algebraMap o S.R)) _ (l.wt α) l.isoFree b _
    (fun t' => GlobalTheory.T.torusOperator_eigen_of_expansion_single_class hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs w₀ hw₀.1 α b σ Φ hσ hσΦ hsupp t' t)] at ht
  have hE : Real.exp (-(l.q α / S.N)) = Real.exp (-(lam * (((Q α : ℚ) / S.N : ℚ) : ℝ))) := by
    rw [hq]; push_cast; ring_nf
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty Finset.univ_nonempty
    (fun i => b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩)
  refine ⟨t, i, ?_⟩
  have hw : Real.exp (-(l.q α / S.N)) ≤
      ‖∑ i, b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ := by
    rw [hE]
    by_contra hlt
    have hlt := not_le.1 hlt
    exact hlt.ne ((heq _ _).1 (le_antisymm ht ((hge _ _).2 hlt.le)))
  have hbi := hb i
  rw [norm_mul] at hi hbi
  calc _ ≤ ‖c‖ * (‖b i‖ * _) := mul_le_mul hδ (hw.trans hi) (Real.exp_pos _).le (norm_nonneg _)
    _ = (‖c‖ * ‖b i‖) * _ := (_root_.mul_assoc _ _ _).symm
    _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hbi (norm_nonneg _)
    _ = _ := _root_.one_mul _

end GlobalTheory.TestFibre
end
