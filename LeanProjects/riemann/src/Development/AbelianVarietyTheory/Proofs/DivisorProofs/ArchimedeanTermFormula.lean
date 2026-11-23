import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGradedRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOnRegularFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyBundleMapSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyArithDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyValueUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricDescendsSameValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFlagValuePreservedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDualMetricIsometricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagValuePullbackCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernPushForwardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernCoverChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricFlagIsometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalEmbeddingAdaptedFlagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericMapToModuliBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricComparisonNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricIsometryNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticFunctionLineAdelesStatement
open NumberField MvPolynomial CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula Formalism.L2.Pj GlobalTheory GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.CovTest GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.TwoLat GlobalTheory.OrthFilt GlobalTheory.VdmRec GlobalTheory.MixDens GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Published
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrthFilt

open GlobalTheory.FlagFibre (Low)

theorem rename_vdm_unit {κ : Type} {g : ℕ} (f : Fin g → κ) :
    rename (fun z : Σ _ : Unit, Fin g => f z.2) (vdm fun _ : Unit => g) =
      ∏ i : Fin g, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (f i') - MvPolynomial.X (f i) : MvPolynomial κ ℝ) := by
  simp [vdm]

theorem isHomogeneous_vdm_one {κ : Type} {g : ℕ} (f : Fin g → κ) :
    (∏ i : Fin g, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (f i') - MvPolynomial.X (f i) : MvPolynomial κ ℝ)).IsHomogeneous
      (g.choose 2) := by
  have h := (FlagCmp.isHomogeneous_vdm fun _ : Unit => g).rename_isHomogeneous (f := fun z : Σ _ : Unit, Fin g => f z.2)
  rwa [rename_vdm_unit, Fintype.card_sigma, Fintype.sum_unique, (FlagCmp.card_low g).2, ← Nat.choose_two_right] at h

theorem isHomogeneous_sq {κ J : Type} [Fintype J] (f : J → κ) :
    (∑ z, MvPolynomial.X (f z) ^ 2 : MvPolynomial κ ℝ).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun z _ => by simpa using (isHomogeneous_X ℝ (f z)).pow 2

theorem bcPair_pull_of_eq {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} {d : ℕ} {ρ : Y ⟶ X} (hX : IsArithVar p (d + 1)) (hρ : FlagChain.IsCov p (d + 1) ρ) (v : ρ ≫ p = q)
    {E : X.Modules} {r : ℕ} {h : VMetric p E r} (H : h.IsCInf) (fl : Vert.Flag E r) (N : HermLB p) :
    bcPair (h.pull ρ v) (fl.pull ρ) (N.pull ρ v) d = (ρ.residueDegree (genericPoint Y) : ℝ) * bcPair h fl N d := by
  subst v
  exact T.flag_height_pairing_pullback_degree k X Y p d ρ hX hρ E r h H fl N

theorem exists_isArFun_of_isVal {k : Type} [CommRing k] {B : Scheme.{0}} [IsIntegral B] {q : B ⟶ Sp k} {n : ℕ}
    (hq : IsArithVar q (n + 1)) {L : B.Modules} {g : ℕ} {hL : VMetric q L g} (HL : hL.IsCInf) (F : FlagSp L g)
    [IsIntegral F.Y] {N : HermLB q} {a : ℝ} (ha : F.IsVal HL N (genericPoint B) n a) :
    ∃ Φ, IsArFun (F.fam HL N) (n + 1 + g.choose 2) Φ ∧ Φ (vdmPol g n) = a := by
  have := hq.isLocallyNoetherian
  obtain ⟨y, Φ, hy, hΦ, e⟩ := ha
  obtain ⟨y', hy', hc, -⟩ := ((T.flag_variety_arith_dimension k B q _ hq L g hL.isVB).2 F).2.2 (genericPoint B)
  have h₁ : y' = genericPoint F.Y := by
    refine IsGenericPoint.eq (S := Set.univ) ?_ (genericPoint_spec F.Y)
    rw [isGenericPoint_def, hc, genericPoint_closure, Set.preimage_univ]
  obtain rfl : y = genericPoint F.Y := h₁ ▸ ((hy.2 y' hy'.1).antisymm (hy'.2 y hy.1)).eq
  rw [show n + 2 + g.choose 2 = n + 1 + g.choose 2 + 1 by omega] at hΦ
  exact ⟨Φ, hΦ, e⟩

theorem apply_pairPol (HP : Hypotheses2) (hR : RegularAlteration) {k : Type} [CommRing k] {B Y X : Scheme.{0}} [IsIntegral B]
    [IsIntegral Y] [IsIntegral X] {q : B ⟶ Sp k} {π : Y ⟶ B} {ρ : X ⟶ Y} {p : X ⟶ Sp k} (w : ρ ≫ π ≫ q = p) {n D : ℕ}
    (hq : IsArithVar q (n + 1)) (hY : IsArithVar (π ≫ q) D) (hρ : FlagChain.IsCov (π ≫ q) D ρ) {ι : Type} [Fintype ι]
    {E E' : ι → B.Modules} {r : ι → ℕ} {h : ∀ a, VMetric q (E a) (r a)} {h' : ∀ a, VMetric q (E' a) (r a)}
    (H : ∀ a, (h a).IsCInf) (H' : ∀ a, (h' a).IsCInf) {u : ∀ a, E a ⟶ E' a} (hu : ∀ a, IsoHom (h a) (h' a) (u a))
    {fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)} (hfl : IsFlagBundle π E r fl)
    {fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj (E' a))) (r a)}
    (hc : ∀ a, Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map (u a))) ((fl a).pull ρ) (fl' a))
    {L : B.Modules} {g : ℕ} {hL : VMetric q L g} (HL : hL.IsCInf) {m : ℕ} {o : ι ≃ Fin m} (hG : IsGraded hL o h u)
    (F : FlagSp L g) {N : HermLB q} (hN : N.icls = -(VMetric.det HL).icls) {a : ℝ}
    (ha : F.IsVal HL N (genericPoint B) n a) {Φ : MvPolynomial ((Σ a, Fin (r a)) ⊕ (Σ a, Fin (r a))) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (Sum.elim (fun z : Σ a, Fin (r a) => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ w)
      fun z : Σ a, Fin (r a) => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ w)) D Φ) :
    Φ (pairPol r n) = (∏ a, ((r a).factorial : ℝ)) * (ρ.residueDegree (genericPoint X) : ℝ) * a := by
  subst w
  have hX := hρ.1
  have := hq.isLocallyNoetherian
  have := hX.isLocallyNoetherian
  obtain ⟨f, hf, rfl⟩ : ∃ f, (vdm r).IsHomogeneous f ∧ D = n + f + 1 := by
    refine ⟨_, FlagCmp.isHomogeneous_vdm r, ?_⟩
    have hs := T.flag_bundle_smooth_relative_dimension B Y π ι E r fl (fun a => (h a).isVB) hfl
    have h₁ := (T.krull_dim_smooth_surjective_total B Y π (∑ a, r a * (r a - 1) / 2) (n + 1) (T.flag_bundle_projection_surjective B Y π ι E r fl (fun a => (h a).isVB) hfl) hq.dim_eq).symm.trans hY.dim_eq
    have h₂ : n + 1 + ∑ a, r a * (r a - 1) / 2 + 1 = D + 1 := by exact_mod_cast h₁
    rw [Fintype.card_sigma, Finset.sum_congr rfl fun a _ => (FlagCmp.card_low (r a)).2]
    omega
  have hF := ((T.flag_variety_arith_dimension k B q _ hq L g hL.isVB).2 F).1
  have := hF.isIntegral
  obtain ⟨ΦF, hΦF, rfl⟩ := exists_isArFun_of_isVal hq HL F ha
  let HX := (HL.pull π rfl).pull ρ rfl
  obtain ⟨T, wf, e, hT, hA, hw⟩ := GlobalTheory.T.graded_metric_flag_isometry k X _ ι _ g _ HX _ _ r (fun a => ((h a).pull π rfl).pull ρ rfl) _
    (fun a => ((H' a).pull π rfl).pull ρ rfl) _ m o (fun a => ((hu a).pull π rfl).pull ρ rfl)
    (GlobalTheory.T.graded_metric_pullback k Y X _ _ ρ rfl ι _ g _ _ _ r _ _ m o (fun a => (h' a).isVB.pullback π)
      (GlobalTheory.T.graded_metric_pullback k B Y q _ π rfl ι L g hL E E' r h u m o (fun a => (h' a).isVB) hG)) _ fl' hc
  obtain ⟨⟨W⟩, hW⟩ := GlobalTheory.T.flag_variety_arith_dimension k X _ _ hX _ g ((hL.isVB.pullback π).pullback ρ)
  replace hW := (hW W).1
  have := hW.isIntegral
  obtain ⟨Z, _, π₂, fz, γ, v, hNp, hfz, hZ, hγ, hdeg, hx, hy, hbc⟩ :=
    GlobalTheory.T.flag_bundle_chern_cover_chain k B Y X q π ρ _ rfl _ _ hq hY hρ ι E r h H fl hfl L g hL HL F W
  rw [show n + f + 1 + g.choose 2 = n + f + g.choose 2 + 1 by omega] at hW hZ hγ
  let LZ : (Σ a, Fin (r a)) ⊕ Option (Fin g) → HermLB (π₂ ≫ F.π ≫ q) :=
    Sum.elim (fun z => VMetric.grLB (fz z.1) z.2 (((H z.1).pull F.π rfl).pull π₂ rfl)) fun o => (F.fam HL N o).pull π₂ rfl
  let x' : (Σ a, Fin (r a)) → HermLB (ρ ≫ π ≫ q) := fun z => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ rfl)
  obtain ⟨ΨZ, hΨZ⟩ := ((HP.p4.arExists k Z _ _ hZ).2 _ LZ).1
  have hΨ₀ := (HP.p4.arProj k Z W.Y _ _ _ hZ hW γ v hγ.2.1 hγ.2.2).2 _ LZ ΨZ hΨZ
  obtain ⟨Ψ, hΨ⟩ := ((HP.p4.arExists k W.Y _ _ hW).2 _ (Sum.elim (fun i => (LZ i).pull γ v) fun z => (x' z).pull W.π rfl)).1
  let Vy : MvPolynomial (Option (Fin g)) ℝ :=
    ∏ i : Fin g, ∏ i' ∈ Finset.Ioi i, (MvPolynomial.X (some i') - MvPolynomial.X (some i))
  have hVy : Vy.IsHomogeneous (g.choose 2) := isHomogeneous_vdm_one some
  have hn : (MvPolynomial.X none ^ n : MvPolynomial (Option (Fin g)) ℝ).IsHomogeneous n := by
    simpa using (isHomogeneous_X ℝ none).pow n

  have e₁ := GlobalTheory.T.flag_bundle_chern_push_forward HP hR k F.Y Z _ _ _ _ hF hZ π₂ rfl ι _ r _ (fun a => (H a).pull F.π rfl) fz hfz _ _ LZ (F.fam HL N)
    .inl .inr (fun _ => .refl _) (fun _ => .refl _) ΦF ΨZ hΦF hΨZ
    ((∑ i : Fin g, MvPolynomial.X (some i) ^ 2) * Vy * MvPolynomial.X none ^ n) (by
      rw [show n + 1 + g.choose 2 + 1 = 2 + g.choose 2 + n by omega]
      exact ((isHomogeneous_sq some).mul hVy).mul hn)

  have e₂ := GlobalTheory.T.flag_bundle_chern_push_forward HP hR k X W.Y _ _ _ _ hX hW W.π rfl Unit _ (fun _ => g) _ (fun _ => HX) (fun _ => W.fl) W.univ _ _ _ _
    (fun z => .inl (.inr (some z.2))) (Sum.elim (fun z => .inl (.inl z)) .inr) (fun z => hy z.2)
    (by rintro (z | z); exacts [hx z.1 z.2, .refl _]) Φ Ψ hΦ hΨ (pairPol r n) (by
      rw [show n + f + 1 + 1 = 2 + f + 1 * n by omega]
      exact ((isHomogeneous_sq Sum.inr).mul hf.rename_isHomogeneous).mul
        ((IsHomogeneous.sum _ _ _ fun z _ => isHomogeneous_X ℝ _).neg.pow n))

  obtain ⟨I, _, c, nn, hV⟩ := FlagCmp.exists_sum_pow (d := n + f + g.choose 2)
    (P := rename Sum.inl (vdm r) * rename Sum.inr (Vy * MvPolynomial.X none ^ n)) (by
      rw [show n + f + g.choose 2 = f + (g.choose 2 + n) by omega]
      exact hf.rename_isHomogeneous.mul (hVy.mul hn).rename_isHomogeneous)
  have key (j : I) := FlagCmp.compare HP.p4 HP.q16 hW (HX.pull W.π rfl) (wf.pull W.π) W.fl _ _ Ψ hΨ
    (fun i => .inr (e.symm i)) (fun i => .inl (.inr (some i)))
    (fun i => ((VMetric.isometric_grLB_pull _ _ _ _ _ _ _ _ _ _ W.π rfl i).trans
      ((e.apply_symm_apply i ▸ hw (e.symm i)).pull W.π rfl)).symm) hy (Sum.elim (nn j) fun _ => 0)
  simp only [bcPair_congr _ _ (FlagCmp.isometric_comb_inl _ _ _), ← FlagCmp.rename_inl_lin] at key
  have b₁ := GlobalTheory.T.flag_bundle_chern_height HP k X W.Y _ _ _ _ hX hW W.π rfl Unit _ (fun _ => g) _ (fun _ => HX) (fun _ => W.fl) W.univ _
    (Option (Σ a, Fin (r a))) (fun i => (LZ i).pull γ v)
    (fun o => o.elim ((N.pull π rfl).pull ρ rfl) fun z => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ rfl)
    (fun z => .inr (some z.2)) (fun o => o.elim (.inr none) .inl) (fun z => hy z.2)
    (by rintro (_ | z); exacts [hNp N, hx z.1 z.2]) (rename some (vdm r) * MvPolynomial.X none ^ n) (by
      rw [add_comm]
      exact hf.rename_isHomogeneous.mul (by simpa using (isHomogeneous_X ℝ none).pow n)) I c nn (by
      rw [hV, rename_vdm_unit fun i => Sum.inr (some i)]
      simp only [Vy, map_mul, map_prod, map_sub, map_pow, rename_X, rename_rename, Option.elim]
      have : ((fun o : Option (Σ a, Fin (r a)) => (o.elim (.inr none) .inl : (Σ a, Fin (r a)) ⊕ Option (Fin g))) ∘ some) =
        Sum.inl := rfl
      erw [this]
      ring) ()
  have b₂ (a : ι) := GlobalTheory.T.flag_bundle_chern_height HP k F.Y Z _ _ (n + g.choose 2) _ (by rwa [add_right_comm]) hZ π₂ rfl ι _ r _
    (fun a => (H a).pull F.π rfl) fz hfz _ _ LZ (F.fam HL N) .inl .inr (fun _ => .refl _) (fun _ => .refl _) _
    (add_comm n _ ▸ hVy.mul hn) I c nn hV a
  have b₃ (j : I) : bcPair (((hL.pull π rfl).pull ρ rfl).pull W.π rfl) (wf.pull W.π) (comb (fun i => (LZ i).pull γ v) (nn j))
      (n + f + g.choose 2) = ∑ a, (γ.residueDegree (genericPoint W.Y) : ℝ) *
        bcPair (((h a).pull F.π rfl).pull π₂ rfl) (fz a) (comb LZ (nn j)) (n + f + g.choose 2) := by
    rw [GlobalTheory.T.orthogonal_embedding_adapted_flag HP.q16 k X _ ι _ g _ HX _ r _ (fun a => ((H a).pull π rfl).pull ρ rfl) T _ wf e hT hA W.Y _ W.π rfl _ hW]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hbc, bcPair_congr _ _ (isometric_comb_pull LZ (nn j) γ v)]
    exact bcPair_pull_of_eq hZ hγ v (((H a).pull F.π rfl).pull π₂ rfl) _ _
  have e₃ : Ψ ((∑ i, MvPolynomial.X (.inr (e.symm i)) ^ 2 - ∑ i, MvPolynomial.X (.inl (.inr (some i))) ^ 2) *
      rename Sum.inl (rename Sum.inl (vdm r) * rename Sum.inr (Vy * MvPolynomial.X none ^ n))) = 0 := by
    rw [← hV, map_sum, Finset.mul_sum, map_sum]
    simp only [map_smul, mul_smul_comm, map_pow, smul_eq_mul, key, mul_sub, Finset.sum_sub_distrib, b₃, b₁, sub_zero,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp only [mul_left_comm (c _), ← Finset.mul_sum, b₂ a, mul_zero]

  have hsum : ∑ z, ((x' z).pull W.π rfl).icls = -((LZ (.inr none)).pull γ v).icls := by
    have a₁ : ((LZ (.inr none)).pull γ v).icls = _ := HermLB.icls_eq_iff.2 (hNp N)
    have a₂ : ∑ z, (x' z).icls = (VMetric.det HX).icls := by
      rw [← sum_icls_grLB HX wf, ← e.sum_comp]
      exact Finset.sum_congr rfl fun z _ => (HermLB.icls_eq_iff.2 (hw z)).symm
    have a₃ : (VMetric.det HX).icls = _ := HermLB.icls_eq_iff.2 ((VMetric.isometric_det_pull (HL.pull π rfl) ρ rfl).trans
      ((VMetric.isometric_det_pull HL π rfl).pull ρ rfl))
    have a₄ := congrArg (HermLB.IsomClass.pull W.π rfl) (a₂.trans a₃)
    rw [map_sum] at a₄
    rw [a₁, HermLB.icls_pull _ W.π, HermLB.icls_pull _ ρ, HermLB.icls_pull N π, hN, map_neg, map_neg, map_neg, neg_neg]
    exact a₄
  have e₄ := apply_aeval HP.p4.arIso hW hΨ hΨ
    (fun i => if i = .inl (.inr none) then -∑ z, MvPolynomial.X (.inr z) else MvPolynomial.X i) (fun i => by
      split_ifs with hi
      · subst hi
        refine ⟨Sum.elim 0 fun _ => -1, by simp [lin], ?_⟩
        simp [Fintype.sum_sum_type, hsum]
      · exact ⟨Pi.single i 1, by simp [lin, Pi.single_apply, apply_ite], by simp [Pi.single_apply]⟩)
    ((∑ i, MvPolynomial.X (.inr (e.symm i)) ^ 2) *
      rename Sum.inl (rename Sum.inl (vdm r) * rename Sum.inr (Vy * MvPolynomial.X none ^ n)))
  have e₅ := FlagCmp.isArFun_restrict_inl HP.p4.arIso hW _ _ hΨ₀ hΨ (rename Sum.inl (vdm r) *
    rename Sum.inr ((∑ i : Fin g, MvPolynomial.X (some i) ^ 2) * Vy * MvPolynomial.X none ^ n))
  rw [LinearMap.smul_apply, e₁, smul_eq_mul, hdeg] at e₅
  rw [sub_mul, map_sub, sub_eq_zero, ← e₄] at e₃
  have hg : ((g.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have e₆ : ΦF (vdmPol g n) = (g.factorial : ℝ)⁻¹ *
      ΦF ((∑ i : Fin g, MvPolynomial.X (some i) ^ 2) * Vy * MvPolynomial.X none ^ n) := by
    rw [vdmPol, mul_assoc, mul_assoc, ← smul_eq_C_mul, map_smul, ← mul_assoc]
    rfl
  rw [Fintype.prod_unique] at e₂
  refine mul_left_cancel₀ hg (e₂.symm.trans (Eq.trans ?_ (e₃.trans (Eq.trans ?_ (e₅.trans ?_)))))
  · congr 1
    have a₁ : aeval (fun z => MvPolynomial.X (.inl (.inl z))) (vdm r) = (rename (fun z => .inl (.inl z)) (vdm r) :
        MvPolynomial (((Σ a, Fin (r a)) ⊕ Option (Fin g)) ⊕ (Σ a, Fin (r a))) ℝ) := by
      rw [rename_eq_aeval]; rfl
    rw [rename_vdm_unit fun i => Sum.inl (Sum.inr (some i)), e.symm.sum_comp fun z => MvPolynomial.X (Sum.inr z) ^ 2]
    simp only [pairPol, Vy, map_mul, map_sum, map_prod, map_sub, map_pow, map_neg, rename_X, aeval_X, rename_rename,
      aeval_rename, Function.comp_def, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq, if_false,
      if_true, a₁]
    ring
  · congr 1
    simp only [map_mul, map_sum, map_pow, rename_X]
    ring
  · rw [e₆]
    field_simp

theorem termW_eq_val : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → RegularAlteration → OnObj fun D O _ _ _ _ =>
    ∀ c (M : DRBase O c) (R : ℝ), 2 ≤ R → termW O c R =
      M.val R (genericPoint M.B) (dimGr D.what₂.Tau O.N O.j - 1) / (Module.finrank ℚ D.what₂.LL : ℝ) := by
  intro _ HP hH hR D O hO _ _ _ _ _ c M R hR2
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨V₀, _, j, hj, hdim, hr⟩ := exists_comp O c
  obtain ⟨B, Bg, q, jB, πB, ρ₀, hpre, hn, hloc⟩ := GlobalTheory.T.model_base_change_number_field O.s.T.Z O.κ.e j hj hdim
  rw [hr] at hpre
  have ⟨hq, hpb, hfin, hrg, hρ₀⟩ := hpre
  have := hq.isIntegral
  obtain ⟨β, hβ, w, hgen, hβd⟩ := GlobalTheory.T.exists_generic_map_to_moduli_base D O c M B Bg q jB πB ρ₀ hpre
  choose E t hvb hfr hlat using fun σ : D.host.E →+* ℂ =>
    exists_bundle O.s.T.Z O.κ.e hq hn hpb (O.S.Dw.mult σ) σ (ArIn.ind ∅) false (fun y => (hloc σ y).1)
  choose E' t' hvb' hfr' hgr using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.model_change_of_field_points_a O.s.T.Z O.κ.e hq hn hpb (O.S.Dw.mult σ) σ (fun y => (hloc σ y).2)
  choose u hg using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.model_change_of_field_points_b O.s.T.Z O.κ.e hq hn hpb (E σ) (E' σ) _ σ (t σ) (t' σ) (hvb σ) (hvb' σ) (hfr σ) (hfr' σ) (hlat σ)
      (hgr σ)
  let G : ∀ σ', EigMet O.s.T.Z σ' := fun σ' => M.x.eigMetAt σ' (some R)
  have hG : EigConj O.s.T.Z G := fun σ σ' y y' g g' τ hσ e hg => GlobalTheory.ShFam.ConjMet.eigMetAt_conj M.x hσ e hg τ _
  choose h hh using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.arithmetic_model_flag_height_fifth _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e B Bg q jB πB hpb (E σ) _ σ false rfl (t σ) G (hvb σ) (hfr σ) hG
  choose h' hh' using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.arithmetic_model_flag_height_fifth _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e B Bg q jB πB hpb (E' σ) _ σ false rfl (t' σ) G (hvb' σ) (hfr' σ) hG
  have hsm := O.s.T.smooth
  have hGs : ∀ σ', (G σ').SmoothOn (manifold O.s.T.Z σ') Set.univ := fun σ' =>
    ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ M.x σ' R hR2 (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ M.x σ')
  have H := fun σ => GlobalTheory.T.arithmetic_model_smooth_flag_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e B Bg q jB πB hpb (E σ) _ σ false rfl (t σ) G (h σ)
    (hfr σ) hGs (hh σ)
  have H' := fun σ => GlobalTheory.T.arithmetic_model_smooth_flag_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e B Bg q jB πB hpb (E' σ) _ σ false rfl (t' σ) G (h' σ)
    (hfr' σ) hGs (hh' σ)
  have hu := fun σ => GlobalTheory.T.model_change_of_field_points_c O.s.T.Z O.κ.e hpb (E σ) (E' σ) _ σ rfl (t σ) (t' σ) (u σ) G (h σ) (h' σ) (hvb σ)
    (hvb' σ) (hfr σ) (hfr' σ) (hg σ) (hh σ) (hh' σ)
  have hAt : PairAt O R c q E E' h h' u jB πB t t' G :=
    ⟨hpb, hfin, hrg, hfr, hfr', hg, hlat, hgr, fun σ n => by rw [M.core.hm_eq]; rfl, hh, hh'⟩
  have hsq : jB ≫ β ≫ M.b = πB ≫ genι O.s.T.Z := by rw [hβ, hρ₀]
  obtain ⟨V, Y, _, π, ρ, wV, fl, fl', hdeg, hY, hρ, hfl, hc, h₁, h₂⟩ :=
    GlobalTheory.T.eigen_metric_isometry_normal_base HP hH hR D O hO R hR2 c M B q E E' h h' H H' u hq hn hu Bg jB πB t t' hAt β w hsq hgen
  obtain ⟨n, hn1⟩ : ∃ n, dimGr D.what₂.Tau O.N O.j = n + 1 := by
    have hι : 0 < Fintype.card D.what₂.Tau := Fintype.card_pos_iff.2 ⟨D.eTau.symm (Classical.arbitrary _)⟩
    exact Nat.exists_eq_add_one.2 (Nat.mul_pos hι (Nat.mul_pos O.indef.1 (Nat.sub_pos_of_lt O.indef.2)))
  have hM := M.ar
  obtain ⟨hM₀, h₀, H₀, hs, hval⟩ := GlobalTheory.T.metric_descends_same_value _ _ (intEquiv O) M.B M.q _ hM _ _ _ ((M.H R).pull M.b rfl)
  have hgr := GlobalTheory.T.eigen_metric_comparison_normal_base D O hO R hR2 c M B q E E' h h' H H' u hq hn hu Bg jB πB t t' hAt β w hsq hgen h₀ hs
  obtain ⟨Φ, hΦ⟩ := ((HP.p4.arExists _ V.X V.p _ V.ar).2 _ (Sum.elim
    (fun z : Letter O.S.Dw => (VMetric.grLB (fl z.1) z.2 ((H z.1).pull π rfl)).pull ρ wV)
    fun z : Letter O.S.Dw => VMetric.grLB (fl' z.1) z.2 (((H' z.1).pull π rfl).pull ρ wV))).1
  rw [GlobalTheory.T.arithmetic_function_line_adeles HP.p4 hH.deg D O hO R hR2 c V _ _ h₁ h₂ Φ hΦ]
  rw [hn1] at hq hM hM₀
  rw [hn1, Nat.add_sub_cancel]
  have v₁ : M.F.IsVal ((M.H R).pull M.b rfl) (M.lam R) (genericPoint M.B) n (M.val R (genericPoint M.B) n) :=
    Classical.epsilon_spec ((T.flag_variety_value_unique HP.p4 _ M.B M.q _ hM _ _ _ ((M.H R).pull M.b rfl) M.F (M.lam R) _ n).1 (by
      rw [genericPoint_closure, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ M.B).isHomeomorph]
      exact hM.dim_eq)).exists
  obtain ⟨F', hF'⟩ := GlobalTheory.T.dual_flag_value_preserved HP.p4 _ M.B _ _ hM₀ _ _ h₀ H₀ M.F
  have := hq.isLocallyNoetherian
  obtain ⟨F₁⟩ := (T.flag_variety_arith_dimension _ B q _ hq _ _ (h₀.dual.pull β w).isVB).1
  have v₂ := GlobalTheory.T.flag_value_pullback_cover HP.p4 _ M.B B _ q n hM₀ β w ⟨w ▸ hq, hgen, hβd⟩ _ _ _ H₀.dual F' F₁ _ _
    (hF' _ n _ rfl (hval M.F _ n _ v₁))
  rw [apply_pairPol HP hR wV hq hY hρ H H' hu hfl hc (H₀.dual.pull β w) hgr F₁ (by
    rw [HermLB.icls_eq_iff.2 ((VMetric.isometric_det_pull H₀.dual β w).trans ((GlobalTheory.T.det_dual_metric_isometric _ _ _ _ _ h₀ H₀).pull β w))]
    simp only [HermLB.icls_pull, HermLB.icls_dual, map_neg, neg_neg]) v₂ hΦ, Cover.ν, hdeg]
  have a₁ : (ρ.residueDegree (genericPoint V.X) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hρ.2.2
  have a₂ : (β.residueDegree (genericPoint B) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hβd
  have a₃ : ∏ σ, ((O.S.Dw.mult σ).factorial : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => by positivity
  have a₄ : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast
  field_simp

end GlobalTheory.OrthFilt

end
