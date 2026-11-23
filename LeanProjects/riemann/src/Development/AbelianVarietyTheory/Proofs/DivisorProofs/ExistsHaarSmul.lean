import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisingTranslateCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteSupportMulLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaRegularizationComparison

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem standing {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) (hx : 11 ≤ D.host.splitBound) {μ₀ : T} (hL : L.Is μ₀)
    (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp => by
    have h := P.level_split p hp
    exact (Nat.Prime.coprime_iff_not_dvd hpp).2 (not_dvd_of_splitK hpp h)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem exists_haar_smul (V : HSp D) (ν ν' : Measure (GA D V)) (h : ν.IsHaarMeasure) (h' : ν'.IsHaarMeasure) :
    ∃ s : NNReal, s ≠ 0 ∧ ν' = s • ν := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact ⟨Measure.haarScalarFactor ν' ν, (Measure.haarScalarFactor_pos_of_isHaarMeasure ν' ν).ne',
    Measure.isMulLeftInvariant_eq_smul ν' ν⟩

theorem integral_change (V : HSp D) {ν ν' : Measure (GA D V)} {𝓕 𝓕' : Set (GA D V)} (h : GlobalTheory.SquareComm.IsHaarFD V ν 𝓕)
    (h' : GlobalTheory.SquareComm.IsHaarFD V ν' 𝓕') {s : NNReal} (hs : ν' = s • ν) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ u, f (γ * u) = f u) :
    (IntegrableOn f 𝓕 ν → IntegrableOn f 𝓕' ν') ∧ ∫ u in 𝓕', f u ∂ν' = ((s : ℝ) : ℂ) * ∫ u in 𝓕, f u ∂ν := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h'.1
  have h2 : IsFundamentalDomain (GQ V) 𝓕 ν' := h.2.mono (by rw [hs]; exact Measure.smul_absolutelyContinuous)
  have hinv : ∀ (γ : GQ V) (g : GA D V), f (γ • g) = f g := fun γ g => hf γ γ.2 g
  refine ⟨fun hi => (h2.integrableOn_iff h'.2 hinv).1 ?_, ?_⟩
  · rw [hs, IntegrableOn, Measure.restrict_smul]
    exact Integrable.smul_measure_nnreal hi
  · rw [h'.2.setIntegral_eq h2 hinv, hs, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]

open GlobalTheory.FinPl GlobalTheory.SmallKerInv in

theorem kerSmall_inv {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) :
    ∃ (Λ : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) Λ (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  set good : Pl D → Prop := fun v => Tame D v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t i j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t i j)) v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.chi (i : ℕ) j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.chi (i : ℕ) j)) v
    with hgood
  have hev : ∀ᶠ v : Pl D in Filter.cofinite, good v := by
    filter_upwards [GlobalTheory.FinPl.eventually_extUnram_two_notMem D,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecT.1,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecT.1]
      with v h0 h1 h2 h3 h4
    exact ⟨⟨h0.1, Or.inl h0.2⟩, h1, h2, h3, h4⟩
  have hfin : {v | ¬ good v}.Finite := Filter.eventually_cofinite.1 hev
  classical
  refine ⟨G.Λ (.grid i j), hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)),
    s0.1.fg, s0.1.span_eq_top, ?_⟩
  intro κ hκ u
  have hgd : ∀ v, v ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)) → good v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  have hoff : ∀ PP ∈ locPl G t,
      ¬ (PP.under (𝓞 D.host.F) ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F))) :=
    fun PP hPP h => h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  obtain ⟨⟨hsb1, hth1⟩, ⟨hsb2, hth2⟩⟩ := h1 d' hd'
  have hv1 := ρ.vT_is t i j i.2.le j.2
  have hv2 := ρ.vX_is i j i.2 j.2.le
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (u * κ) g _ = thetaKO (W.om (.mu t i j)) u g _
    unfold thetaKO
    have e1 : ((u * κ, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (u, g) * (κ, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.mu t i j) (u, g) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hm W.θ_is _ _ _
      (fun v hv => ⟨s0, s1, (hgd v hv).1, (hgd v hv).2.1, (hgd v hv).2.2.1⟩) e _ he hoff _ _ _
      hv1.2.theta hv1.2.lat hth1 _ _ _ _ _ κ 1 hκ (inK_one _ _ _)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (u * κ) _ = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u _
    unfold thetaKO
    have e2 : ((negGA _ g₁, u * κ) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (negGA _ g₁, u) * (1, κ) := by simp
    rw [e2, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.chi (i : ℕ) j) (negGA _ g₁, u) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hc W.θ_is _ _ _
      (fun v hv => ⟨isSelfDualC_neg s2, s0, (hgd v hv).1, (hgd v hv).2.2.2.1, (hgd v hv).2.2.2.2⟩) e _ he hoff _ _ _
      hv2.2.theta hv2.2.lat hth2 _ _ _ _ _ 1 κ (inK_one _ _ _) hκ

theorem exists_reg_at (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) (hM : M.Is t) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v ∉ P, ∃ w : GA D (G.V (.grid i j)) →₀ ℂ, zdeg w ≠ 0 ∧
      IntegrableOn (translates w (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) ∧
      ∀ b ∈ w.support, b ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig (G.V (.grid i j)).gram v) := by
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv, hvP⟩ := GlobalTheory.RegAt.squareTriple_avoid hL W t i j hst P M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid, hsupp⟩ :=
    GlobalTheory.RegAt.translates_kerSmall_le_theta_at hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL W B ρ t i j Θ Θ' hΘ g₁ z
  exact ⟨Bs.v₁, hvP, z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd), hsupp⟩

open GlobalTheory.SmallConst in

theorem reg_const (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) (hM : M.Is t) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) :
    ∃ J : ℂ, ∀ z, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) →
      ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ = zdeg z * J := by
  classical
  have k2 := exists_reg_at hK hL W B ρ t i j hst M hM Θ Θ' hΘ g g₁
  obtain ⟨Λ, S, hfg, hsp, hright⟩ := kerSmall_inv hL W B ρ t i j Θ Θ' hΘ g g₁
  choose b' Pb hPb hKb using fun b => GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer (G.V (.grid i j)) Λ hfg hsp S b
  have hinv := kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁
  set f := kerSmall W Θ' g g₁ with hf
  have kb : ∀ b u, f (u * b' b) = f (u * b) := fun b u => by
    have := hright _ (hKb b) (u * b' b)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  have hfd := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI := hfd.1
  have key := zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv
  obtain ⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩ := k2 ∅
  refine ⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩
  have hz'f : translates (z.mapDomain b') f = translates z f := by
    funext u
    simp only [translates]
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finsupp.sum_congr fun b _ => by rw [kb]
  have hz'd : zdeg (z.mapDomain b') = zdeg z := by
    simp only [zdeg]
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  obtain ⟨v, hv, w, hw, hi, hs⟩ := k2 (insert v₀ (z.support.biUnion Pb))
  have hv0 : v ≠ v₀ := fun h => hv (h ▸ Finset.mem_insert_self _ _)
  have c1 : ∀ x ∈ w.support, ∀ y ∈ (z.mapDomain b').support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (hPb b v fun h => hv (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨b, hb, h⟩)))
  have c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨y', rfl⟩ := hs₀ y hy
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')
  have e1 := key w _ c1 hi (by rw [hz'f]; exact hz)
  have e2 := key w w₀ c2 hi hi₀
  rw [hz'f, hz'd] at e1
  rw [mul_div_assoc', eq_div_iff hw₀]
  apply mul_left_cancel₀ hw
  linear_combination zdeg w₀ * e1 - zdeg z * e2

end GlobalTheory.ThetaRegularizationComparison

end
