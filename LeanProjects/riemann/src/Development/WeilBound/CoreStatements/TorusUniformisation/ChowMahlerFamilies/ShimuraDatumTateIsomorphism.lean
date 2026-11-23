import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ModuliNonemptyOfObj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.ShimuraDatumTate

open GlobalTheory GlobalTheory.PointUnif

theorem adj_of_weil {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {G : Over S}
    [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {act : OAct (𝓞 E) G} {L : LB G.left}
    {ty : Fin g → (E →+* ℂ)} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    {EF : LinearMap.BilinForm ℤ La} (hL : L.IsLB) (he : IsExp e) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hros : ∀ (k : ℕ) (x x' : Over.mk y ⟶ G) (a : 𝓞 E) (c : Γ((Over.mk y).left, ⊤)ˣ), x ^ k = 1 → x' ^ k = 1 →
      Out.WeilIs G L k (x ≫ act.act a) x' c → Out.WeilIs G L k x (x' ≫ act.act (H.bar a)) c)
    (c : 𝓞 E) (x x' : La) : EF (c • x) x' = EF x (H.bar c • x') := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ EF (c • x) x' - EF x (H.bar c • x') := fun n hn => by
    have e1 := hweil n (c • x) x' _ hn (expNegUnit_zpow_val n _)
    have e2 := hweil n x (H.bar c • x') _ hn (expNegUnit_zpow_val n _)
    rw [exp_div_smul hP hlin] at e1 e2
    have e3 := hros n _ _ c _ (exp_div_pow he hker hn x) (exp_div_pow he hker hn x') e1
    have f := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e3 e2
    rw [← (expNegUnit_isPrimitiveRoot hn).zpow_eq_one_iff_dvd, _root_.zpow_sub, f, mul_inv_cancel]
  exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (key _ (Nat.succ_pos (EF (c • x) x' - EF x (H.bar c • x')).natAbs))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))

theorem weil_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L]
    (t : SAB H (Sp L)) (ht : IsPrincipal t) (k : ℕ) (T : Over (Sp L)) (x x' : T ⟶ t.G) (a : 𝓞 E)
    (c : Γ(T.left, ⊤)ˣ) (hx : x ^ k = 1) (hx' : x' ^ k = 1)
    (h : Out.WeilIs t.G t.PP.L k (x ≫ t.act.act a) x' c) :
    Out.WeilIs t.G t.PP.L k x (x' ≫ t.act.act (H.bar a)) c := by
  letI := H.starRing
  exact (weilRosati abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.cube (Sp L) (SabModel.pol t ht) (𝓞 E)
    ⟨t.act.toRingAct, t.rosatiAdj⟩ k T x x' a c hx hx').1 h

end PositivityTheory.Xgn.ShimuraDatumTate

open GlobalTheory GlobalTheory.PointUnif PositivityTheory.Xgn.ShimuraDatumTate in
theorem PositivityTheory.Xgn.shimura_datum_tate_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) := by
  intro E _ _ _ H L _ t ht σ p q hdet
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' t (spMap σ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap σ) t⟩⟩
  have hLiso : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨hab, hamp, hkt⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally _ _ t.G t'.G
    (spMap σ) m.cm.F _ _ t.PP.isLB t'.PP.isLB (SabModel.pol t ht).isAb m.cart hLiso
  have ht' : IsPrincipal t' := ⟨hab.proper, hamp ht.2.1, hkt ht.2.2⟩
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    thetaUnifAV_all (SabModel.pol t' ht') t'.PP.rig t'.PP.rigGen
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (weilIs_iff_of_isGrpPullback_comm _ _ _ _ (spMap σ) m.cm.F _ _ t.PP.isLB t'.PP.isLB m.cart hLiso _) (spMap σ)
    (Category.id_comp _)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (t'.act.act a) (t'.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left _ _ _ (Φ _), hΦ]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => (u.ex z).left ≫ q) (m.act a)).trans
      (Category.assoc _ _ _).symm)
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 hφ)]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 hφ)]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := PeriodDatum.exists_datum E H u.Λ Ef p q g ty P Hm' hty hbij
    (adj_of_weil t.PP.isLB he hker hPs hlin hweil' fun k => weil_adj t ht k _) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  exact ⟨D', hp, hq, ⟨expTateIso he hper hker' hlin hweil''⟩⟩
