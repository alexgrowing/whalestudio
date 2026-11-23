import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagDomainCellCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityPropertiesStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open MeasureTheory Filter Topology Matrix NumberField ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FdPiece

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem bad_null (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0) (hx : IsOrth X x)
    {FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd X))} (hF : IsFundSet X x0 FF) :
    volume {w | w ∈ OmF X x ∧ ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
      cpt X x w ≠ lact γ (rmul (cpt X x0 z') b)} = 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  set Sat : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, lact (γ : GL (Fin r) E)⁻¹ ⁻¹' KU.Sset X x0 FF with hSat
  have hSm : MeasurableSet Sat :=
    MeasurableSet.iUnion fun γ => (KU.cont_lact X _).measurable (KU.meas_S X h0 hF.1)
  have hB : ∀ y, ∀ b ∈ Bor X.Ψ r, rmul y b ∈ Sat ↔ y ∈ Sat := fun y b hb => by
    simp only [hSat, Set.mem_iUnion, Set.mem_preimage]
    refine exists_congr fun γ => ?_
    rw [KU.lact_rmul' X, KU.rmul_mem_S X hb]
  have hin : ∀ γ ∈ X.Γ, ∀ z' ∈ FF, ∀ b ∈ Bor X.Ψ r, lact γ (rmul (cpt X x0 z') b) ∈ Sat :=
    fun γ hγ z' hz' b hb => Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨(z', b), ⟨hz', hb⟩, by
      show rmul (cpt X x0 z') b = lact γ⁻¹ (lact γ _)
      rw [← FundSetPf.lact_mul, inv_mul_cancel, FundSetPf.lact_one]⟩⟩
  have hout : ∀ y ∈ Sat, ∃ γ ∈ X.Γ, ∃ z' ∈ FF, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul (cpt X x0 z') b) := by
    intro y hy
    obtain ⟨γ, ⟨z', b⟩, ⟨hz', hb⟩, e⟩ := Set.mem_iUnion.1 hy
    refine ⟨γ, γ.2, z', hz', b, hb, ?_⟩
    have e' : rmul (cpt X x0 z') b = lact (γ : GL (Fin r) E)⁻¹ y := e
    rw [e', ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  have hφ : Measurable ((Satᶜ).indicator (1 : Frame X.Ψ r → ENNReal)) :=
    measurable_one.indicator hSm.compl
  have hinv := measInv_holds r X x0 x h0 hx _ hφ (fun y _ b hb => by
    by_cases hy : y ∈ Sat
    · rw [Set.indicator_of_notMem (by simpa using (hB y b hb).2 hy),
        Set.indicator_of_notMem (by simpa using hy)]
    · rw [Set.indicator_of_mem (by simpa using fun h => hy ((hB y b hb).1 h)),
        Set.indicator_of_mem (by simpa using hy)]
      rfl)
  have e : ∀ x' : Frame X.Ψ r, ∫⁻ z, (Satᶜ).indicator (1 : Frame X.Ψ r → ENNReal) (cpt X x' z) ∂muF X x' =
      muF X x' (cpt X x' ⁻¹' Satᶜ) := fun x' => by
    rw [← lintegral_indicator_one ((KU.cont_cpt X x').measurable hSm.compl)]
    rfl
  rw [e, e] at hinv
  have hl : muF X x0 (cpt X x0 ⁻¹' Satᶜ) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 hF.2.2.2)
    exact fun ⟨z', hz', γ, hγ, b, hb, h⟩ => hz (h ▸ hin γ hγ z' hz' b hb)
  rw [hl] at hinv
  have hr := (withDensity_apply_eq_zero (OntoC.measurable_densF X x)).1 hinv.symm
  have hr2 := nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hr.le)
  refine measure_mono_null (fun w hw => ?_) hr2
  refine ⟨⟨?_, fun hs => ?_⟩, hw.1⟩
  · simpa using OntoB.densF_pos hw.1
  · obtain ⟨γ, hγ, z', hz', b, hb, h⟩ := hout _ hs
    exact hw.2 z' hz' γ hγ b hb h

theorem exists_cells (X : Data E r) : ∃ C : Set (Frame X.Ψ r), C.Countable ∧ (∀ x ∈ C, IsOrth X x) ∧
    ∀ y ∈ X.dom, ∃ x ∈ C, ∃ w ∈ OmF X x, ∃ b ∈ Bor X.Ψ r, y = rmul (cpt X x w) b := by
  have hlu := fun x : {x : Frame X.Ψ r // IsOrth X x} => lu_holds r X x.1 x.2
  choose Δ zOf bOf hD _ _ _ hsplit hinv using hlu
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun x => {y | Δ x y ≠ 0})
    (fun x => isOpen_ne_fun (hD x).continuous continuous_const)
  refine ⟨Subtype.val '' T, hTc.image _, ?_, fun y hy => ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  obtain ⟨x1, h1, b, hb, e⟩ := ortho_holds r X y hy
  have hz : (0 : ReciprocityTheory.L2DbarEstimates.V (nd X)) ∈ OmF X x1 := by
    show cpt X x1 0 ∈ X.dom
    rw [PoinPf.cpt_zero]
    exact PoinPf.orth_mem_dom X h1
  have hy' : y ∈ ⋃ x, {y | Δ x y ≠ 0} := Set.mem_iUnion.2 ⟨⟨x1, h1⟩, by
    have := (hinv ⟨x1, h1⟩ 0 hz b hb).1
    rwa [PoinPf.cpt_zero, ← e] at this⟩
  rw [← hT] at hy'
  obtain ⟨x, hxT, hne⟩ := Set.mem_iUnion₂.1 hy'
  obtain ⟨h2, h3, h4⟩ := hsplit x y hy hne
  exact ⟨x.1, ⟨x, hxT, rfl⟩, _, h2, _, h3, h4⟩

theorem isNull_image {e : ℕ} {Y : Type} [TopologicalSpace Y] (A : FinHolAtlas e Y)
    {D Z : Set (Fin e → ℂ)} {Φ : (Fin e → ℂ) → Y}
    (hP : ∀ z ∈ D, ∃ W, z ∈ W ∧ W ⊆ D ∧ IsParam A W Φ) (hZ : Z ⊆ D) (h0 : volume Z = 0) :
    IsNull A (Φ '' Z) := by
  choose! W hzW _ hWp using hP
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun z : D => W z)
    (fun z => (hWp z z.2).1)
  intro j
  have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' (Φ '' Z) ⊆
      ⋃ t ∈ T, (A.chart j ∘ Φ) '' (Z ∩ (W t ∩ Φ ⁻¹' (A.chart j).source)) := by
    rintro u ⟨hu, z, hz, e⟩
    have hz' : z ∈ ⋃ t : D, W t := Set.mem_iUnion.2 ⟨⟨z, hZ hz⟩, hzW z (hZ hz)⟩
    rw [← hT] at hz'
    obtain ⟨t, ht, hzt⟩ := Set.mem_iUnion₂.1 hz'
    refine Set.mem_iUnion₂.2 ⟨t, ht, z, ⟨hz, hzt, ?_⟩, ?_⟩
    · show Φ z ∈ (A.chart j).source
      rw [e]
      exact (A.chart j).map_target hu
    · show A.chart j (Φ z) = u
      rw [e]
      exact (A.chart j).right_inv hu
  refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).2 fun t _ => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun z hz => ?_)
    (measure_mono_null Set.inter_subset_left h0)
  exact (((hWp t t.2).2.2.2 j z hz.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt

def sg (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e) :
    Fin (nd X) ≃ Fin e :=
  (Fintype.equivFin (Ent X)).symm.trans ((Equiv.prodCongr lab (Equiv.refl _)).symm.trans q)

def cc (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ) (q : LowEnt Ψ r ≃ Fin e)
    (z : Fin e → ℂ) : ReciprocityTheory.L2DbarEstimates.V (nd X) :=
  WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr lab (Equiv.refl _)).symm ((Fintype.equivFin (Ent X)).symm i)))

theorem cc_preserving (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : MeasurePreserving (cc X lab q) volume volume := by
  have h : MeasurePreserving (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm) :
      (Fin e → ℂ) → (Fin (nd X) → ℂ)) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm
  have ht : MeasurePreserving (WithLp.toLp 2 : (Fin (nd X) → ℂ) → ReciprocityTheory.L2DbarEstimates.V (nd X)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (nd X) → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin (nd X)))
  have e : (cc X lab q) = WithLp.toLp 2 ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin (nd X) => ℂ) (sg X lab q).symm) := by
    funext z
    refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sg]
    rfl
  rw [e]
  exact ht.comp h

theorem cc_injective (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : Function.Injective (cc X lab q) := by
  intro z z' h
  have h1 : ∀ i, z (sg X lab q i) = z' (sg X lab q i) := fun i => congrFun (WithLp.toLp_injective 2 h) i
  funext a
  simpa using h1 ((sg X lab q).symm a)

theorem cc_surjective (X : Data E r) {Ψ : Type} [Fintype Ψ] {e : ℕ} (lab : Ψ ≃ X.Ψ)
    (q : LowEnt Ψ r ≃ Fin e) : Function.Surjective (cc X lab q) := by
  intro w
  refine ⟨fun a => w.ofLp ((sg X lab q).symm a), ?_⟩
  have : (fun i => w.ofLp ((sg X lab q).symm (sg X lab q i))) = w.ofLp := funext fun i => by simp
  exact (congrArg (WithLp.toLp 2) this).trans rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N j e n : ℕ) (Ψ : Type) [Fintype Ψ] (S : AnSys e (Ψ × Fin N)) (X : Fin n → Data E N) (x0 : ∀ k, Frame (X k).Ψ N) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k)))) (lab : ∀ k, Ψ ≃ (X k).Ψ) (q : LowEnt Ψ N ≃ Fin e) (pr : ∀ k, Frame (X k).Ψ N → S.X), j ≤ N → (∀ k, (X k).p0 = N - j ∧ IsOrth (X k) (x0 k) ∧ IsFundSet (X k) (x0 k) (FF k)) → (∀ y : S.X, y ∈ S.open' ↔ ∃ k, ∃ x ∈ (X k).dom, pr k x = y) → (∀ k k', ∀ x ∈ (X k).dom, ∀ x' ∈ (X k').dom, pr k x = pr k' x' → k = k') → (∀ k (x x' : (X k).dom), pr k x.1 = pr k x'.1 ↔ ReciprocityTheory.ChartRestriction.G.AR.Inst.Rel (X k) x x') → (∀ k (x : Frame (X k).Ψ N), IsOrth (X k) x → ∀ z ∈ cellDom j q, (∃ W, z ∈ W ∧ W ⊆ cellDom j q ∧ IsParam S.A W fun z' => pr k (cpt (X k) x (WithLp.toLp 2 fun i => z' (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) ∧ ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ z' in 𝓝 z, (S.potH p).φ (pr k (cpt (X k) x (WithLp.toLp 2 fun i => z (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) (pr k (cpt (X k) x (WithLp.toLp 2 fun i => z' (q ((Equiv.prodCongr (lab k) (Equiv.refl _)).symm ((Fintype.equivFin (Ent (X k))).symm i))) : ReciprocityTheory.L2DbarEstimates.V (nd (X k))))) = stepPot N j p.2 (lowMat q z' p.1) + (G z').re) → ∃ U : PieceUnif S j n, ∀ k, U.vol k = muF (X k) (x0 k) (FF k) := by
  intro E _ _ _ N j e n Ψ _ S X x0 FF lab q pr hj hX hcov hdisj hrel hloc
  have hbr : ∀ k (x : Frame (X k).Ψ N), IsOrth (X k) x →
      (∀ z : Fin e → ℂ, z ∈ cellDom j q ↔ cc (X k) (lab k) q z ∈ OmF (X k) x) ∧
      ∀ F : Set (ReciprocityTheory.L2DbarEstimates.V (nd (X k))), MeasurableSet F → F ⊆ OmF (X k) x →
        muF (X k) x F = cellVol j q (cc (X k) (lab k) q ⁻¹' F) := fun k x hx =>
    GlobalTheory.T.flag_domain_cell_coordinates E N j e (X k) x Ψ (lab k) q hx hj (hX k).1
  have hrelcpt : ∀ k {y y' : Frame (X k).Ψ N}, y ∈ (X k).dom → y' ∈ (X k).dom →
      ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N, y' = lact γ (rmul y b) → pr k y = pr k y' :=
    fun k y y' hy hy' γ hγ b hb h => (hrel k ⟨y, hy⟩ ⟨y', hy'⟩).2 ⟨γ, hγ, b, hb, h⟩
  have hopen := (GlobalTheory.T.analytic_system_regularity_properties e (Ψ × Fin N) S).2.1
  have hcells := fun k => exists_cells (X k)
  choose C hCc hCo hCcov using hcells
  have hnull : ∀ k, ∀ x ∈ C k, IsNull S.A ((fun z => pr k (cpt (X k) x (cc (X k) (lab k) q z))) ''
      (cc (X k) (lab k) q ⁻¹' {w | w ∈ OmF (X k) x ∧ ∀ z' ∈ FF k, ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N,
        cpt (X k) x w ≠ lact γ (rmul (cpt (X k) (x0 k) z') b)})) := by
    intro k x hx
    have ho := hCo k x hx
    refine isNull_image S.A (D := cellDom j q) (fun z hz => (hloc k x ho z hz).1)
      (fun z hz => ((hbr k x ho).1 z).2 hz.1) ?_
    exact (cc_preserving (X k) (lab k) q).quasiMeasurePreserving.preimage_null
      (bad_null (X k) (hX k).2.1 ho (hX k).2.2)
  refine ⟨{ q := fun _ => q
            π := fun k z => pr k (cpt (X k) (x0 k) (cc (X k) (lab k) q z))
            FF := fun k => cc (X k) (lab k) q ⁻¹' FF k
            mem_open := ?_, param := ?_, pot := ?_, meas := ?_, sub := ?_, inj := ?_, disj := ?_, cover := ?_ }, ?_⟩
  · intro k z hz
    exact (hcov _).2 ⟨k, _, ((hbr k _ (hX k).2.1).1 z).1 hz, rfl⟩
  · intro k z hz
    exact (hloc k _ (hX k).2.1 z hz).1
  · intro k z hz p
    exact (hloc k _ (hX k).2.1 z hz).2 p
  · intro k
    exact (cc_preserving (X k) (lab k) q).measurable (hX k).2.2.1
  · intro k z hz
    exact ((hbr k _ (hX k).2.1).1 z).2 ((hX k).2.2.2.1 hz)
  · intro k z hz z' hz' h
    have hO := (hX k).2.2.2.1
    obtain ⟨γ, hγ, b, hb, e'⟩ := (hrel k ⟨_, hO hz⟩ ⟨_, hO hz'⟩).1 h
    exact cc_injective (X k) (lab k) q ((hX k).2.2.2.2.1 _ hz _ hz' γ hγ b hb e')
  · intro k k' hk
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', e'⟩
    exact hk (hdisj k' k _ ((hX k').2.2.2.1 hz') _ ((hX k).2.2.2.1 hz) e').symm
  · have hsub : (⋃ k, (fun z => pr k (cpt (X k) (x0 k) (cc (X k) (lab k) q z))) '' (cc (X k) (lab k) q ⁻¹' FF k))ᶜ ⊆
        S.open'ᶜ ∪ ⋃ k, ⋃ x ∈ C k, (fun z => pr k (cpt (X k) x (cc (X k) (lab k) q z))) ''
          (cc (X k) (lab k) q ⁻¹' {w | w ∈ OmF (X k) x ∧ ∀ z' ∈ FF k, ∀ γ ∈ (X k).Γ, ∀ b ∈ Bor (X k).Ψ N,
            cpt (X k) x w ≠ lact γ (rmul (cpt (X k) (x0 k) z') b)}) := by
      intro y hy
      by_cases hyo : y ∈ S.open'
      swap
      · exact Or.inl hyo
      refine Or.inr ?_
      obtain ⟨k, x', hx', rfl⟩ := (hcov y).1 hyo
      obtain ⟨x, hxC, w, hw, b, hb, e'⟩ := hCcov k x' hx'
      have h1 : pr k (cpt (X k) x w) = pr k x' :=
        hrelcpt k hw hx' 1 (X k).Γ.one_mem b hb (by rw [FundSetPf.lact_one]; exact e')
      obtain ⟨u, rfl⟩ := cc_surjective (X k) (lab k) q w
      refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion₂.2 ⟨x, hxC, u, ⟨hw, ?_⟩, h1⟩⟩
      intro z' hz' γ hγ b' hb' e2
      obtain ⟨u', rfl⟩ := cc_surjective (X k) (lab k) q z'
      refine hy (Set.mem_iUnion.2 ⟨k, u', hz', ?_⟩)
      exact (hrelcpt k ((hX k).2.2.2.1 hz') hw γ hγ b' hb' e2).trans h1
    intro a
    refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono hsub)) ?_
    rw [Set.preimage_union, Set.inter_union_distrib_left]
    refine measure_union_null (hopen a) ?_
    simp only [Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun k => (measure_biUnion_null_iff (hCc k)).2 fun x hx => hnull k x hx a
  · intro k
    exact ((hbr k _ (hX k).2.1).2 _ (hX k).2.2.1 (hX k).2.2.2.1).symm

end GlobalTheory.CompanionTheory.Ar.Cmp.FdPiece
