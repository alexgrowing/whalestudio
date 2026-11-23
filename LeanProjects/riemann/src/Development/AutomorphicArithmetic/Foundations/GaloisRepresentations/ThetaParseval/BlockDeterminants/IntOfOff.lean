import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.Decomp
import Development.WeilBound.ThetaLifts.LatticeBasics.CommuteTheta
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP

private theorem abs_tail {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n} {v : Pl F}

private theorem fix_off {g : UA σ X.J} (hg : OffAt v g) {z : Fin n → AE F E} (hz : At (evFin F v) z) : mat g *ᵥ z = z := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  have e : (mat g - 1) *ᵥ z = 0 := by
    rw [← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e
  exact e

private theorem int_of_off {g : UA σ X.J} (hg : OffAt v g) : IntAt v g := fun z hz h => by
  have e := fix_off hg h
  have e' : mat g⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← e]
    rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel]
    exact Matrix.one_mulVec z
  exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩

private theorem int_gOff {S : Finset (Pl F)} {c : UA σ X.J} (hc : c ∈ gOff σ X S) (hv : v ∈ S) : IntAt v c :=
  (Subgroup.closure_le (Euler.intGrp σ X v)).2 (fun _ hg => int_of_off (hg.2 v hv)) hc

private theorem int_gAt {S : Finset (Pl F)} {b : UA σ X.J} (hb : b ∈ gAt σ X S) (hv : v ∉ S) : IntAt v b := by
  have : gAt σ X S ≤ Euler.intGrp σ X v := iSup₂_le fun w hw x hx => by
    have hvw : v ≠ w := fun e => hv (e ▸ hw)
    have := (Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem
    rwa [mul_one] at this
  exact this hb

private theorem hgt_right {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (x : G2 σ X) {k : G2 σ X} (hk : k ∈ K) :
    a (x * k) = a x := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
  rw [mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']

end

end UpperTheory.TP

open UpperTheory.TP in
theorem UpperTheory.TP.tail :
    UpperTheory.TP.Tools → UpperTheory.TP.Tail := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀
  classical
  have := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA σ X.J
  have hL := hX.lat
  have dec := UpperTheory.TP.decomp T F E σ B n X hB hX
  let U : Set (UA σ X.J) := {g | IntAll g}
  have Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y) := fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)
  have Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹ := fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)
  have U1 : IntAll (1 : UA σ X.J) := fun v => (Euler.intGrp σ X v).one_mem
  obtain ⟨-, -, -, -, cU, oU, -, -, -⟩ := dec ∅
  have hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1)) := fun g u hu => by
    have : e (g * u, 1) = e (g, 1) * e (u, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, hgt_right ha _ (Bad.emb_mem hB hX (by simp) hK he hu)]
  have lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1)) := (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by
      have := hr g _ hx
      rwa [mul_inv_cancel_left] at this⟩
  let f : UA σ X.J → ENNReal := fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)
  have cf : Continuous f := (lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous
  let m : Measure (UA σ X.J) := μ.withDensity f
  have mfin : m Set.univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hi.lintegral_lt_top.ne
  let A : Finset (Pl F) → Set (UA σ X.J) := fun S => {g | ∀ v ∈ S, IntAt v g} \ U
  have mA : ∀ S, MeasurableSet (A S) := fun S => by
    refine MeasurableSet.diff ?_ oU.measurableSet
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL u).measurableSet
  have anti : Antitone A := fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩
  have emp : ⋂ S, A S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg
    exact (hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  have pos : 0 < μ U := oU.measure_pos μ ⟨1, U1⟩
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists
  refine ⟨S, hS, fun μC hC => ?_⟩
  obtain ⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩ := dec S
  have : LocallyCompactSpace (gInf σ X) := cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gAt σ X S) := cA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gOff σ X S) := cO.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (gInf σ X) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gAt σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gOff σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  let j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J :=
    { toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv
      continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      continuous_invFun := by
        have := j.symm.continuous
        exact ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }
  have hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1 := fun d c => hj (d.1, d.2, c)
  have hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1 := fun d => by rw [hj']; simp
  have hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1) := fun d c => by
    have := map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))
    rw [Prod.mk_mul_mk, one_mul, mul_one, hj1] at this
    rw [this, hj']
    simp
  have res := abs_tail j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1
    (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe)
    (fun d c hg => by
      have hx : IntAll d.1.1 := iI _ d.1.2
      have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
      have hb : IntAll d.2.1 := fun v => by
        by_cases hv : v ∈ S
        · have e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹ := by group
          rw [e1]
          exact (Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v))
            ((Euler.intGrp σ X v).inv_mem (int_gOff c.2 hv))
        · exact int_gAt d.2.2 hv
      have hxb := Um hx hb
      refine ⟨by rw [hj1]; exact hxb, ?_⟩
      show IntAll c.1
      have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
      rw [e2]
      exact Um (Ui hxb) hg')
    (fun d c hd hcK => by
      have hd' : IntAll (d.1.1 * d.2.1) := hj1 d ▸ hd
      refine ⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩
      · rw [hj']
        exact (Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff c.2 hv)
      · have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
        show IntAll c.1
        have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
        rw [e2]
        exact Um (Ui hd') hg'
      · show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)
        rw [hcm, hr _ _ hd'])
    (by
      rw [← withDensity_apply _ (mA S)]
      exact hlt)
  exact res

end
