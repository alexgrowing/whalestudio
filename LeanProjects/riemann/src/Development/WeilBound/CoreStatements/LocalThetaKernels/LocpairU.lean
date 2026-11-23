import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairUnit
import Development.WeilBound.ThetaLifts.CartanFactorisation.MaxDef

noncomputable section

namespace PositivityTheory.ThKH.Locpair

open scoped Matrix TensorProduct GlobalTheory.VacAny
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK PositivityTheory.ThKH.Locrep
open MeasureTheory

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {ψ : AddChar (AF F) ℂ}
  [LocallyCompactSpace (Fv F v)]

section Gen

variable {G : Type} [Group G] {om : G →* Module.End ℂ ((κ → AF F) → ℂ)} {omv : G →* Module.End ℂ ((κ → Fv F v) → ℂ)}

theorem cont_loc [TopologicalSpace G] (ho : IsLocOm v om omv) (h : IsContOn (adeleClass F) om) :
    IsContOn (sbClass (Fv F v)) omv := by
  intro l _ φ hφ
  obtain ⟨r₀, x₀, hr₀, h₁⟩ := PositivityTheory.ThKH.Locrep.exists_base κ v
  have key : (fun g => l (omv g φ)) =
      fun g => (l ∘ₗ PositivityTheory.ThKH.Locrep.res v x₀) (om g (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r₀)) := by
    funext g
    rw [LinearMap.comp_apply, ← PositivityTheory.ThKH.Locrep.eq_of_acts v h₁ (hr₀ φ hφ) (ho g φ hφ).2]
  rw [key]
  exact h _ (PositivityTheory.ThKH.Locrep.res_adm v x₀ l) _ (hr₀ φ hφ).2

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem unit_loc (ho : IsLocOm v om omv) (h : IsUnitaryOn (adeleClass F) om) : IsUnitaryOn (sbClass (Fv F v)) omv := by
  intro μ hμ g φ hφ
  let _ : MeasurableSpace (κ → AF F) := borel _
  have : BorelSpace (κ → AF F) := ⟨rfl⟩
  let _ : MeasurableSpace (κ → Fv F v) := borel _
  have : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  obtain ⟨Φ₀, hΦ₀, hc0, hcs, h0⟩ := GlobalTheory.CompanionTheory.SplitRatio.exists_schA_compact F κ
  have hev : Continuous ⇑(PositivityTheory.ThKH.Locrep.evA κ v) :=
    continuous_pi fun i => (PositivityTheory.ThKH.Locrep.continuous_evFin' v).comp (continuous_apply i)
  have hin : Continuous ⇑(PositivityTheory.ThKH.Locrep.inA κ v) :=
    continuous_pi fun i => (GlobalTheory.VacAny.continuous_atPlace v).comp (continuous_apply i)
  obtain ⟨c, hc, hfac⟩ := exists_factor (PositivityTheory.ThKH.Locrep.evA_inA v) hev hin
    (MeasureTheory.Measure.addHaar : MeasureTheory.Measure (κ → AF F)) μ hc0 hcs h0
  let r : (κ → AF F) → ℂ := fun x => Φ₀ (PositivityTheory.ThKH.Locrep.putA v x 0)
  have hT : ∀ φ' : (κ → Fv F v) → ℂ,
      PositivityTheory.ThKH.Locrep.Pm (PositivityTheory.ThKH.Locrep.evA κ v) (PositivityTheory.ThKH.Locrep.inA κ v) φ' 0 Φ₀ =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ' r := fun φ' => rfl
  have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · simp only [r, PositivityTheory.ThKH.Locrep.putA_add v hz]
    · rw [← hT]
      exact PositivityTheory.ThKH.Locrep.PA_mem v hφ 0 hΦ₀
  have hom : om g (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) (omv g φ) r :=
    (ho g φ hφ).2 r hrest
  have e1 := hfac φ hφ.1.continuous
  have e2 := hfac (omv g φ) (ho g φ hφ).1.1.continuous
  have e3 := h MeasureTheory.Measure.addHaar inferInstance g _ hrest.2
  rw [hT] at e1 e2
  rw [hom] at e3
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  refine (ENNReal.mul_right_inj hc' ENNReal.coe_ne_top).mp ?_
  rw [← e1, ← e2]
  exact e3

end Gen

variable [IsModuleTopology (Fv F v) (Ev E v)] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)}
  {JAv : Matrix α α (Ev E v)} {JBv : Matrix β β (Ev E v)} {co : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
  {dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) JAv JBv) κ} {om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)}
  {omv : UG (cV σ v) JBv →* Module.End ℂ ((κ → Fv F v) → ℂ)}

omit [DecidableEq α] in
theorem uweilB_loc (hψ : IsStd ψ) (hA : JA.map (compFin F E v) = JAv) (hB : JB.map (compFin F E v) = JBv) (h : IsLocD co dv)
    (ho : IsLocOm v (om.comp (liftU hB)) omv) {χ : Chr F E} (hw : IsUWeilB (cA σ) (adeleClass F) ψ (-1) JA JB co χ om) :
    IsUWeilB (cV σ v) (sbClass (Fv F v)) (GlobalTheory.VacAny.psiV ψ v) (-1) JAv JBv dv (locChr v χ) omv := by
  obtain ⟨hs, dd, omd, hdd, ⟨hlagr, hus, hsr⟩, hbox⟩ := hw
  obtain ⟨ddv, omdv, hlocd, hddv, hsd, hsrv, hboxv⟩ :=
    dbl_loc hψ hA hB h ho hdd hus.toIsSplitting hsr hbox
  refine ⟨⟨split_loc hψ hB h hs.toIsSplitting ho, unit_loc ho ?_, cont_loc ho ?_⟩, ddv, omdv, hddv,
    ⟨?_, ⟨hsd, unit_loc hlocd ?_, cont_loc hlocd ?_⟩, hsrv⟩, hboxv⟩
  · exact fun μ hμ g φ hφ => hs.unit μ hμ _ φ hφ
  · exact fun l hl φ hφ => (hs.cont l hl φ hφ).comp (continuous_liftU hB)
  · obtain ⟨h1, Cx, Mx, h2, h3, h4⟩ := hlagr
    have hD : (GlobalTheory.WeilM.diagCols β : Matrix (β ⊕ β) β (AE F E)).map (compFin F E v) =
        GlobalTheory.WeilM.diagCols β := by
      ext i j
      rcases i with i | i <;> simp [GlobalTheory.WeilM.diagCols, Matrix.one_apply, apply_ite]
    have hF : ∀ X : Matrix (β ⊕ β) β (AE F E),
        ((GlobalTheory.WeilM.diagCols β).fromCols X).map (compFin F E v) =
          (GlobalTheory.WeilM.diagCols β).fromCols (X.map (compFin F E v)) := by
      intro X
      rw [← hD]
      ext i j
      rcases j with j | j <;> rfl
    refine ⟨?_, Cx.map (compFin F E v), Mx.map (compFin F E v), ?_, ?_, ?_⟩
    · have e := congrArg (fun M => M.map (compFin F E v)) h1
      simp only [Matrix.map_mul, Matrix.transpose_map, compM_cA, hD, comp_dbl hB, Matrix.map_zero,
        map_zero] at e
      exact e
    · have e := congrArg (fun M => M.map (compFin F E v)) h2
      simp only [Matrix.map_mul, Matrix.transpose_map, compM_cA, comp_dbl hB, Matrix.map_zero,
        map_zero] at e
      exact e
    · have e := congrArg (fun M => M.map (compFin F E v)) h3
      simp only [Matrix.map_mul, hF, Matrix.map_one, map_zero, map_one] at e
      exact e
    · have e := congrArg (fun M => M.map (compFin F E v)) h4
      simp only [Matrix.map_mul, hF, Matrix.map_one, map_zero, map_one] at e
      exact e
  · exact fun μ hμ g φ hφ => hus.unit μ hμ _ φ hφ
  · exact fun l hl φ hφ => (hus.cont l hl φ hφ).comp (continuous_liftU _)

theorem locUPairEx : PositivityTheory.ThKF.LocUPairEx := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hP hw v _ i2 _
  obtain rfl : i2 = GlobalTheory.VacAny.invTwoV v := Subsingleton.elim _ _
  have hψ := hP.base.std
  obtain ⟨dv, omv, hd, ho, o1, o2, h⟩ := locPair_core (v := v) hψ hw
  obtain ⟨w1, ⟨d', hd', w2⟩, w3⟩ := hw
  obtain ⟨dv', hdv'⟩ := exists_locD (comp_incM (v := v) W.J) (comp_incM X.J) d'
  have hc : Continuous ((liftU (σ := σ) (comp_incM (v := v) X.J)).prodMap (liftU (σ := σ) (comp_incM (v := v) W.J))) :=
    Continuous.prodMap (continuous_liftU (σ := σ) (comp_incM (v := v) X.J)) (continuous_liftU (σ := σ) (comp_incM (v := v) W.J))
  refine ⟨_, dv, _, _, omv, h, uweilB_loc hψ (comp_incM X.J) (comp_incM W.J) hd o1 w1,
    ⟨dv', fun x => ?_, uweilB_loc hψ (comp_incM W.J) (comp_incM X.J) hdv' o2 w2⟩, cont_loc ho (w3.comp hc)⟩
  rw [← comp_up v x, ← Matrix.transpose_map, hdv', hd, hd']

end PositivityTheory.ThKH.Locpair
