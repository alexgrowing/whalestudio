import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfJ

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB ReciprocityTheory.ChartRestriction.G.AR.Up.OntoH
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoI ReciprocityTheory.ChartRestriction.G.AR.Up.OntoJ
open scoped ComplexConjugate ContDiff ENNReal InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem onto_of (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E))
    (hGrad : RhGradFStatement (E := E)) (hExG : ExhaustGStatement (E := E))
    (hKa : KaUnfoldStatement (E := E)) (hPair : PairUnfoldStatement (E := E))
    (hBig : BigCellStatement (E := E)) (hConn : OmFConnStatement (E := E)) :
    OntoStatement (E := E) := by
  intro r X x0 hx0 hPD la W Ps g1 bb m hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hSS FF hFF hfin
    f hf hfF
  obtain ⟨K, g, hg⟩ := hfin
  have hWm : Measurable W := hW.1
  have hPo := fun (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ)
      (hD : OntoJ.Dt X x0 W bb la F P) =>
    hPoin r X x0 hx0 hPD la W bb hW hWL hbb4 F P hD.1 hD.2.1 hD.2.2.1 hD.2.2.2
  have hae : ∀ᵐ z ∂(OntoI.nuF X x0 W FF), z ∈ FF := by
    have h1 : ∀ᵐ z ∂((muF X x0).restrict FF), z ∈ FF := ae_restrict_mem hFF.1
    first
      | exact (withDensity_absolutelyContinuous _ _).ae_le h1
      | (unfold OntoI.nuF; exact (withDensity_absolutelyContinuous _ _).ae_le h1)
  have hmemP : ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), OntoJ.Dt X x0 W bb la F P →
      MemLp (fun z => poin X la P (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := fun F P hD =>
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      (hPo F P hD).2.1.1.1.continuousOn ((hPo F P hD).2.2.1 FF hFF)
  have hmemf : MemLp (fun z => f (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    OntoI.memLp_of (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm
      hf.1.1.1.continuousOn hfF
  have hzero : MemLp (fun z => (0 : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) := by
    refine (hmemP _ _ (OntoJ.Dt_zero X x0)).ae_eq (ae_of_all _ fun z => ?_)
    exact OntoI.poin_zero (r := r) (X := X) la _

  obtain ⟨M, hMmem⟩ : ∃ M : Submodule ℂ (Lp ℂ 2 (OntoI.nuF X x0 W FF)), ∀ v, v ∈ M ↔
      ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), OntoJ.Dt X x0 W bb la F P ∧
        v = OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P (cpt X x0 z)) := by
    refine ⟨{ carrier := {v | ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ),
                OntoJ.Dt X x0 W bb la F P ∧
                v = OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P (cpt X x0 z))}
              add_mem' := by
                rintro _ _ ⟨F1, P1, hD1, rfl⟩ ⟨F2, P2, hD2, rfl⟩
                refine ⟨_, _, OntoJ.Dt_add (r := r) (X := X) (x0 := x0) hWm hD1 hD2, ?_⟩
                rw [← OntoJ.TL_add (hmemP F1 P1 hD1) (hmemP F2 P2 hD2)]
                refine OntoJ.TL_congr ((hmemP F1 P1 hD1).add (hmemP F2 P2 hD2)) ?_
                filter_upwards [hae] with z hz
                have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
                show poin X la P1 (cpt X x0 z) + poin X la P2 (cpt X x0 z) =
                  poin X la (fun y => P1 y + P2 y) (cpt X x0 z)
                exact (OntoI.poin_add (r := r) (X := X) la ((hPo F1 P1 hD1).1 _ hx)
                  ((hPo F2 P2 hD2).1 _ hx)).symm
              zero_mem' := ⟨fun _ => 0, fun _ => 0, OntoJ.Dt_zero X x0, by
                rw [show (fun z => poin X la (fun _ => (0 : ℂ)) (cpt X x0 z)) =
                    (0 : V (nd X) → ℂ) from
                  funext fun z => OntoI.poin_zero (r := r) (X := X) la _, OntoJ.TL_zero]⟩
              smul_mem' := by
                rintro a _ ⟨F, P, hD, rfl⟩
                refine ⟨_, _, OntoJ.Dt_smul (r := r) (X := X) (x0 := x0) a hD, ?_⟩
                rw [show (fun z => poin X la (fun y => a * P y) (cpt X x0 z)) =
                    a • (fun z => poin X la P (cpt X x0 z)) from
                  funext fun z => OntoI.poin_smul (r := r) (X := X) la a P _,
                  OntoJ.TL_smul a (hmemP F P hD)] }, fun v => Iff.rfl⟩

  obtain ⟨D2, hD2i⟩ : ∃ D2 : Submodule ℂ (Frame X.Ψ r → ℂ), ∀ h, h ∈ D2 ↔
      h ∈ Submodule.span ℂ (Set.range g) ∧
        MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
    ⟨{ carrier := {h | h ∈ Submodule.span ℂ (Set.range g) ∧
          MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF)}
       add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, ha.2.add hb.2⟩
       zero_mem' := ⟨Submodule.zero_mem _, hzero⟩
       smul_mem' := fun c {h} hh => ⟨Submodule.smul_mem _ c hh.1, hh.2.const_smul c⟩ },
      fun h => Iff.rfl⟩
  have hD2m : ∀ h : D2, MemLp (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := fun h => ((hD2i h).1 h.2).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : D2 →ₗ[ℂ] Lp ℂ 2 (OntoI.nuF X x0 W FF), ∀ h : D2,
      Φ h = OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z)) :=
    ⟨{ toFun := fun h => OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => (h : Frame X.Ψ r → ℂ) (cpt X x0 z))
       map_add' := fun a b => by
         first
           | exact OntoJ.TL_add (hD2m a) (hD2m b)
           | (rw [← OntoJ.TL_add (hD2m a) (hD2m b)]; rfl)
       map_smul' := fun c a => by
         first
           | exact OntoJ.TL_smul c (hD2m a)
           | (rw [RingHom.id_apply, ← OntoJ.TL_smul c (hD2m a)]; rfl) }, fun h => rfl⟩
  have hMle : M ≤ LinearMap.range Φ := by
    intro v hv
    obtain ⟨F, P, hD, rfl⟩ := (hMmem v).1 hv
    obtain ⟨c, hc⟩ := hg _ (hSS _ (hPo F P hD).2.1) ((hPo F P hD).2.2.1 FF hFF)
    obtain ⟨h, hhD, hhx⟩ : ∃ h : Frame X.Ψ r → ℂ, h ∈ Submodule.span ℂ (Set.range g) ∧
        ∀ x, h x = ∑ i, c i * g i x :=
      ⟨∑ i, c i • g i, Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)),
        fun x => by simp [Finset.sum_apply]⟩
    have hae2 : (fun z => h (cpt X x0 z)) =ᵐ[OntoI.nuF X x0 W FF]
        fun z => poin X la P (cpt X x0 z) := by
      filter_upwards [hae] with z hz
      rw [hhx, hc _ (hFF.2.1 hz)]
    have hmh : MemLp (fun z => h (cpt X x0 z)) 2 (OntoI.nuF X x0 W FF) :=
      (hmemP F P hD).ae_eq hae2.symm
    refine LinearMap.mem_range.2 ⟨⟨h, (hD2i h).2 ⟨hhD, hmh⟩⟩, ?_⟩
    rw [hΦ]
    exact OntoJ.TL_congr hmh hae2
  haveI hfS : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) := by
    first
      | exact FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
      | exact FiniteDimensional.span_of_finite (Set.finite_range g)
      | exact Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range g))
      | exact inferInstance
  have hD2le : D2 ≤ Submodule.span ℂ (Set.range g) := by
    intro h hh
    exact ((hD2i h).1 hh).1
  haveI hfD2 : FiniteDimensional ℂ D2 := by
    first
      | exact Submodule.finiteDimensional_of_le hD2le
      | exact Module.Finite.of_injective (Submodule.inclusion hD2le)
          (Submodule.inclusion_injective hD2le)
  haveI hfR : FiniteDimensional ℂ (LinearMap.range Φ) := by
    first
      | exact LinearMap.finiteDimensional_range Φ
      | exact inferInstance
  haveI hfM : FiniteDimensional ℂ M := by
    first
      | exact Submodule.finiteDimensional_of_le hMle
      | exact Module.Finite.of_injective (Submodule.inclusion hMle)
          (Submodule.inclusion_injective hMle)
  haveI : CompleteSpace M := by
    first
      | exact FiniteDimensional.complete ℂ M
      | exact inferInstance

  obtain ⟨y, hyM, w, hw, hvyw⟩ : ∃ y ∈ M, ∃ w ∈ M.orthogonal,
      OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => f (cpt X x0 z)) = y + w := by
    first
      | exact Submodule.exists_add_mem_mem_orthogonal M _
      | exact Submodule.exists_add_mem_mem_orthogonal _
  obtain ⟨F, P, hD, rfl⟩ := (hMmem y).1 hyM
  have hmemf0 : MemLp (fun z => f (cpt X x0 z) - poin X la P (cpt X x0 z)) 2
      (OntoI.nuF X x0 W FF) := hmemf.sub (hmemP F P hD)
  have hwTL : w = OntoJ.TL (OntoI.nuF X x0 W FF)
      (fun z => f (cpt X x0 z) - poin X la P (cpt X x0 z)) := by
    have e1 := OntoJ.TL_sub hmemf (hmemP F P hD)
    have e2 : w = OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => f (cpt X x0 z)) -
        OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P (cpt X x0 z)) := by
      rw [hvyw]; abel
    rw [e2, ← e1]
    rfl
  have horth : ∀ (F' : V (nd X) → ℂ) (P' : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F' (OmF X x0) →
      InAt X x0 W bb F' → IsBEq X la P' → (∀ z ∈ OmF X x0, P' (cpt X x0 z) = F' z) →
      ∫ z in FF, poin X la P' (cpt X x0 z) *
          (starRingEnd ℂ) (f (cpt X x0 z) - poin X la P (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 = 0 := by
    intro F' P' h1 h2 h3 h4
    have hD' : OntoJ.Dt X x0 W bb la F' P' := ⟨h1, h2, h3, h4⟩
    have hmem' : OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P' (cpt X x0 z)) ∈ M :=
      (hMmem _).2 ⟨F', P', hD', rfl⟩
    have h0 : ⟪OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P' (cpt X x0 z)), w⟫_ℂ = 0 := by
      first
        | exact Submodule.inner_right_of_mem_orthogonal hmem' hw
        | exact (Submodule.mem_orthogonal M w).1 hw _ hmem'
    have h0' : ⟪w, OntoJ.TL (OntoI.nuF X x0 W FF) (fun z => poin X la P' (cpt X x0 z))⟫_ℂ = 0 := by
      first
        | exact inner_eq_zero_symm.1 h0
        | exact Submodule.inner_left_of_mem_orthogonal hmem' hw
    rw [hwTL, OntoJ.TL_eq hmemf0, OntoJ.TL_eq (hmemP F' P' hD'),
      OntoI.inner_toLp (r := r) (X := X) (x0 := x0) (W := W) (FF := FF) hWm hmemf0
        (hmemP F' P' hD')] at h0'
    refine (integral_congr_ae ?_).trans h0'
    filter_upwards with z
    ring
  have hf0SS : (fun y => f y - poin X la P y) ∈ X.SS la :=
    hSS _ (OntoI.bdd_sub (r := r) (X := X) hf.1 (hPo F P hD).2.1)
  have hff0 : InFF X x0 W FF (fun y => f y - poin X la P y) := by
    have hcf : ContinuousOn (fun z => f (cpt X x0 z)) (OmF X x0) :=
      hf.1.1.1.continuousOn.comp
        ((OntoB.cd_cpt (r := r) (X := X) (x0 := x0)).continuous.continuousOn)
        (by intro z hz; exact hz)
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ))) (muF X x0) :=
      OntoH.aem_of (r := r) (X := X) (x0 := x0)
        (ENNReal.continuous_ofReal.comp_continuousOn ((hcf.norm.pow 2).div_const 1))
    have haem : AEMeasurable
        (fun z => ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2 / (1 : ℝ)) * W (cpt X x0 z))
        ((muF X x0).restrict FF) :=
      (h1.mul (OntoH.measW (r := r) (X := X) (x0 := x0) hWm).aemeasurable).restrict
    have key := OntoI.lint_add_le (μ := (muF X x0).restrict FF) (a := fun z => f (cpt X x0 z))
      (b := fun z => -poin X la P (cpt X x0 z)) (k := fun _ => (1 : ℝ))
      (om := fun z => W (cpt X x0 z)) (fun _ => one_pos) haem
    simp only [div_one, norm_neg, ← sub_eq_add_neg] at key
    have hPF := (hPo F P hD).2.2.1 FF hFF
    show ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z) - poin X la P (cpt X x0 z)‖ ^ 2) *
      W (cpt X x0 z) ∂muF X x0 < ⊤
    refine lt_of_le_of_lt key (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
    · first
        | exact ENNReal.mul_lt_top (by simp) hfF
        | exact ENNReal.mul_lt_top (by simp) hfF.ne
    · first
        | exact ENNReal.mul_lt_top (by simp) hPF
        | exact ENNReal.mul_lt_top (by simp) hPF.ne
  have hvan := OntoH.vanish (r := r) (X := X) (x0 := x0) hExG hGrad hKa hPair hBig hConn hExtF
    hx0 hPD hW hWL hbb4 hm hg1 hg1ne hPs hWPs hLev hFF hf0SS hff0 horth
  obtain ⟨hD1, hD2, hD3, hD4⟩ := hD
  refine ⟨F, P, hD1, hD2, hD3, hD4, fun x hx => ?_⟩
  have hx0' := hvan x hx
  exact (sub_eq_zero.1 hx0').symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
