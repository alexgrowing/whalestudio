import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DiscChar

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {ω χ : HChar E}
  {V : Submodule ℂ (Sm E a)}

structure IsDiscreteWith (ω : HChar E) (V : Submodule ℂ (Sm E a)) : Prop where
  aut : ∀ φ ∈ V, IsAutForm φ
  central : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ
  sqInt : ∀ φ ∈ V, IsSqInt fun g => ((‖φ.1 g‖ : ℝ) : ℂ)
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

variable (a) in

def detLine (χ : HChar E) : Submodule ℂ (Sm E a) := Submodule.span ℂ {mulChi a χ (oneFn E a)}

theorem mem_detLine {φ : Sm E a} :
    φ ∈ detLine a χ ↔ ∃ c : ℂ, ∀ g, φ.1 g = c * (χ.1 (GeneralLinearGroup.det g) : ℂˣ) :=
  Submodule.mem_span_singleton.trans <| exists_congr fun c =>
    ⟨fun e g => e ▸ congrArg (c * ·) (one_mul _),
      fun e => Subtype.ext (funext fun g => ((e g).trans (congrArg (c * ·) (one_mul _).symm)).symm)⟩

theorem map_detLine (χ χ' : HChar E) : (detLine a χ).map (mulChi a χ').toLinearMap = detLine a (χ * χ') := by
  rw [detLine, Submodule.map_span, Set.image_singleton, detLine, mulChi_mul]
  rfl

theorem chiDet_scalar (χ : HChar E) (z : Neutral.B1.Ideles E) :
    chiDet a χ (GeneralLinearGroup.scalar (Fin a) z) = (χ ^ a).1 z := by
  have : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin a) z) = z ^ a := Units.ext (by
    change (Matrix.scalar (Fin a) (z : Ad E)).det = _
    simp)
  exact (congrArg χ.1 this).trans ((map_pow _ _ _).trans (MonoidHom.pow_apply χ.1 a z).symm)

abbrev expId (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (t : ℝ) : Neutral.B1.Ideles E :=
  infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem isUnitary_of_expId (h : ∀ t, ω.1 (expId E t) = 1) : ω.IsUnitary := by
  refine (CG.isUnitary_ofChar_iff ω).1 ((CG.isUnitary_mk _).2 (Model.isUnitary_of_isNormalised ?_))
  rintro _ ⟨φ, hφ, rfl⟩ t g
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  change _ * (chiDet 1 ω _ : ℂ) = _ * (chiDet 1 ω _ : ℂ)
  rw [map_mul, splitCentre_eq_scalar, chiDet_scalar, pow_one, h, one_mul]
  rfl

theorem IsDiscreteWith.apply (h : IsDiscreteWith ω V) {φ : Sm E a} (hφ : φ ∈ V) (z : Neutral.B1.Ideles E) (g : GA E a) :
    φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g := by
  rw [CuspRep.scalar_comm]
  exact congrFun (congrArg Subtype.val (h.central z φ hφ)) g

theorem IsDiscreteWith.unique {ω' : HChar E} (h : IsDiscreteWith ω V) (h' : IsDiscreteWith ω' V) : ω = ω' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 h.ne_bot
  exact Subtype.ext (MonoidHom.ext fun z =>
    Units.ext (smul_left_injective ℂ h0 ((h.central z φ hφ).symm.trans (h'.central z φ hφ))))

theorem enorm_ofReal_norm (z : ℂ) : ‖((‖z‖ : ℝ) : ℂ)‖ₑ = ‖z‖ₑ := by simp [enorm]

theorem IsDiscreteWith.isDiscrete (h : IsDiscreteWith ω V) (hω : ∀ t, ω.1 (expId E t) = 1) : IsDiscrete V :=
  ⟨h.aut, fun φ hφ => ⟨fun t g => by rw [splitCentre_eq_scalar, h.apply hφ, hω, Units.val_one, one_mul], by
    simpa only [enorm_ofReal_norm] using (h.sqInt φ hφ).2⟩, h.stable, h.ne_bot, h.irred⟩

theorem isDiscreteWith_of_isDiscrete (h : IsDiscrete V) (hc : ∀ z : Neutral.B1.Ideles E, ∀ φ ∈ V,
    rt E a (GeneralLinearGroup.scalar (Fin a) z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ) : IsDiscreteWith ω V :=
  ⟨h.aut, hc, fun φ hφ => ⟨fun t g => by simp only [(h.sqInt φ hφ).1 t g], by
    simpa only [enorm_ofReal_norm] using (h.sqInt φ hφ).2⟩, h.stable, h.ne_bot, h.irred⟩

theorem isSqInt_of_bounded {f : GA E a → ℂ} (h : ∀ t g, f (splitCentre E a t * g) = f g) {C : ℝ}
    (hC : ∀ g, ‖f g‖ ≤ C) : IsSqInt f := by
  have hd := isFundamentalDomain_stdDom (latticeGL E a) (Measure.haar : Measure (GA E a))
  have hf := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a Measure.haar
  refine ⟨h, Measure.haar, _, inferInstance, hd, ?_⟩
  refine (lintegral_mono (g := fun _ => ENNReal.ofReal C ^ 2) fun g => ?_).trans_lt ?_
  · exact pow_le_pow_left' ((ofReal_norm_eq_enorm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC g))) 2
  · rw [setLIntegral_const, ← quotMeasure_univ hd]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (measure_lt_top _ _)

theorem IsDiscreteWith.twist (h : IsDiscreteWith ω V) {ν : HChar E} (hν : ν.IsUnitary) :
    IsDiscreteWith (ω * ν ^ a) (V.map (mulChi a ν).toLinearMap) where
  aut := by rintro _ ⟨φ, hφ, rfl⟩; exact (h.aut φ hφ).mulChi ν
  central := by
    rintro z _ ⟨φ, hφ, rfl⟩
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * _) * (chiDet a ν (g * _) : ℂ) = ((ω.1 z * (ν ^ a).1 z : ℂˣ) : ℂ) * (φ.1 g * (chiDet a ν g : ℂ))
    rw [← CuspRep.scalar_comm, h.apply hφ, map_mul, chiDet_scalar, Units.val_mul, Units.val_mul]
    ring
  sqInt := by
    rintro _ ⟨φ, hφ, rfl⟩
    convert h.sqInt φ hφ using 3 with g
    change ‖φ.1 g * (ν.1 _ : ℂ)‖ = _
    rw [norm_mul, hν, mul_one]
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (V.smul_mem _ (h.stable o φ hφ)) (V.smul_mem _ hφ), (act_mulChi ν o φ).symm⟩
  ne_bot e := h.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a ν)).1 e)
  irred W hW hs := by
    have h := h.irred (W.comap (mulChi a ν).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a ν).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a ν).toLinearMap := (act_mulChi ν o φ) ▸ hs o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul ν o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a ν).toLinearMap) (mulChi a ν).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem isDiscreteWith_detLine (hχ : χ.IsUnitary) : IsDiscreteWith (χ ^ a) (detLine a χ) := by
  have h1 : IsDiscreteWith 1 (Submodule.span ℂ {oneFn E a}) :=
    isDiscreteWith_of_isDiscrete ⟨fun _ => isAutForm_const, fun φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact isSqInt_of_bounded (f := fun _ => c * 1) (fun _ _ => rfl) fun _ => le_rfl,
      isStable_const, fun e => oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 e),
      fun W hW _ => (nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW⟩ fun z φ hφ => by
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        exact (one_smul ℂ _).symm
  have h2 := h1.twist hχ
  rwa [one_mul, Submodule.map_span, Set.image_singleton] at h2

theorem isDiscreteWith_cusp (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hω : ω.IsUnitary)
    (h : π.HasCentral ω) : IsDiscreteWith ω π.V :=
  have hu : π.IsUnitary := ⟨ω, hω, h⟩
  ⟨fun φ hφ => (π.cusp φ hφ).1, h, fun φ hφ => by
    obtain ⟨C, hC⟩ := hB.of_isUnitary hu hφ
    exact isSqInt_of_bounded (fun t g => by rw [splitCentre_eq_scalar, hu.norm_eq hφ]) (C := C)
      fun g => by simpa using hC g, π.stable, π.ne_bot, π.irred⟩

theorem detLine_ne_cusp (ha : 1 < a) (χ : HChar E) (π : CuspSub E a) : detLine a χ ≠ π.V := fun e => by
  have h := (π.cusp _ (e.le (Submodule.mem_span_singleton_self _))).mulChi χ⁻¹
  rw [← mulChi_mul, mul_inv_cancel, mulChi_one] at h
  exact GlobalTheory.ConstNotCusp.not_isCuspidal_oneFn E a ha h.2

section Local

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSpeh_detRep_two {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    IsSpeh (IrrGL.ofChar η hη) 2 (detRep (Fin 2) η) := by
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_prodIrr (θ := fun i : Fin 2 => η * absPow k ((((2 : ℕ) : ℂ) - 1) / 2 - (i : ℕ)))
    (fun _ => hη.mul (isSmoothChar_absPow _)) (x := spehFactor (IrrGL.ofChar η hη) 2)
    (fun _ => IrrGL.tw_ofChar _ _ hη (isSmoothChar_absPow _)) (Θ := (detLevi pts η⁻¹)⁻¹) fun g => by
      rw [MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two,
        show (((2 : ℕ) : ℂ) - 1) / 2 - ((0 : Fin 2) : ℕ) = 1 / 2 by norm_num,
        show (((2 : ℕ) : ℂ) - 1) / 2 - ((1 : Fin 2) : ℕ) = -(1 / 2) by norm_num, absPow_neg]
      simp [mul_comm]
  exact ⟨hd, (isCosocle_detRep_two hη).of_equiv (.refl _) ψ⟩

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem eq_of_hasSpehComp {χ' : HChar E} (h : HasSpehComp (detLine 2 χ) ((CuspSub.triv E le_rfl).twist χ') 2) :
    χ = χ' := by
  have key : ∀ w, χ.loc w = χ'.loc w := fun w => by
    let σ' := (SmIrr.triv _).twist (CuspSub.locDet 2 χ w) (CuspSub.isOpen_ker_locDet χ w)
    have h1 : IsLocCompGL (detLine 2 χ) w σ' := by
      refine ⟨LinearMap.toSpanSingleton ℂ _ (mulChi 2 χ (oneFn E 2)), fun e => ?_,
        fun v => Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), fun g v => Subtype.ext (funext fun x => ?_)⟩
      · exact oneFn_ne_zero ((mulChi 2 χ).map_eq_zero_iff.1 ((one_smul ℂ _).symm.trans (LinearMap.congr_fun e (1 : ℂ))))
      · change ((CuspSub.locDet 2 χ w g : ℂ) * (show ℂ from v)) * (1 * (chiDet 2 χ x : ℂ)) =
          (show ℂ from v) * (1 * (chiDet 2 χ (x * _) : ℂ))
        rw [map_mul, CuspSub.chiDet_locGL, Units.val_mul]
        ring
    have h2 := h.loc w _ _ (CG.isLoc_ofChar χ' w) h1
    have hs : GlobalTheory.SmGL.IsSmoothChar (χ'.loc w) := by
      have hc : Continuous (CG.oneByOne : (w.adicCompletion E)ˣ → GL (Fin 1) (w.adicCompletion E)) :=
        Continuous.units_map _ (continuous_pi fun _ => continuous_id).matrix_diagonal
      have h := (CuspSub.isOpen_ker_locDet (a := 1) χ' w).preimage hc
      simp only [Set.preimage_ofPred_eq, CuspSub.locDet, MonoidHom.comp_apply, CG.det_oneByOne] at h
      exact h
    obtain ⟨_, h3⟩ := h2
    obtain ⟨_, h4⟩ := isSpeh_detRep_two hs
    obtain ⟨e⟩ : Nonempty ((GlobalTheory.SmGL.detRep (Fin 2) (χ.loc w)).Equiv (GlobalTheory.SmGL.detRep (Fin 2) (χ'.loc w))) :=
      h4.unique h3
    ext x
    let g : GL (Fin 2) (w.adicCompletion E) := GeneralLinearGroup.mkOfDetNeZero !![x.1, 0; 0, 1] (by simp)
    have hg : GeneralLinearGroup.det g = x := Units.ext (by simp [g])
    have h5 : e (((χ.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • (1 : ℂ)) =
        ((χ'.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • e (1 : ℂ) :=
      LinearMap.congr_fun (e.isIntertwining' g) (1 : ℂ)
    rw [map_smul, hg] at h5
    exact smul_left_injective ℂ ((map_ne_zero_iff e e.injective).2 (one_ne_zero (α := ℂ))) h5
  have : χ * χ'⁻¹ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    rw [HChar.val_mul, HChar.val_inv, mul_inv_eq_one]
    exact congrArg (fun f => f (atFin v (unif v))) (key v)
  exact mul_inv_eq_one.1 this

end GlobalTheory.DiscChar

namespace GlobalTheory.Published

open GlobalTheory.DiscChar

def DiscreteSpectrumGLTwo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (ω : HChar E), ω.IsUnitary →
    ∀ V : Submodule ℂ (Sm E 2), IsDiscreteWith ω V ↔
      (∃ π : CuspSub E 2, π.HasCentral ω ∧ V = π.V) ∨ ∃ χ : HChar E, χ ^ 2 = ω ∧ V = detLine 2 χ

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem DiscreteSpectrumGL.cusp_or_detLine (H : DiscreteSpectrumGL) (hB : CuspFormsBoundedGL) {V : Submodule ℂ (Sm E 2)}
    (hV : IsDiscrete V) : (∃ π : CuspSub E 2, V = π.V) ∨ ∃ χ : HChar E, V = detLine 2 χ := by
  obtain ⟨h1, h2, -, -, h5⟩ := H E 2 one_le_two
  have key : ∀ V : Submodule ℂ (Sm E 2), IsDiscrete V → (∃ π : CuspSub E 2, V = π.V) ∨
      ∃ χ : HChar E, IsNormalised ((CuspSub.triv E le_rfl).twist χ) ∧ IsSpehOf V ((CuspSub.triv E le_rfl).twist χ) 2 := by
    intro V hV
    obtain ⟨a, d, π, hu, hn, hs⟩ := h1 V hV
    have hm := hs.mul_eq
    have hd : d ≤ 2 := Nat.le_of_dvd two_pos ⟨a, hm.symm⟩
    rcases (by interval_cases d <;> omega : d = 2 ∧ a = 1 ∨ d = 1 ∧ a = 2) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
      exact .inr ⟨χ, hn, hs⟩
    · obtain ⟨ω, hω, hc⟩ := hu
      have h3 := isDiscreteWith_cusp hB hω hc
      exact .inl ⟨π, (h2 2 1 π rfl hn).unique ⟨hV, hs⟩ ⟨⟨h3.aut, fun φ hφ => ⟨hn φ hφ, by
        simpa only [enorm_ofReal_norm] using (h3.sqInt φ hφ).2⟩, h3.stable, h3.ne_bot, h3.irred⟩, isSpehOf_one π⟩⟩
  refine (key V hV).imp_right fun ⟨χ, hn, hs⟩ => ⟨χ, ?_⟩
  have h0 : ∀ t, χ.1 (expId E t) = 1 := fun t => by
    have h := hn _ ⟨_, Submodule.mem_span_singleton_self _, rfl⟩ t 1
    change 1 * (chiDet 1 χ _ : ℂ) = 1 * (chiDet 1 χ _ : ℂ) at h
    rw [mul_one, splitCentre_eq_scalar, chiDet_scalar, pow_one, map_one, one_mul, one_mul] at h
    exact Units.ext h
  have hL : IsDiscrete (detLine 2 χ) := (isDiscreteWith_detLine (isUnitary_of_expId h0)).isDiscrete fun t =>
    (MonoidHom.pow_apply χ.1 2 _).trans (by rw [h0, one_pow])
  obtain ⟨π, e⟩ | ⟨χ', hn', hs'⟩ := key _ hL
  · exact absurd e (detLine_ne_cusp one_lt_two χ π)
  · obtain rfl := eq_of_hasSpehComp (h5 _ hL 1 2 _ hn' hs')
    exact (h2 1 2 _ rfl hn).unique ⟨hV, hs⟩ ⟨hL, hs'⟩

theorem discreteSpectrumGLTwo_of (H : DiscreteSpectrumGL) (hB : CuspFormsBoundedGL) : DiscreteSpectrumGLTwo := by
  intro E _ _ _ ω hω V
  refine ⟨fun hV => ?_, ?_⟩
  · obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E 2 two_pos (dchi ω 1)
    have h0 : ∀ t, (ω * ν ^ 2).1 (expId E t) = 1 := fun t => Units.ext <| by
      have h1 := hν t
      rw [splitCentre_eq_scalar, chiDet_scalar] at h1
      have h2 : ((ω.1 (expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
        refine (chiInf_expU ω _).trans (congrArg _ ?_)
        rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
        simp
      change ((ω.1 _ * (ν ^ 2).1 _ : ℂˣ) : ℂ) = 1
      rw [Units.val_mul, h1, h2, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hu : ν.IsUnitary := isUnitary_of_pow two_ne_zero (by
      simpa only [inv_mul_cancel_left] using hω.inv.mul (isUnitary_of_expId h0))
    have back : (V.map (mulChi 2 ν).toLinearMap).map (mulChi 2 ν⁻¹).toLinearMap = V := by
      rw [← Submodule.map_comp]
      refine (congrArg (fun f => V.map f) (LinearMap.ext fun φ => ?_)).trans (Submodule.map_id V)
      exact (mulChi_mul ν ν⁻¹ φ).symm.trans (by rw [mul_inv_cancel, mulChi_one]; rfl)
    obtain ⟨π, e⟩ | ⟨χ, e⟩ := H.cusp_or_detLine hB ((hV.twist hu).isDiscrete h0)
    · have e' : V = (π.twist ν⁻¹).V := back.symm.trans (by rw [e]; rfl)
      exact .inl ⟨_, fun z φ hφ => hV.central z φ (e'.ge hφ), e'⟩
    · have e' : V = detLine 2 (χ * ν⁻¹) := back.symm.trans (by rw [e, map_detLine])
      refine .inr ⟨_, Subtype.ext (MonoidHom.ext fun z => Units.ext ?_), e'⟩
      have h1 := hV.apply (e'.ge (Submodule.mem_span_singleton_self _)) z 1
      change 1 * (chiDet 2 _ _ : ℂ) = _ * (1 * (chiDet 2 _ _ : ℂ)) at h1
      simpa only [mul_one, one_mul, map_one, Units.val_one, chiDet_scalar] using h1
  · rintro (⟨π, hc, rfl⟩ | ⟨χ, rfl, rfl⟩)
    · exact isDiscreteWith_cusp hB hω hc
    · exact isDiscreteWith_detLine (isUnitary_of_pow two_ne_zero hω)

theorem discreteSpectrumGLTwo_of_cuspidalSpectrum (H : DiscreteSpectrumGL) (hC : CuspidalSpectrumGL) :
    DiscreteSpectrumGLTwo := discreteSpectrumGLTwo_of H hC.2.2

theorem DiscreteSpectrumGLTwo.exists_char (H : DiscreteSpectrumGLTwo) {ω : HChar E} (hω : ω.IsUnitary)
    {V : Submodule ℂ (Sm E 2)} (hV : IsDiscreteWith ω V) {φ : Sm E 2} (hφ : φ ∈ V) (hc : ¬ IsCuspidal φ.1) :
    ∃ χ : HChar E, χ ^ 2 = ω ∧ χ.IsUnitary ∧ ∀ ψ ∈ V, ∃ c : ℂ, ∀ g, ψ.1 g = c * (χ.1 (GeneralLinearGroup.det g) : ℂˣ) := by
  obtain ⟨π, -, rfl⟩ | ⟨χ, rfl, rfl⟩ := (H E ω hω V).1 hV
  · exact absurd (π.cusp φ hφ).2 hc
  · exact ⟨χ, rfl, isUnitary_of_pow two_ne_zero hω, fun _ => mem_detLine.1⟩

theorem DiscreteSpectrumGLTwo.sSup_eq (H : DiscreteSpectrumGLTwo) {ω : HChar E} (hω : ω.IsUnitary) :
    sSup {V : Submodule ℂ (Sm E 2) | IsDiscreteWith ω V} =
      (⨆ (π : CuspSub E 2) (_ : π.HasCentral ω), π.V) ⊔ ⨆ (χ : HChar E) (_ : χ ^ 2 = ω), detLine 2 χ := by
  refine le_antisymm (sSup_le fun V hV => ?_) (sup_le (iSup₂_le fun π h => le_sSup ((H E ω hω _).2 (.inl ⟨π, h, rfl⟩)))
    (iSup₂_le fun χ h => le_sSup ((H E ω hω _).2 (.inr ⟨χ, h, rfl⟩))))
  obtain ⟨π, h, rfl⟩ | ⟨χ, h, rfl⟩ := (H E ω hω V).1 hV
  · exact le_sup_of_le_left (le_iSup₂_of_le π h le_rfl)
  · exact le_sup_of_le_right (le_iSup₂_of_le χ h le_rfl)

example : IsDiscreteWith (1 ^ 2) (detLine 2 (1 : HChar E)) ∧ ∀ π : CuspSub E 2, detLine 2 (1 : HChar E) ≠ π.V :=
  ⟨isDiscreteWith_detLine isUnitary_one, detLine_ne_cusp one_lt_two 1⟩

end GlobalTheory.Published

end
