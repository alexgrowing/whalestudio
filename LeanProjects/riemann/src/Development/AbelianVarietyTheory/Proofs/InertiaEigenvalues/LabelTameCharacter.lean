import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RestrictMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType ValuativeRel Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameCharLabel

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {p : ℕ} [Fact p.Prime]

theorem red_natCast_val (hp : resCard F = p) (a : ZMod p) : red hp ((a.val : ℕ) : 𝒪[F]) = a := by
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem valuation_natCast_val (hp : resCard F = p) (a : (ZMod p)ˣ) :
    valuation F ((((a : ZMod p).val : ℕ) : F)) = 1 := by
  have hu : IsUnit (((a : ZMod p).val : ℕ) : 𝒪[F]) :=
    isUnit_of_red_ne_zero hp (by rw [red_natCast_val]; exact a.ne_zero)
  have := (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.1 hu
  rwa [map_natCast] at this

theorem tame_eq {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) {x y : Fˣ} (hy : valuation F (y : F) = 1)
    (hxy : valuation F ((x : F) - y) < 1) : χ x = χ y := by
  have h1 : valuation F (((x / y : Fˣ) : F) - 1) < 1 := by
    have : ((x / y : Fˣ) : F) - 1 = ((x : F) - y) / y := by
      rw [Units.val_div_eq_div_val, sub_div, div_self y.ne_zero]
    rw [this, map_div₀, hy, div_one]
    exact hxy
  have := hχ _ h1
  rwa [_root_.map_div, div_eq_one] at this

def unitOf (hp : resCard F = p) (a : (ZMod p)ˣ) : Fˣ :=
  Units.mk0 (((a : ZMod p).val : ℕ) : F) fun h => by
    have := valuation_natCast_val hp a
    rw [h, map_zero] at this
    exact zero_ne_one this

theorem eq_unitOf {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) (hp : resCard F = p) (a : (ZMod p)ˣ) (x : Fˣ)
    (hx : valuation F ((x : F) - ((a : ZMod p).val : F)) < 1) : χ x = χ (unitOf hp a) :=
  tame_eq hχ (valuation_natCast_val hp a) hx

theorem exists_charLift (hp : resCard F = p) {χ : Fˣ →* ℂˣ} (hχ : IsTame χ) : ∃ θ : (ZMod p)ˣ →* ℂˣ, CharLift θ χ := by
  refine ⟨{ toFun := fun a => χ (unitOf hp a), map_one' := ?_, map_mul' := fun a b => ?_ }, fun a x hx => ?_⟩
  · have h := eq_unitOf hχ hp 1 1 (by
      have := (red_eq_iff_val hp 1 ((1 : (ZMod p)ˣ) : ZMod p)).1 (by simp)
      simpa using this)
    rw [map_one] at h
    exact h.symm
  · have h := eq_unitOf hχ hp (a * b) (unitOf hp a * unitOf hp b) (by
      have := (red_eq_iff_val hp (((a : ZMod p).val : ℕ) * ((b : ZMod p).val : ℕ) : 𝒪[F]) ((a * b : (ZMod p)ˣ) : ZMod p)).1
        (by rw [map_mul, red_natCast_val, red_natCast_val, Units.val_mul])
      rw [MulMemClass.coe_mul, SubringClass.coe_natCast, SubringClass.coe_natCast] at this
      rw [Units.val_mul]
      exact this)
    rw [map_mul] at h
    exact h.symm
  · exact eq_unitOf hχ hp a x hx

end Local

end GlobalTheory.TameCharLabel

namespace GlobalTheory.TameCharLabel

open NumberField IsDedekindDomain GlobalTheory.SerSys.TameGen GlobalTheory.Published.DepthZeroModel

theorem inflates_det {E : Type} [Field E] [NumberField E] {g : ℕ} [Fact g.Prime] {w : HeightOneSpectrum (𝓞 E)}
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) {θ : (ZMod g)ˣ →* ℂˣ} {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hθ : CharLift θ χ) :
    Inflates ((IrrRep.det (Fin 1) χ hχ).ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (tauOne θ) := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  refine ⟨LinearMap.id, fun e => (one_ne_zero : (1 : ℂ) ≠ 0) (LinearMap.congr_fun e (1 : ℂ)), fun k (v : ℂ) => ?_⟩
  set c := Matrix.GeneralLinearGroup.det k
  have e2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k)) =
      Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c) := by
    ext; simp [c, GlobalTheory.GLp.inc, RingHom.map_det]
  have e3 : Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k) =
      Units.map (PadicInt.toZMod (p := g)).toMonoidHom c := by
    ext; simp [c, GlobalTheory.GLp.red, RingHom.map_det]
  set r : ℕ := (PadicInt.toZMod (c : ℤ_[g])).val
  have hk : ‖(((c : ℤ_[g]) - r : ℤ_[g]) : ℚ_[g])‖ < 1 := by
    have : (c : ℤ_[g]) - r ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at this
    exact this
  have h6 := he.lt_one_iff_lt_one.2 (GlobalTheory.Published.DepthZeroTypeModel.v_lt_one i hi hk)
  have h7 : χ (Units.map i.toRingHom.toMonoidHom (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom c)) =
      θ (Units.map (PadicInt.toZMod (p := g)).toMonoidHom c) := by
    refine hθ _ _ ?_
    convert h6 using 2
    simp [r]
  change ((θ (Matrix.GeneralLinearGroup.det (GlobalTheory.GLp.red g 1 k)) : ℂˣ) : ℂ) • v =
    ((χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g 1 k))) : ℂˣ) : ℂ) • v
  rw [e2, e3, h7]

theorem label_reduction : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : Formalism.BasicNotions.D7) (Γ : GlobalTheory.HeightCounting.GrpSide D) (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : ZMod (D.host.g k)), IsTame χ → labAt hL D k v (Irr.ofDet 1 χ hχ) = Polynomial.X - Polynomial.C u → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k ∧ ∀ L : GlobalTheory.GLq.LabelDatum (D.host.g k), L.teich = D.ntypes.teichC k → L.gen = Γ.ζ k → ∃ θ : (ZMod (D.host.g k))ˣ →* ℂˣ, CharLift θ χ ∧ GlobalTheory.GLp.IsCharLab L θ u := by
  intro H hL D Γ k v χ hχ u htame hlab
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hp : resCard ((D.naut.plGw k v).adicCompletion D.host.E) = D.host.g k := by
    haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨h1, -, -⟩ := GlobalTheory.Mem.Chr.splitsC_place (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)
    exact (GlobalTheory.LocLanglands.resCard_eq_normV _).trans h1
  refine ⟨hp, fun L hteich hgen => ?_⟩
  obtain ⟨θ, hθ⟩ := exists_charLift hp htame
  set x := GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    (GlobalTheory.LocLanglands.cls (IrrRep.det (Fin 1) χ hχ)) with hx
  have hlab' : GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) x = X - C u := hlab
  refine ⟨θ, hθ, fun hu0 => ?_, fun u' hu' => ?_⟩
  · have := GlobalTheory.WeilDeligne.WD.lab_coeff_zero_ne_zero (D.ntypes.teichC k) (D.ntypes.tg k v) x
    rw [hlab', hu0] at this
    simp at this
  · obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
    obtain ⟨P, hP, hPe⟩ := exists_label L θ u' hu'
    have hT : Formalism.L2.NT.TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (Γ.kv k v) (D.ntypes.tg k v) L.gen := by
      rw [hgen]; exact Γ.tg_tame k v
    have h1 := H D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
      (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL _) (I.i k v) (I.cont k v) (Γ.kv k v) L _ (D.ntypes.tg_mem k v) hT 1
      (IrrRep.det (Fin 1) χ hχ) (GlobalTheory.LocGL.IrrGL.isCusp_ofChar χ hχ) (tauOne θ) P hP
      (inflates_det (I.i k v) (I.cont k v) hχ hθ)
    rw [hPe] at h1
    obtain ⟨a, ha, ε, -, hl⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))
    have hdim : x.lpDim = 1 := hl.dim _
    have h2 := GlobalTheory.WeilDeligne.WD.inePol_eq_of_natDegree_lab (D.ntypes.teichC k) (D.ntypes.tg k v) x
      (by rw [hlab', hdim, natDegree_X_sub_C])
    have hr : Formalism.CyclotomicNorms.rootsBar (X - C u) = {algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) u} := by
      simp [Formalism.CyclotomicNorms.rootsBar]
    rw [hlab', hr, h1] at h2
    have h3 := congrArg (fun q => q.coeff 0) h2
    simp at h3
    rw [hteich]
    exact h3
end GlobalTheory.TameCharLabel

end
