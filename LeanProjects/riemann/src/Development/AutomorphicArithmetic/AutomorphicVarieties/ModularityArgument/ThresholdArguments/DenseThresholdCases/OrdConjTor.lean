import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
namespace UpperTheory.V.Z.Ord
section Loc
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
private theorem hasSupport_contra {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL k)} (h : HasSupport π s) :
    HasSupport (contra π) (s.map Zc.dualCl) := by
  have hsm := h.isSmooth
  obtain ⟨c, x, rfl, hi, hc, e, hsub⟩ := h
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hci : ∀ a, (contra (x a).rep).IsIrreducible := fun a =>
    GlobalTheory.CompanionTheory.ContraProd.contra_rep_isIrreducible hA (x a)
  have hcu : ∀ a, IsCuspidal (contra (x a).rep) := fun a => by
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA (x a) ⟨(hc a).1, (hc a).2.2⟩).1
    rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA] at this
    exact (IrrGL.isCusp_of.1 this).2
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.ContraProd.parInd_equiv_contra e
    (isSmooth_piTensor fun a => (x a).2.rep.smooth) (GlobalTheory.CompanionTheory.ContraProd.contra_piTensor_rep hA x)
  have H : IsCuspSupport (contra π) (fun a => (x a).1) (fun a => contra (x a).rep) := by
    refine ⟨GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k N) (hA k N V π hsm hi) hi,
      fun a => ⟨(hc a).1, hci a, hcu a⟩, e, ?_⟩
    exact (GlobalTheory.CompanionTheory.ContraSub.main k N _ _ _ _ hsm (isSmooth_parInd e _) hsub).trans
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective)
  have e2 : (Zc.dualCl ∘ x) = fun a => IrrGL.of (contra (x a).rep) (H.2.1 a).2.2.1 (H.2.1 a).2.1 :=
    funext fun a => GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA (x a)
  rw [Multiset.map_map, e2]
  exact hasSupport_of_isCuspSupport H
private theorem hasSupport_of_invT (c : k ≃+* k') (hc : Continuous c) {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) V) (τ : Representation ℂ (GL (Fin N) k') W)
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g v, τ (GlobalTheory.LFun.ConjPlace.invT c N g) (T v) = T (σ g v))
    {s : Multiset (IrrGL k)} (h : HasSupport σ s) :
    HasSupport τ ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL c (GlobalTheory.LocalFieldIso.continuous_symm c hc))) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm c hc
  obtain ⟨E⟩ := GlobalTheory.GelfandKazhdan.equiv_contra k N V σ (hA k N V σ h.isSmooth h.isIrreducible) h.isIrreducible
  have h1 := (hasSupport_contra h).of_equiv E.symm
  have h2 := GlobalTheory.SuppIne.hasSupport_comp c hc hc' h1
  refine h2.of_equiv (GlobalTheory.LocGL.equivOfBijective ⟨T.toLinearMap, fun g => LinearMap.ext fun v => ?_⟩ T.bijective)
  have hg : GlobalTheory.LFun.ConjPlace.invT c N (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k
      (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) = g :=
    Units.ext (Matrix.ext fun i j => by
      rw [GlobalTheory.LFun.ConjPlace.invT_val]
      exact c.apply_symm_apply _)
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change T (σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k (Matrix.GeneralLinearGroup.map (n := Fin N) c.symm.toRingHom g)) v) = τ g (T v)
  rw [← hT, hg]
private theorem dualCl_eq_of {x y : IrrGL k} (H : GlobalTheory.LocLanglands.DualCl x y) : Zc.dualCl x = y := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨n, π, π', rfl, rfl, ⟨E⟩⟩ := H
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA]
  change IrrGL.of _ _ _ = IrrGL.of π'.ρ π'.smooth π'.irr
  exact IrrGL.of_eq_of.2 ⟨(GlobalTheory.ContraRefl.contraEquiv (equivRep π)).trans E.symm⟩
private theorem val_lt_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) < 1 ↔ valuation k x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x⁻¹
  have p1 : 0 < valuation k x := by
    rw [zero_lt_iff]; simpa using hx
  have p2 : 0 < valuation k' (i x) := by
    rw [zero_lt_iff]; simpa using hx
  rw [map_inv₀, map_inv₀, map_inv₀, inv_le_one₀ p1, inv_le_one₀ p2] at h
  rw [← not_le, ← not_le, h]
private theorem val_eq_one_iff (i : k ≃+* k') (hi : Continuous i) (x : k) :
    valuation k' (i x) = 1 ↔ valuation k x = 1 := by
  have a := GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi x
  have b := val_lt_one_iff i hi x
  exact ⟨fun h => le_antisymm (a.1 h.le) (not_lt.1 fun l => (b.2 l).ne h),
    fun h => le_antisymm (a.2 h.le) (not_lt.1 fun l => (b.1 l).ne h)⟩
private theorem unram_unif (i : k ≃+* k') (hi : Continuous i) (μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    μ (Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k')) = μ (ImaginaryQuadraticEtaCharacter.unif k) := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  set a : kˣ := Units.map i.symm.toRingHom.toMonoidHom (ImaginaryQuadraticEtaCharacter.unif k') with ha
  have hav : (a : k) = i.symm (ImaginaryQuadraticEtaCharacter.unif k' : k') := rfl
  have S := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  have S' := (ImaginaryQuadraticEtaCharacter.polFacts k').1
  have ha1 : valuation k (a : k) < 1 := by
    rw [hav]; exact (val_lt_one_iff i.symm hi' _).2 S'.1
  have hb1 : valuation k' (i (ImaginaryQuadraticEtaCharacter.unif k : k)) < 1 := (val_lt_one_iff i hi _).2 S.1
  have le1 := S.2 _ ha1
  have le2 := S'.2 _ hb1
  have pa : 0 < valuation k (a : k) := by
    rw [zero_lt_iff]; simp
  have pb : 0 < valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := by
    rw [zero_lt_iff]; simp
  have pu : 0 < valuation k' (ImaginaryQuadraticEtaCharacter.unif k' : k') := by
    rw [zero_lt_iff]; simp
  have le3 : valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) ≤ valuation k (a : k) := by
    have h1 : valuation k' (i ((ImaginaryQuadraticEtaCharacter.unif k : k) * (a : k)⁻¹)) ≤ 1 := by
      have : i (a : k) = (ImaginaryQuadraticEtaCharacter.unif k' : k') := by rw [hav]; exact i.apply_symm_apply _
      rw [map_mul, map_inv₀, this, map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ le2 zero_le'
    have h2 := (GlobalTheory.LocalFieldIso.valuation_map_le_one_iff i hi _).1 h1
    rw [map_mul, map_inv₀] at h2
    simpa using (mul_inv_le_iff₀ pa).1 h2
  have he : valuation k (a : k) = valuation k (ImaginaryQuadraticEtaCharacter.unif k : k) := le_antisymm le1 le3
  have hu : μ (a * (ImaginaryQuadraticEtaCharacter.unif k)⁻¹) = 1 := hμ _ (by
    rw [Units.val_mul, map_mul, he, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ pb.ne'])
  rw [map_mul, map_inv, mul_inv_eq_one] at hu
  exact hu
private theorem isUnram_comp (i : k ≃+* k') (hi : Continuous i) {μ : kˣ →* ℂˣ} (hμ : IsUnram μ) :
    IsUnram (μ.comp (Units.map i.symm.toRingHom.toMonoidHom)) := fun x hx =>
  hμ _ ((val_eq_one_iff i.symm (GlobalTheory.LocalFieldIso.continuous_symm i hi) _).2 hx)
private theorem unl_of_map (i : k ≃+* k') (hi : Continuous i) (q : ℕ) (s : Multiset (IrrGL k))
    (h : ImaginaryQuadraticEtaCharacter.Unl q ((s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i (GlobalTheory.LocalFieldIso.continuous_symm i hi)))) :
    ImaginaryQuadraticEtaCharacter.Unl q s := by
  have hi' := GlobalTheory.LocalFieldIso.continuous_symm i hi
  intro ξ hξ ξ' hξ' hun
  obtain ⟨h1, m1⟩ := hξ
  obtain ⟨h2, m2⟩ := hξ'
  let U : k'ˣ →* kˣ := Units.map i.symm.toRingHom.toMonoidHom
  have sm : ∀ ζ : kˣ →* ℂˣ, IsSmoothChar ζ → IsSmoothChar ((ζ⁻¹).comp U) := fun ζ hζ =>
    IsOpen.preimage (Continuous.units_map _ hi') hζ.inv
  have mem : ∀ (ζ : kˣ →* ℂˣ) (hζ : IsSmoothChar ζ), IrrGL.ofChar ζ hζ ∈ s →
      IrrGL.ofChar ((ζ⁻¹).comp U) (sm ζ hζ) ∈ (s.map Zc.dualCl).map (GlobalTheory.SuppIne.trGL i hi') := fun ζ hζ hm =>
    Multiset.mem_map.2 ⟨IrrGL.ofChar ζ⁻¹ hζ.inv, Multiset.mem_map.2 ⟨_, hm,
      dualCl_eq_of (GlobalTheory.LocLanglands.CuspModel.dualCl_ofChar _ _ hζ hζ.inv rfl)⟩,
      GlobalTheory.DegOneChar.trGL_ofChar i hi' _ _ _⟩
  have e : ((ξ'⁻¹).comp U) * ((ξ⁻¹).comp U)⁻¹ = (ξ * ξ'⁻¹).comp U :=
    MonoidHom.ext fun x => by simp [mul_comm]
  have := h ((ξ'⁻¹).comp U) ⟨sm _ h2, mem _ _ m2⟩ ((ξ⁻¹).comp U) ⟨sm _ h1, mem _ _ m1⟩
    (by rw [e]; exact isUnram_comp i hi hun)
  rw [e, MonoidHom.comp_apply] at this
  rwa [unram_unif i hi _ hun] at this
end Loc
theorem conj_torsion_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → ConjTor := by
  intro _ E _ _ _ n hn π hd w w' hu hT
  by_cases e : w' = w
  · subst e
    exact hT
  obtain rfl : w' = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl ⟨hu, Or.inl e⟩
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hc : Continuous (GlobalTheory.ThetaSatake.cloc w) := (conjLoc_spec _ w).1
  have hc' := GlobalTheory.LocalFieldIso.continuous_symm _ hc
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E n π w
  have key : ∀ σ, π.IsLocComp (GlobalTheory.ThetaSatake.cw w) σ → ∃ T : σ.V ≃ₗ[ℂ] τ.V, ∀ g v,
      τ.ρ (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n g) (T v) = T (σ.ρ g v) := fun σ hσ =>
    GlobalTheory.CompanionTheory.OneExDatum.exists_equiv_of_dualIsConj hd w σ τ hσ (hA _ _ _ _ σ.smooth σ.irred) hτ
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨T, hTT⟩ := key σ hσ
    obtain ⟨s, hs, h1⟩ := hT.1 τ hτ
    have hs' : HasSupport τ.ρ s := hs.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred).symm
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w).symm hc' τ.ρ σ.ρ T.symm (fun g v => by
      obtain ⟨u, rfl⟩ := T.surjective v
      have := hTT (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) u
      have e : GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w).symm n g) = g :=
        (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n).apply_symm_apply g
      rw [e] at this
      rw [this, T.symm_apply_apply, T.symm_apply_apply]) hs'
    refine ⟨_, h2.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), ?_⟩
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨y'', hy'', rfl⟩ := Multiset.mem_map.1 hy'
    have := (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA y'' (hs'.isCusp hy'')).2
    exact this.trans (h1 _ hy'')
  · rintro s ⟨σ, hσ, hs⟩
    obtain ⟨T, hTT⟩ := key σ hσ
    have h2 := hasSupport_of_invT (GlobalTheory.ThetaSatake.cloc w) hc σ.ρ τ.ρ T hTT hs
    have h3 := hT.2 _ ⟨τ, hτ, h2⟩
    rw [GlobalTheory.ThetaSatake.absNorm_cw]
    exact unl_of_map (GlobalTheory.ThetaSatake.cloc w) hc _ _ h3
end UpperTheory.V.Z.Ord
end
