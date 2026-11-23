import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isLift_of_conj {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    (ν b : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin n) k) V) (σ' : Representation ℂ (GL (Fin n) k) V')
    (π : Representation ℂ (GL (Fin d) k) W)
    (β : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] W) (hβ : β ≠ 0)
    (he : ∀ (g : GL (Fin n) k) (h : GL (Fin d) k) (Φ Φ₁ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k)),
      Φ₁.1 = GlobalTheory.SplitFlip.omA ν b g h Φ.1 → ∀ x, β Φ₁ (σ g x) = π h (β Φ x))
    (C : V ≃ₗ⋆[ℂ] V') (hC : ∀ g x, C (σ g x) = σ' g (C x)) : IsLift ν b σ' π := by
  let β' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] V' →ₗ[ℂ] W :=
    { toFun := fun Φ => (β Φ).comp (C.symm : V' →ₛₗ[starRingEnd ℂ] V)
      map_add' := fun Φ Ψ => by ext x; simp
      map_smul' := fun a Φ => by ext x; simp }
  have hβ' : ∀ Φ x, β' Φ x = β Φ (C.symm x) := fun _ _ => rfl
  refine ⟨β', fun h0 => hβ ?_, fun g h Φ Φ₁ hΦ x => ?_⟩
  · ext Φ x
    have := hβ' Φ (C x)
    rw [h0] at this
    simpa using this.symm
  · rw [hβ', hβ']
    have : C.symm (σ' g x) = σ g (C.symm x) := by
      apply C.injective
      rw [hC]
      simp
    rw [this]
    exact he g h Φ Φ₁ hΦ _

private theorem seg_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (h : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal) (x : ℂˣ) (m : ℕ) : seg v x m = seg w x m := by
  unfold seg
  refine Multiset.map_congr rfl fun i _ => ?_
  congr 1
  apply Units.ext
  simp only [coe_npowU, npow, h]

theorem UpperTheory.Gal.TP.Loc.pairSat :
    UpperTheory.Gal.TP.Loc.LiftSat → UpperTheory.Gal.TP.Loc.PullGood → UpperTheory.Gal.TP.Loc.ContraIrr → UpperTheory.Gal.TP.Loc.ContraUnit → UpperTheory.Gal.TP.Loc.SatContra → UpperTheory.Gal.TP.Loc.PairSat := by
  intro hLift hPull hCI hCU hSC E _ _ _ n d hnd v t χX χW τ τ' hP hU hX hW B hB
  have hw := splitPrime_under t
  obtain ⟨ψ, h1, -, h3, -, -⟩ := SplitChart.exists_equiv_complMap t hw
  have hcs : Function.Surjective (complMap hw) := fun y => ⟨ψ.symm y, by rw [← h1]; simp⟩
  have hcc : Continuous (complMap hw) := SplitChart.continuous_complMap hw
  have hmap : ∀ (m : ℕ) (g : GL (Fin m) (Fv (maximalRealSubfield E) v)),
      Matrix.GeneralLinearGroup.map ψ.toRingHom g = Matrix.GeneralLinearGroup.map (complMap hw) g := fun m g =>
    Units.ext (Matrix.ext fun i j => h1 _)
  have hmap' : ∀ (m : ℕ) (g : GL (Fin m) ((splitPrime t).adicCompletion E)),
      Matrix.GeneralLinearGroup.map (complMap hw) (Matrix.GeneralLinearGroup.map ψ.symm.toRingHom g) = g := fun m g =>
    Units.ext (Matrix.ext fun i j => (h1 _).symm.trans (ψ.apply_symm_apply _))
  have hq : Formalism.UG.qV E (splitPrime t) = Formalism.UG.qV (maximalRealSubfield E) v := SplitChart.absNorm_splitPrime t
  have hv : ∀ x, Valued.v (ψ x) = Valued.v x := h3
  have hv' : ∀ x, Valued.v (ψ.symm x) = Valued.v x := fun x => by
    rw [← hv, ψ.apply_symm_apply]
  obtain ⟨s1, s2, s3⟩ := hPull _ _ (complMap hw) hcc hcs n τ.V τ.ρ
  obtain ⟨p1, p2, -⟩ := hPull _ _ (complMap hw) hcc hcs d τ'.V τ'.ρ
  have a1 := s1 τ.smooth
  have a2 := s2 τ.irred
  have a3 := s3 hU
  have b1 := p1 τ'.smooth
  have b2 := p2 τ'.irred
  set σ₀ : Representation ℂ (GL (Fin n) (Fv (maximalRealSubfield E) v)) τ.V :=
    τ.ρ.comp (Matrix.GeneralLinearGroup.map (complMap hw)) with hσ₀
  set π : Representation ℂ (GL (Fin d) (Fv (maximalRealSubfield E) v)) τ'.V :=
    τ'.ρ.comp (Matrix.GeneralLinearGroup.map (complMap hw)) with hπ
  have hB₀ : HasSatGL v σ₀ B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv ψ.symm hv' hq.symm (LinearEquiv.refl ℂ _) (fun g x => by
      change τ.ρ _ x = _
      rw [hmap']
      rfl) hB
  obtain ⟨c1, C, hC⟩ := hCU _ n τ.V σ₀ a1 a2 a3
  have c2 := (hCI _ n τ.V σ₀ a1 a2).1
  have hB₁ := hSC _ v n τ.V σ₀ a1 a2 a3 B hB₀
  have hL : IsLift (chrW χW t)⁻¹ (chrW χX t) (contra σ₀) π := by
    obtain ⟨β, hβ, he⟩ := hP
    exact isLift_of_conj _ _ σ₀ _ _ β hβ he C hC
  have uX := (PositivityTheory.ThK.SplitAsm.isUnram_chrW_iff χX t).2 hX
  have uW := (PositivityTheory.ThK.SplitAsm.isUnram_chrW_iff χW t).2 hW
  have uW' : GlobalTheory.SplitWeil.IsUnram (chrW χW t)⁻¹ := fun x hx => by
    rw [MonoidHom.inv_apply, uW x hx, inv_one]
  have nX : IsUnitaryChar (chrW χX t) := fun x => norm_locChar χX (splitPrime t) _
  have nW : IsUnitaryChar (chrW χW t)⁻¹ := fun x => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv]
    rw [show ‖((chrW χW t x : ℂˣ) : ℂ)‖ = 1 from norm_locChar χW (splitPrime t) _, inv_one]
  obtain ⟨ϖ₀, hϖ₀⟩ := exists_isUnifV v
  have hϖ0 : ϖ₀ ≠ 0 := fun e => by simp [Formalism.UG.IsUnifV, e] at hϖ₀
  let ϖ : (Fv (maximalRealSubfield E) v)ˣ := Units.mk0 ϖ₀ hϖ0
  have hunif : ∀ {χ : Chr (maximalRealSubfield E) E}, UnrAt χ (splitPrime t) → chrW χ t ϖ = val χ (splitPrime t) := by
    intro χ hχ
    refine hχ.locChar_eq_val ?_
    change Valued.v (complMap hw ϖ₀) = _
    rw [← h1, hv]
    exact hϖ₀
  have key := hLift _ v n d _ _ _ _ (contra σ₀) π hnd uW' nW uX nX (isSmooth_contra _) c2 c1 b1 b2 hL ϖ hϖ₀ _ hB₁
  have e1 : (B.map (·⁻¹)).map (fun x => x⁻¹ * ((chrW χW t)⁻¹ ϖ * chrW χX t ϖ)) =
      B.map (· * (val χX (splitPrime t) * (val χW (splitPrime t))⁻¹)) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp, inv_inv, MonoidHom.inv_apply, hunif hX, hunif hW, mul_comm]
  rw [e1, hunif hX, seg_eq v (splitPrime t) (SplitChart.absNorm_splitPrime t)] at key
  exact GlobalTheory.IsoPull.hasSatGL_of_ringEquiv ψ hv hq (LinearEquiv.refl ℂ _) (fun g x => by
    change τ'.ρ _ x = τ'.ρ _ x
    rw [hmap]) key
