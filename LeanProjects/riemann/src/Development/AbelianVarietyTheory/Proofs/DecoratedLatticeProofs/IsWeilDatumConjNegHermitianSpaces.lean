import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7}

theorem cj_id_cj_id {X : Type} (f : X → ℂ) : cj id (cj id f) = f := cj_cj id id (fun _ => rfl) f

theorem cj_id_apply {X : Type} (f : X → ℂ) (x : X) : cj id f x = starRingEnd ℂ (f x) := rfl

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨(h.1.inv : Continuous fun x => (χ x)⁻¹), fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem enorm_conj (z : ℂ) : ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := by
  simp [enorm]

theorem mt_negGA_symm (V : HSp D) (g : GA D (negSp V)) : mt V ((negGA V).symm g) = mt (negSp V) g := by
  rw [← mt_negGA, MulEquiv.apply_symm_apply]

theorem continuous_negGA_symm (V : HSp D) : Continuous (negGA V).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem UJ_neg {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (J : Matrix n n A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem negGA_symm_mem_GQ (V : HSp D) (γ : GA D (negSp V)) (h : γ ∈ GQ (negSp V)) : (negGA V).symm γ ∈ GQ V := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _).symm

theorem splitFacO_inv (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    ((splitFacO χS⁻¹ χT⁻¹ x y : Circle) : ℂ) = starRingEnd ℂ (splitFacO χS χT x y) := by
  rw [← Circle.coe_inv_eq_conj]
  congr 1
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, _root_.mul_inv_rev]
  exact mul_comm _ _

theorem conjTarget_apply {S T : HSp D} (om : Om S T) (p : GA D S × GA D (negSp T)) (f : WO S T → ℂ) :
    conjTarget om p f = cj id (om (p.1, (negGA T).symm p.2) (cj id f)) := rfl

theorem conjSource_apply {S T : HSp D} (om : Om S T) (p : GA D (negSp S) × GA D T) (f : WO S T → ℂ) :
    conjSource om p f = cj id (om ((negGA S).symm p.1, p.2) (cj id f)) := rfl

theorem actO_negT (S T : HSp D) (g : GA D S) (h : GA D (negSp T)) (w : WO S T) :
    actO S (negSp T) g h w = actO S T g ((negGA T).symm h) w := by
  unfold actO; rw [mt_negGA_symm]

theorem actO_negS (S T : HSp D) (g : GA D (negSp S)) (h : GA D T) (w : WO S T) :
    actO (negSp S) T g h w = actO S T ((negGA S).symm g) h w := by
  unfold actO; rw [← map_inv (negGA S).symm g, mt_negGA_symm]

theorem weil_conjTarget (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thT : ∀ f : WO S (negSp T) → ℂ, IsThetaFunO ψ S (negSp T) f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).1
    rwa [cj_id_cj_id] at this
  have hzT : ∀ (w : WO S T) (f : WO S (negSp T) → ℂ),
      heisO ψ S (negSp T) w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).1
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjTarget_apply, thT, cj_id_cj_id]
    exact hw.om_pres _ _ ((thT f).1 hf)
  · intro g h w₀ f hf
    rw [conjTarget_apply, conjTarget_apply, hzT w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thT f).1 hf),
      hzT _ (cj id _), cj_id_cj_id, actO_negT]
  · intro γ hγ γ' hγ' f hf
    rw [conjTarget_apply]
    show starRingEnd ℂ (om (γ, (negGA T).symm γ') (cj id f) 0) = f 0
    rw [hw.om_aut γ hγ _ (negGA_symm_mem_GQ T γ' hγ') _ ((thT f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thT f).1 hf) w
    simp only [conjTarget_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (continuous_fst.prodMk ((continuous_negGA_symm T).comp continuous_snd)))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (p.1, (negGA T).symm p.2) (cj id f) ((thT f).1 hf)
    simp only [conjTarget_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g ((negGA T).symm h) hg
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hh) x y hx (by unfold IsDetAt; rw [mt_negGA_symm]; exact hy)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add, map_add]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (g, (negGA T).symm h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').1, hℓ u hu (cj id f') ((I.1 f').1.2 hf')]) (cj id f) ((thT f).1 hf)
    rw [cj_id_cj_id, ← conjTarget_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem weil_conjSource (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO (negSp S) T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO (negSp S) T → ℂ),
      heisO ψ (negSp S) T w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).2
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjSource_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [conjSource_apply, conjSource_apply, hzS w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thS f).1 hf),
      hzS _ (cj id _), cj_id_cj_id, actO_negS]
  · intro γ hγ γ' hγ' f hf
    rw [conjSource_apply]
    show starRingEnd ℂ (om ((negGA S).symm γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_symm_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [conjSource_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA_symm S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF ((negGA S).symm p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [conjSource_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he ((negGA S).symm g) h
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA_symm]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add, map_add]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om ((negGA S).symm g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').2, hℓ u hu (cj id f') ((I.1 f').2.2 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← conjSource_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem conj_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om →
      IsWeilDatumO ψ S (GlobalTheory.ChiGrid.negSp T) χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om) ∧
      IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) :=
  fun D ψ S T χS χT om hw => ⟨weil_conjTarget D ψ S T χS χT om hw, weil_conjSource D ψ S T χS χT om hw⟩

end GlobalTheory.ConjWeil
