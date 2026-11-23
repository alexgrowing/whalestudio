import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LitModel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem weilRel_refl_iff (σ σ' : Weil h) : WeilRel (RingEquiv.refl Ω) σ σ' ↔ σ = σ' :=
  ⟨fun H => Subtype.ext (AlgEquiv.ext H), by rintro rfl z; rfl⟩

theorem weilRel_conj_iff (τ σ σ' : Weil h) :
    WeilRel ((τ : G E Ω) : Ω ≃ₐ[E] Ω).toRingEquiv σ σ' ↔ σ' = τ * σ * τ⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, eq_comm]
  exact ⟨fun H => Subtype.ext (AlgEquiv.ext H), fun H z => DFunLike.congr_fun (congrArg Subtype.val H) z⟩

theorem wdRel_refl_iff (y y' : WD h) : WDRel (RingEquiv.refl Ω) y y' ↔ y = y' := by
  constructor
  · rintro ⟨n, b, b', rfl, rfl, hN, hρ⟩
    exact WD.sound ⟨.refl _ _, fun σ v => by rw [hρ σ σ fun _ => rfl]; rfl, fun v => by rw [hN]; rfl⟩
  · rintro rfl
    obtain ⟨n, b, rfl⟩ := y.exists_rep
    exact ⟨n, b, b, rfl, rfl, rfl, fun σ σ' H => by rw [(weilRel_refl_iff σ σ').1 H]⟩

theorem repRel_refl_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x x' : IrrGL k) : RepRel (RingEquiv.refl k) x x' ↔ x = x' := by
  have hm : ∀ {n : ℕ} (g : GL (Fin n) k), GeneralLinearGroup.map (RingEquiv.refl k).toRingHom g = g :=
    fun g => Units.ext (Matrix.ext fun _ _ => rfl)
  constructor
  · rintro ⟨n, π, π', e, rfl, rfl, H⟩
    refine congrArg (Sigma.mk n) (IrrRep.cl_eq_iff.2 ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun v => ?_⟩)
    have := H g v
    rw [hm] at this
    exact this
  · rintro rfl
    obtain ⟨n, c⟩ := x
    exact ⟨n, c.rep, c.rep, .refl _ _, congrArg (Sigma.mk n) c.cl_rep.symm, congrArg (Sigma.mk n) c.cl_rep.symm,
      fun g v => by rw [hm]; rfl⟩

theorem placeIso_weil (τ : Weil h) :
    PlaceIso A w A w ((τ : G E Ω) : Ω ≃ₐ[E] Ω).toRingEquiv (RingHom.id E) (RingEquiv.refl _) := by
  refine ⟨fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun x => (τ : G E Ω).commutes x, continuous_id, fun _ => rfl⟩
  · have := val_apply_le_one (Weil_le_Dec h τ⁻¹.2) ((A.valuation_le_one_iff _).2 hz)
    rw [A.valuation_le_one_iff] at this
    simpa using this
  · exact (A.valuation_le_one_iff _).1 (val_apply_le_one (Weil_le_Dec h τ.2) ((A.valuation_le_one_iff _).2 hz))

theorem exists_placeIso_ne (h : IsPlaceOver A w) : ∃ φ : Ω ≃+* Ω, φ ≠ RingEquiv.refl Ω ∧
    PlaceIso A w A w φ (RingHom.id E) (RingEquiv.refl _) := by
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  let τ : Weil h := ⟨φ, mem_Weil_of_isFrob h hφ⟩
  refine ⟨_, fun e => ?_, placeIso_weil τ⟩
  have h1 : deg τ = ((1 : ℕ) : ℤ) - (0 : ℕ) := deg_eq (actsAs_one_iff.2 hφ)
  have h2 : τ = 1 := Subtype.ext (AlgEquiv.ext fun z => DFunLike.congr_fun e z)
  rw [h2, deg_one] at h1
  omega

theorem wdRel_weil (τ : Weil h) (hτ : deg τ = 0) (y : WD h) :
    WDRel ((τ : G E Ω) : Ω ≃ₐ[E] Ω).toRingEquiv y y := by
  obtain ⟨n, b, rfl⟩ := y.exists_rep
  let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := LinearEquiv.ofLinear (b.ρ τ⁻¹) (b.ρ τ)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine ⟨n, b, b.transport e, rfl, WD.sound (b.iso_transport e).symm, ?_, fun σ σ' H => ?_⟩
  · have := b.conj_N τ⁻¹
    rw [deg_inv, hτ, neg_zero, zpow_zero, one_smul, inv_inv] at this
    exact this.symm
  · rw [(weilRel_conj_iff τ σ σ').1 H]
    show _ = b.ρ τ⁻¹ * b.ρ _ * b.ρ τ
    rw [← map_mul, ← map_mul]
    congr 1
    group

theorem fieldCompatible_iff {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h') :
    FieldCompatible rc rc' ↔ ∀ φ j i, PlaceIso A w A' w' φ j i → ∀ x x', RepRel i x x' →
      ∃ (b : WDRep h (Fin x.1 → ℂ)) (b' : WDRep h' (Fin x.1 → ℂ)), WD.mk b = rc x ∧ WD.mk b' = rc' x' ∧
        b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), WeilRel φ σ σ' → b.ρ σ = b'.ρ σ' := by
  constructor
  · rintro H φ j i P _ _ ⟨n, π, π', e, rfl, rfl, He⟩
    exact H φ j i P.mem P.ext P.cont P.loc n π π' e He
  · intro H φ j i a b c d n π π' e He
    exact H φ j i ⟨a, b, c, d⟩ _ _ ⟨n, π, π', e, rfl, rfl, He⟩

theorem fieldCompatible_iff_wdRel {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
    [IsAlgClosure E' Ω'] {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
    (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h')
    (hd : ∀ x, (rc x).lpDim = x.1) :
    FieldCompatible rc rc' ↔ ∀ φ j i, PlaceIso A w A' w' φ j i → ∀ x x', RepRel i x x' → WDRel φ (rc x) (rc' x') := by
  rw [fieldCompatible_iff]
  refine ⟨fun H φ j i P x x' R => ⟨_, H φ j i P x x' R⟩, fun H φ j i P x x' R => ?_⟩
  obtain ⟨n, b, b', h1, h2, h3⟩ := H φ j i P x x' R
  have : n = x.1 := by rw [← hd, ← h1]; simp
  subst this
  exact ⟨b, b', h1, h2, h3⟩

theorem exists_isRecLit (H : GlobalTheory.Published.LocalLanglandsGL) : ∃ rc, IsRecLit h rc :=
  let ⟨rc, hrc, _⟩ := H.1 E Ω A w h; ⟨rc, hrc.toLit⟩

theorem not_lawsMin_const {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} (y : WD h) : ¬ LawsMin a ha e fun _ => y := fun H => by
  have h0 := H.dim ⟨0, (IrrRep.det (Fin 0) 1 isSmoothChar_one).cl⟩
  have h1 := H.dim (.ofChar 1 isSmoothChar_one)
  rw [h0] at h1
  exact Nat.zero_ne_one h1

theorem segSum_nil (rc : IrrGL (w.adicCompletion E) → WD h) : segSum rc [] = WD.lpZero h := rfl

end GlobalTheory.LocLanglands.LitModel

end
