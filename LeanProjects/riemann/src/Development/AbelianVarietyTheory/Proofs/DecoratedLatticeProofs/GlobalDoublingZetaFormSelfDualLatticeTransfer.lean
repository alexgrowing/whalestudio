import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepPreservesFockDegreeOfCommuteCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteAStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem rmul_one' {V : HSp D} (q : AutomorphicL2Unitary.Quot (GQ V)) : AutomorphicL2Unitary.rmul (GQ V) 1 q = q := by
  induction q using Quotient.inductionOn' with
  | h x => exact congrArg _ (mul_one x)

def rmulEquiv {V : HSp D} (y : GA D V) : AutomorphicL2Unitary.Quot (GQ V) ≃ᵐ AutomorphicL2Unitary.Quot (GQ V) where
  toFun := AutomorphicL2Unitary.rmul (GQ V) y
  invFun := AutomorphicL2Unitary.rmul (GQ V) y⁻¹
  left_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, mul_inv_cancel, rmul_one']
  right_inv q := by rw [← AutomorphicL2Unitary.rmul_mul, inv_mul_cancel, rmul_one']
  measurable_toFun := AutomorphicL2Unitary.measurable_rmul y
  measurable_invFun := AutomorphicL2Unitary.measurable_rmul y⁻¹

theorem descend_mul_right {V : HSp D} {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) = AutomorphicL2Unitary.descend (GQ V) φ ∘ AutomorphicL2Unitary.rmul (GQ V) y := by
  funext q
  have e : AutomorphicL2Unitary.rmul (GQ V) y q = AutomorphicL2Unitary.mk (GQ V) (q.out * y) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  simp only [Function.comp, e, hφ.descend_mk]
  rfl

section Quot

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_descend_mul_right {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q ∂autMeasure V m =
      ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q ∂autMeasure V m := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding _

theorem integrable_descend_mul_right_iff {φ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (y : GA D V) :
    Integrable (AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y))) (autMeasure V m) ↔
      Integrable (AutomorphicL2Unitary.descend (GQ V) φ) (autMeasure V m) := by
  rw [descend_mul_right hφ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integrable_comp_emb (rmulEquiv y).measurableEmbedding

theorem petersson_rTr {φ ψ : GA D V → ℂ} (hφ : AutomorphicL2Unitary.LeftInv (GQ V) φ) (hψ : AutomorphicL2Unitary.LeftInv (GQ V) ψ) (y : GA D V) :
    petersson V m (rTr V y φ) (rTr V y ψ) = petersson V m φ ψ := by
  show ∫ q, AutomorphicL2Unitary.descend (GQ V) (fun x => φ (x * y)) q * conj (AutomorphicL2Unitary.descend (GQ V) (fun x => ψ (x * y)) q)
      ∂autMeasure V m = ∫ q, AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q) ∂autMeasure V m
  rw [descend_mul_right hφ y, descend_mul_right hψ y]
  exact (AutomorphicL2Unitary.measurePreserving_rmul (Γ := GQ V) (μ := m) y).integral_comp (rmulEquiv y).measurableEmbedding
    (fun q => AutomorphicL2Unitary.descend (GQ V) φ q * conj (AutomorphicL2Unitary.descend (GQ V) ψ q))

end Quot

section Conj

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem integral_conj (F : GA D V → ℂ) (k : GA D V) : ∫ y, F (k * y * k⁻¹) ∂m = ∫ y, F y ∂m := by
  rw [integral_mul_left_eq_self (fun z => F (z * k⁻¹)) k, integral_mul_right_eq_self F k⁻¹]

theorem integrable_of_conj {F : GA D V → ℂ} (k : GA D V) (h : Integrable (fun y => F (k * y * k⁻¹)) m) :
    Integrable F m := by
  have h2 := (h.comp_mul_left k⁻¹).comp_mul_right k
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Conj

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

section Weil

variable {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χA χB : (AE D)ˣ →* Circle} {om : WRep A B}

theorem om_mul_one (g g' : GA D A) (f : WO A B → ℂ) : om (g, 1) (om (g', 1) f) = om (g * g', 1) f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem thetaKO_om (g k : GA D A) (h : GA D B) (Φ : WO A B → ℂ) :
    thetaKO om g h (om (k, 1) Φ) = thetaKO om (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem leftInv_thetaKO (hW : IsWeilDatumO ψ A B χA χB om) {Φ : WO A B → ℂ} (hΦ : IsThetaFunO ψ A B Φ) (h : GA D B) :
    AutomorphicL2Unitary.LeftInv (GQ A) fun g => thetaKO om g h Φ := by
  intro γ hγ g
  show om (γ * g, h) Φ 0 = om (g, h) Φ 0
  have e : ((γ * g, h) : GA D A × GA D B) = (γ, 1) * (g, h) := by rw [Prod.mk_mul_mk, one_mul]
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (GQ B).one_mem _ (hW.om_pres _ _ hΦ)

theorem wcoef_om (hW : IsWeilDatumO ψ A B χA χB om) {ν : Measure (WO A B)} {𝓕 : Set (WO A B)}
    (hν : IsCovolOne (ratL B A) ν 𝓕) {Φ₁ Φ₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B Φ₁) (h₂ : IsThetaFunO ψ A B Φ₂)
    (k y : GA D A) :
    wcoef om ν 𝓕 (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) y = wcoef om ν 𝓕 Φ₁ Φ₂ (k * y * k⁻¹) := by
  have e : om (y, 1) (om (k⁻¹, 1) Φ₁) = om (k⁻¹, 1) (om (k * y * k⁻¹, 1) Φ₁) := by
    rw [om_mul_one, om_mul_one]; congr 2; group
  have key := GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hW.std A B ν 𝓕 hν.1 hν.2.1 (om (k⁻¹, 1))
    (fun f hf => hW.om_pres (k⁻¹, 1) f hf) (fun f hf => hW.om_unit ν 𝓕 hν.1 hν.2.1 (k⁻¹, 1) f hf)
    (om (k * y * k⁻¹, 1) Φ₁) Φ₂ (hW.om_pres _ _ h₁) h₂
  simp only [wcoef, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, e]
  exact key

end Weil

section Cusp

variable {V : HSp D} (m : Measure (GA D V)) [m.IsHaarMeasure] [m.IsMulRightInvariant]

theorem rcoef_rTr {u₁ u₂ : GA D V → ℂ} (h₁ : AutomorphicL2Unitary.LeftInv (GQ V) u₁) (h₂ : AutomorphicL2Unitary.LeftInv (GQ V) u₂) (k y : GA D V) :
    rcoef m (rTr V k⁻¹ u₁) (rTr V k⁻¹ u₂) y = rcoef m u₁ u₂ (k * y * k⁻¹) := by
  unfold rcoef
  have h₃ : AutomorphicL2Unitary.LeftInv (GQ V) (rTr V (k * y * k⁻¹) u₁) := h₁.mul_right _
  rw [← petersson_rTr m h₃ h₂ k⁻¹]
  congr 1
  funext x
  simp only [rTr]
  congr 1
  group

end Cusp

end GlobalTheory.Core.Rk.GlobMove

namespace GlobalTheory.Core.Rk.GlobMove

variable {D : D7}

theorem cuspFormsArchimedeanKFinite_left_invariant {θ : InfFam D} {A : HSp D} {cA : CptF A} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    AutomorphicL2Unitary.LeftInv (GQ A) u :=
  AutomorphicL2Unitary.leftInv_of_isAutFun (Submodule.mem_inf.1 hu).1.1.toIsAutFun

theorem globalFormAt_move : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    GlobalFormAt A L → GlobalFormAt A L' := by
  intro D A L L' hL hL' hG
  obtain ⟨k, hk, hh⟩ := GlobalTheory.T.doubledLatticeHeight_selfDual_lattices_eq_conj D A L L' hL hL'
  intro ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hΦ₁ hΦ₂ u₁ hu₁ u₂ hu₂
  haveI := hm
  haveI := hmH
  haveI : m.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds A m hm
  have hW := hP.weil
  have hθ : IsInfFam θ := hP.setting.2.2.2.1
  have hki : k⁻¹ ∈ GfC A := inv_mem hk
  have fock : ∀ Φ, IsFockVec ψ θ A B sA sB Φ → IsFockVec ψ θ A B sA sB (om (k⁻¹, 1) Φ) := by
    rintro Φ ⟨hΦ, N, hN⟩
    refine ⟨hW.om_pres _ _ hΦ, N, fun l hl => ?_⟩
    refine GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ θ A B χA χB om sA sB hW hθ k⁻¹ (fun τ => ?_) N Φ hΦ hN l hl
    rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ A hki τ, Matrix.one_mul, Matrix.mul_one]
  have lu₁ := cuspFormsArchimedeanKFinite_left_invariant hu₁
  have lu₂ := cuspFormsArchimedeanKFinite_left_invariant hu₂

  have upEq : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      (∀ h, AutomorphicL2Unitary.descend (GQ A) (fun g => thetaKO om g h (om (k⁻¹, 1) Φ) * rTr A k⁻¹ u g) =
        AutomorphicL2Unitary.descend (GQ A) (fun g => (fun x => thetaKO om x h Φ * u x) (g * k⁻¹))) ∧
      ∀ h, AutomorphicL2Unitary.LeftInv (GQ A) (fun x => thetaKO om x h Φ * u x) := by
    intro Φ hΦ u hu
    refine ⟨fun h => ?_, fun h γ hγ g => ?_⟩
    · congr 1
      funext g
      rw [thetaKO_om]
      rfl
    · simp only [leftInv_thetaKO hW hΦ h γ hγ g, hu γ hγ g]
  have upConvIff : ∀ Φ, IsThetaFunO ψ A B Φ → ∀ u : GA D A → ℂ, AutomorphicL2Unitary.LeftInv (GQ A) u →
      up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u ∧
      (UpConv om m mH (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) → UpConv om m mH Φ u) := by
    intro Φ hΦ u hu
    obtain ⟨e1, e2⟩ := upEq Φ hΦ u hu
    have hup : up om m (om (k⁻¹, 1) Φ) (rTr A k⁻¹ u) = up om m Φ u := by
      funext h
      simp only [up]
      rw [e1 h, integral_descend_mul_right m (e2 h) k⁻¹]
    refine ⟨hup, fun ⟨c1, c2⟩ => ⟨fun h => ?_, hup ▸ c2⟩⟩
    have := c1 h
    rw [e1 h, integrable_descend_mul_right_iff m (e2 h) k⁻¹] at this
    exact this

  have hint : ∀ s y, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s y =
      integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) := by
    intro s y
    simp only [integrand]
    rw [wcoef_om hW hP.covol hΦ₁.1 hΦ₂.1, rcoef_rTr m lu₁ lu₂, hh a hP.maj]
    congr 3
    group
  obtain ⟨c1, c2, c3, z, hz, hpet⟩ := hG ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH
    (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (fock Φ₁ hΦ₁) (fock Φ₂ hΦ₂)
    (rTr A k⁻¹ u₁) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₁ hu₁)
    (rTr A k⁻¹ u₂) (GlobalTheory.T.rTr_mem_A0 D θ A cA hθ k⁻¹ hki u₂ hu₂)
  obtain ⟨up₁, cv₁⟩ := upConvIff Φ₁ hΦ₁.1 u₁ lu₁
  obtain ⟨up₂, cv₂⟩ := upConvIff Φ₂ hΦ₂.1 u₂ lu₂
  refine ⟨cv₁ c1, cv₂ c2, fun s hs => integrable_of_conj m k ?_, z, ?_, ?_⟩
  · have := c3 s hs
    rwa [show integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s =
      fun y => integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s (k * y * k⁻¹) from funext (hint s)] at this
  · have e : (fun s => ∫ g, integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s g ∂m) =
        fun s => ∫ g, integrand om m ν 𝓕 L a (om (k⁻¹, 1) Φ₁) (om (k⁻¹, 1) Φ₂) (rTr A k⁻¹ u₁) (rTr A k⁻¹ u₂) s g ∂m := by
      funext s
      simp only [hint]
      rw [integral_conj m (integrand om m ν 𝓕 L' a Φ₁ Φ₂ u₁ u₂ s) k]
    rw [e]
    exact hz
  · rw [← up₁, ← up₂]
    exact hpet

end GlobalTheory.Core.Rk.GlobMove
