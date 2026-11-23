import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FirstTermWeak
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ConclusionZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsOrthogonalSumAndHyperbolicSumSpaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop

noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.OrthSumSp (posSp hypSp hypSumDec posSp_sigOK hypSp_sigOK)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.WeakModel

variable {D : D7}

def IsPairRes {S T' : HSp D} (ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)) (m : Measure (GA D T'))
    (Ψ : WO S T' → ℂ) (B : GA D S → ℂ) : Prop :=
  ∃ (E : GA D T' → ℂ → ℂ) (c : ℂ → ℂ) (s₀ : ℂ) (σ : ℝ), (∀ s : ℂ, σ < s.re → ∀ g, ThetaPairConv ω' m Ψ (fun h => E h s) g) ∧
    ∀ g, ResidueAt (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) s₀ (B g)

theorem residueAt_zero (s₀ : ℂ) : ResidueAt (fun _ : ℂ => (0 : ℂ)) s₀ 0 :=
  ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simp)⟩

theorem IsPairRes.eq_zero {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} {B : GA D S → ℂ} (h : IsPairRes ω' m Ψ B) {g : GA D S} (h0 : ∀ x, thetaKO ω' g x Ψ = 0) : B g = 0 := by
  obtain ⟨E, c, s₀, σ, -, hr⟩ := h
  have e : (fun s => c s * thetaPair ω' m Ψ (fun h => E h s) g) = fun _ => 0 := funext fun s => by
    have : (descend (GQ T') fun h => thetaKO ω' g h Ψ * E h s) = fun _ => 0 := funext fun q => by simp [AutomorphicL2Unitary.descend, h0]
    simp [thetaPair, this]
  have := hr g
  rw [e] at this
  exact CoeffAt.unique this (residueAt_zero s₀)

theorem IsPairRes.eq_of_kernel {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} {B : GA D S → ℂ} (h : IsPairRes ω' m Ψ B) {g g' : GA D S}
    (h0 : ∀ x, thetaKO ω' g x Ψ = thetaKO ω' g' x Ψ) : B g = B g' := by
  obtain ⟨E, c, s₀, σ, -, hr⟩ := h
  have h1 := hr g
  have h2 := hr g'
  unfold thetaPair at h1 h2
  simp only [h0] at h1
  exact CoeffAt.unique h1 h2

theorem isPairRes_thetaInt {S T' : HSp D} {ω' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} {m : Measure (GA D T')}
    {Ψ : WO S T' → ℂ} (h : ∀ g, ThetaPairConv ω' m Ψ 1 g) (κ : ℂ) : IsPairRes ω' m Ψ (κ • thetaInt ω' m Ψ) := by
  refine ⟨fun _ _ => 1, fun s => κ * s⁻¹, 0, 0, fun _ _ g => h g, fun g => ?_⟩
  have h3 : IsMerExt (fun s : ℂ => κ * s⁻¹ * thetaInt ω' m Ψ g) Set.univ fun s => κ * s⁻¹ * thetaInt ω' m Ψ g :=
    ⟨isRightDomain_univ, fun s _ => by fun_prop, 0, fun s _ => rfl⟩
  refine (h3.isExtAt trivial).coeffAt_of_tendsto (k := 1) (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => ?_))
  have : s ≠ 0 := hs
  simp only [Pi.smul_apply, smul_eq_mul, sub_zero, pow_one]
  field_simp

def Met (A T T' : HSp D) : Prop :=
  ∃ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D T →* Module.End ℂ (WO (dblSp A) T → ℂ))
    (ω' : GA D (dblSp A) × GA D T' →* Module.End ℂ (WO (dblSp A) T' → ℂ)) (a : GL (Fin A.rank) (AE D))
    (μ₀ : Measure (WO A T)) (𝓕₀ : Set (WO A T)) (m : Measure (GA D T')) (φ : WO (dblSp A) T → ℂ),
    IsWeilDatumO ψ (dblSp A) T 1 χ ω ∧ IsWeilDatumO ψ (dblSp A) T' 1 χ ω' ∧ m.IsHaarMeasure ∧ IsCovolOne (ratL T A) μ₀ 𝓕₀ ∧
    swSec A T ω μ₀ 𝓕₀ φ 1 = 1 ∧
    ∃ (Ψ : WO (dblSp A) T' → ℂ) (B : GA D (dblSp A) → ℂ), IsThetaFunO ψ (dblSp A) T' Ψ ∧ IsKFinVec ω' (Khat A a) Ψ ∧
      IsPairRes ω' m Ψ B ∧ EisCoeffAt A (flat A a (swSec A T ω μ₀ 𝓕₀ φ) (sZero A T)) (sZero A T) (-1) B

theorem met_of (h : FirstTermWeak) (A T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (hA : HSpace.SigOK A) (hT : HSpace.SigOK T)
    (hr : T.rank + T'.rank = 2 * A.rank) (hlt : T'.rank < T.rank) (h0 : 0 < T'.rank)
    (hc : IsAniso T' ∨ ∃ (T₀ : HSp D) (r' : ℕ) (_ : HypDec T' T₀ r'), IsAniso T₀ ∧ 0 < r') : Met A T T' := by
  obtain ⟨ψ, χ, ω, a, θ, sS, sT, ν, 𝓕, -, φ, hω, ha, hθ, hS, hsT, hK, hν, -, hφ, h1⟩ :=
    GlobalTheory.Core.Rk.IP.FockModel.hyp A T hA hT (by omega) (by omega)
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨ω', hω'⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hω.std (dblSp A) T' 1 χ ⟨η, hη⟩ hω.hecS hω.hecT hω.resS
    (resEta_parity hω.resT (by omega))
  obtain ⟨b, hb⟩ := exists_isMaj T
  obtain ⟨b', hb'⟩ := exists_isMaj T'
  have h2 := fun v => GlobalTheory.Core.Rk.IP.Model.isSplit_two (D := D) v
  obtain ⟨Ψ, B, p1, p2, p3, p4⟩ := h D ψ A T T' t d hr hlt h0 χ ω ω' hω hω' a b ha hb (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)
    (GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D T T' t d b h2 hb) ν 𝓕 hν Measure.haar inferInstance θ hθ sS sT hS hsT hK
    (hc.imp_right fun ⟨T₀, r', d₀, e1, e2⟩ => ⟨T₀, r', d₀, b', e1, e2, hb', GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D T' T₀ r' d₀ b' h2 hb'⟩)
    φ hφ (GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ _ T 1 χ ω sS sT hω hθ hS hsT _ (isCompact_Khat A a) hK φ hφ)
  exact ⟨ψ, χ, ω, ω', a, ν, 𝓕, Measure.haar, φ, hω, hω', inferInstance, hν, h1, Ψ, B, p1, p2, p3, p4⟩

theorem isAniso_pos (D : D7) (n : ℕ) : IsAniso (posSp D n) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (posSp_sigOK D n) fun _ => .inl rfl

theorem met_aniso (h : FirstTermWeak) (D : D7) : Met (posSp D 2) (hsum (posSp D 1) (hypSp D 1)) (posSp D 1) :=
  met_of h _ _ _ 1 (hypSumDec D _ 1) (posSp_sigOK D 2) (sigOK_hsum (posSp_sigOK D 1) (hypSp_sigOK D 1)) rfl
    (by show 1 < 1 + (1 + 1); omega) Nat.one_pos (.inl (isAniso_pos D 1))

theorem met_iso (h : FirstTermWeak) (D : D7) :
    Met (posSp D 4) (hsum (hsum (posSp D 1) (hypSp D 1)) (hypSp D 1)) (hsum (posSp D 1) (hypSp D 1)) :=
  met_of h _ _ _ 1 (hypSumDec D _ 1) (posSp_sigOK D 4)
    (sigOK_hsum (sigOK_hsum (posSp_sigOK D 1) (hypSp_sigOK D 1)) (hypSp_sigOK D 1)) rfl
    (by show 1 + (1 + 1) < 1 + (1 + 1) + (1 + 1); omega) (by show 0 < 1 + (1 + 1); omega)
    (.inr ⟨_, 1, hypSumDec D _ 1, isAniso_pos D 1, Nat.one_pos⟩)

end GlobalTheory.RegSW.WeakModel

end
