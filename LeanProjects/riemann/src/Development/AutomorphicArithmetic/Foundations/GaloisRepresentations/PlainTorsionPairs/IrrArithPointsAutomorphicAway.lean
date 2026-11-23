import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormAbsPowUnif
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUnl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ClassicalityIrreducibleArith

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.W UpperTheory.V.Af UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open UpperTheory.V.HV (Coef)

namespace UpperTheory.Gal.projectedFormsSystemPart

section

variable {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def WitOff (u : Plc (Lp F)) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (∀ v : Plc F, ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → Unl1 r v → PotUnl r v) ∧
    ∀ π : CuspSub F n, (CG.mk π).IsRegAlg → AttC ι r π → ∃ t : ℝ, ∀ v : Plc F, v.under (𝓞 (Lp F)) ≠ u →
      (((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∨ PotUnl r v) → WinAt π t v

def AutOff (_u : Plc (Lp F)) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := IsAutCsd ι r

def AutOffN (u : Plc (Lp F)) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → WitOff u ι r)

def AutOffW (_u : Plc (Lp F)) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := IsAutCsdN ι r

variable {u u' : Plc (Lp F)} {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}

theorem WitOff.of (h : WitA ι r) : WitOff u ι r :=
  ⟨h.1, fun π h1 h2 => (h.2 π h1 h2).imp fun _ ht v _ hv => ht v hv⟩

theorem witA_of (hO : UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinOf) (hU : UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinUnl) (hn : 1 ≤ n) (hu : u ≠ u') (h : WitOff u ι r) (h' : WitOff u' ι r) :
    WitA ι r := by
  refine ⟨h.1, fun π h1 h2 => ?_⟩
  obtain ⟨t, ht⟩ := hO F n hn π
  obtain ⟨a, ha⟩ := h.2 π h1 h2
  obtain ⟨b, hb⟩ := h'.2 π h1 h2
  refine ⟨t, fun v hv => ?_⟩
  by_cases e : v.under (𝓞 (Lp F)) = u
  · have k := hb v (e ▸ hu) hv
    exact ht v k.1 (hU F n π b v k)
  · have k := ha v e hv
    exact ht v k.1 (hU F n π a v k)

theorem glueN (hn : 1 ≤ n) (hu : u ≠ u') (h : AutOffN u ι r) (h' : AutOffN u' ι r) :
    AutCsd0 ι r ∧ (Continuous r → WitA ι r) :=
  ⟨h.1, fun hc => witA_of UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf winUnl hn hu (h.2 hc) (h'.2 hc)⟩

end

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def IrrArithPointsAutomorphicAway : Prop :=
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    AutOffN s.v0 ι ρ

variable {B ι J}

theorem end2o (_ : r.V0ok) (H : B.arithmeticPointClassicality ι J) (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)) :
    J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ → AutOff s.v0 ι ρ := H x h ρ
theorem end2oN (_ : r.V0ok) (H : IrrArithPointsAutomorphicAway B ι J) (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)) :
    J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ → AutOffN s.v0 ι ρ := H x h ρ

omit [IsAlgClosure L Ω] in

theorem v0_ne {s s' : HidaSetting l L Ω} (h : ¬ s'.p ∣ s.p) : s.v0 ≠ s'.v0 := fun e =>
  h (by rw [← s.norm_v0_eq_one, ← s'.norm_v0_eq_one, e])

end UpperTheory.Gal.projectedFormsSystemPart
