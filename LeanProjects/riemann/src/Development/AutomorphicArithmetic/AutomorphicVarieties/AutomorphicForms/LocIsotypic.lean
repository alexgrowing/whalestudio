import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HasCohomology

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

def IsLevelWD {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w} (M n : ℕ) (x : WD h) : Prop :=
  ∃ (χ : Fin n → G F Ω →* ℂˣ) (a : WDRep h (Fin n → ℂ)), (∀ i, KillsMu M (χ i)) ∧ WD.mk a = x ∧ a.N = 0 ∧
    ∀ s : ↥(Ine (F := F) A), a.ρ (ineIncl h s) = Matrix.toLin' (Matrix.diagonal fun i => (χ i s : ℂ))

variable (F) in

def KLoc (w : HeightOneSpectrum (𝓞 F)) (n M : ℕ) : Subgroup (GL (Fin n) (w.adicCompletion F)) :=
  (KLev F n M).comap (locGL F n w)

def LocIsotypic {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V)
    (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) : Prop :=
  Nontrivial V ∧ ⨆ f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F n w g) (f v)}, LinearMap.range f.1 = ⊤

def FlagAt {l : ℕ} [Fact l.Prime] {n : ℕ} (M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ) : Prop :=
  ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ, (∀ i, KillsMu M (χ i)) ∧ IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i (s : ↥(Dec (F := F) A)), (s : G F Ω) ∈ Ine (F := F) A → κ i s = cycBar F Ω l s ^ m i * χ i s

end Defs

def WDAway : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (χ : Fin n → G F Ω →* (Qbar l)ˣ), (∀ i, KillsMu M (χ i)) → IsDiagOn r (Ine (F := F) A) χ →
      ∀ x : WD h, IsWDOf ι r x → IsLevelWD M n x

def WDAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ((∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨ PotCrysAt r A) →
      IsLevelWD M n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype))

def JumpsAbove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O), Induces Bw → ∀ (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → ∀ (τ : F →+* Qbar l) (J : Multiset ℤ),
      IsJumpsAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) τ J → J = Finset.univ.val.map fun i => -m i

def LocFixed : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      IsLevelWD M n (rc (algNorm σ)) → HasFixed σ.ρ (KLoc F w n M)

def GlobFixed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n M : ℕ), 1 ≤ M → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V), GlobalTheory.PRep.IsSmooth ρ →
    (∀ w, ∃ σ, LocIsotypic ρ w σ ∧ HasFixed σ.ρ (KLoc F w n M)) → HasFixed ρ (KLev F n M)

def LocCompC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (π : CuspSub E n) (w : HeightOneSpectrum (𝓞 E)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def LocCompR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (π : TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)),
    (∃ σ, π.IsLocComp w σ) ∧ ∀ σ, π.IsLocComp w σ → LocIsotypic π.finPart w σ

def SatLoc : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F))),
    (HasFixed σ.ρ (GlobalTheory.LFun.KGL w n) → ∃ B, GlobalTheory.LFun.HasSatGL w σ.ρ B) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V), LocIsotypic ρ w σ →
      ∀ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B ↔ GlobalTheory.LFun.HasSatGL w σ.ρ B

def SatFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion F) → WD h), IsRec h rc →
        IsWDOf ι r (rc (algNorm σ))) → FrobEig ι r w (algSat n (normV w) B)

def CrysSlopes : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime],
    ¬ (p : ℤ) ∣ discr F → ∀ (ι : Qbar p ≃+* ℂ) (n : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar p)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[p] O] [TopologicalSpace O]
      (Bw : LocBridge p F Ω (Dec (F := F) A) O) (hj : Induces Bw),
      IsCrysAt (Loc.PP p) Bw (r.comp (Dec (F := F) A).subtype) →
      (∀ (τ : F →+* Qbar p) (LL' : FinExt p) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[p]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt (Loc.PP p) Bw (r.comp (Dec (F := F) A).subtype) τ (Finset.univ.val.map fun i => -m i)) →
      ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
      ∀ rc, IsRec h rc → wdAt (Loc.PP p) ι Bw h hj (r.comp (Dec (F := F) A).subtype) = rc (algNorm σ) →
      ∀ b ∈ algSat n (normV w) B, (∀ a : ℤ, (∀ i, -a ≤ m i) → ‖ι.symm ((normV w : ℂ) ^ a * b⁻¹)‖ ≤ 1) ∧
        ∀ a : ℤ, (∀ i, m i ≤ a) → ‖ι.symm ((normV w : ℂ) ^ a * b)‖ ≤ 1

def WeylC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), ∃ c A : ℕ, ∀ m : Fin n → ℤ, StrictAnti m →
    ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∃ Ξ : GlobalTheory.GKCoh.AlgRep E n, (∀ τ, AlgInfChar Ξ τ ((infOf m).map Neg.neg)) ∧ Ξ.d ≤ c * (H + 1) ^ A

def WeylQ : Prop :=
  ∀ (n : ℕ), ∃ c A : ℕ, ∀ m : Fin n → ℤ, StrictAnti m →
    ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∃ Ξ : TR.AlgRep ℚ n, (∀ v, Ξ.HasInfChar v ((infOf m).map Neg.neg)) ∧ Ξ.d ≤ c * (H + 1) ^ A

def CohBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (Γ : Subgroup (GL (Fin n) F)), Γ.FiniteIndex → ∃ c A : ℕ,
    ∀ M : ℕ, 1 ≤ M → ∀ (d : ℕ) (ξ : GL (Fin n) F →* Matrix (Fin d) (Fin d) ℂ),
      cohDim Γ (KLev F n (3 * M)) ξ ≤ (c * M ^ A * d : ℕ)

def CompatAtLQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (wt : ℤ) (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub ℚ n), Continuous r → IsIrr r →
    ∀ (M : ℕ) (m : Fin n → ℤ), 1 ≤ M → StrictAnti m → Level l M m r →
    (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → π.IsRegAlg → AttR ι r π →
    ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l ℚ Ω (Dec (F := ℚ) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := ℚ) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := ℚ) A).subtype) = rc (algNorm σ)

end UpperTheory.V.Af
