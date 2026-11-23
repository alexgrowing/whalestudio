import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

def infOf {n : ℕ} (m : Fin n → ℤ) : Multiset ℂ := Finset.univ.val.map fun i => ((n : ℂ) - 1) / 2 + (m i : ℂ)

def SigK (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ GlobalTheory.ContraPair.DualIsConj π ∧ HasFixed π.finPart (KLev K n M)}

def SigQ {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (TR.CuspSub ℚ n) :=
  {π | (∀ v, π.HasInfChar v (infOf m)) ∧ (∃ χ : HChar ℚ, π.IsSelfDualBy χ) ∧ HasFixed π.finPart (KLev ℚ n M)}

def CardK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigK K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def CardQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (TR.CuspSub ℚ n), (∀ π ∈ S, π ∈ SigQ m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def ConjK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigK K m M, ∃ π' ∈ SigK K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def ConjQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigQ m M, ∃ π' ∈ SigQ m M, ∀ w B, π.HasSat w B →
      ∃ B', π'.HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def SatK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n M : ℕ) (π : CuspSub K n), HasFixed π.finPart (KLev K n M) →
    ∀ w : HeightOneSpectrum (𝓞 K), (M : 𝓞 K) ∉ w.asIdeal → ∃ B, (CG.mk π).HasSat w B

def SatR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n M : ℕ) (π : TR.CuspSub F n), HasFixed π.finPart (KLev F n M) →
    ∀ w : HeightOneSpectrum (𝓞 F), (M : 𝓞 F) ∉ w.asIdeal → ∃ B, π.HasSat w B

def PureK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ,
    ∀ π ∈ SigK K m M, ∀ w B, (CG.mk π).HasSat w B → ∀ b ∈ algSat n (normV w) B,
      ‖b‖ = (normV w : ℝ) ^ (((n : ℝ) - 1) / 2)

def PureQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ M : ℕ,
    ∀ π ∈ SigQ m M, ∀ w B, π.HasSat w B → ∀ b ∈ algSat n (normV w) B, ‖b‖ = (normV w : ℝ) ^ (-(wt : ℝ) / 2)

def SlopesIn {n : ℕ} (q : ℕ) (m : Fin n → ℤ) (B : Multiset ℂ) : Prop :=
  ∀ b ∈ B, (∀ a : ℤ, (∀ i, -a ≤ m i) → IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)) ∧
    ∀ a : ℤ, (∀ i, m i ≤ a) → IsIntegral ℤ ((q : ℂ) ^ a * b)

def IntK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigK K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def IntQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigQ m M, ∀ w : HeightOneSpectrum (𝓞 ℚ), (M : 𝓞 ℚ) ∉ w.asIdeal →
      ∀ B, π.HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def LevelK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), LevelO l M m r → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

def LevelQ : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
      (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub ℚ n), IsIrr r → Level l M m r →
      (∃ θ, IsCycWt l wt θ ∧ DualTw r θ) → π.IsRegAlg → AttR ι r π →
      π ∈ SigQ m M ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), (l : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

def IsoOfFrob : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' →
    (∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, FrobEig ι r w B ∧ FrobEig ι r' w B) → RepIso r r'

def SelfDualQ : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (wt : ℤ) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub ℚ n) (θ : G ℚ Ω →* (Qbar l)ˣ),
    IsCycWt l wt θ → DualTw r θ → AttR ι r π → ∃ χ : HChar ℚ, π.IsSelfDualBy χ ∧
      ∃ (art : Neutral.B1.Ideles ℚ →* GlobalTheory.HeckeGal.Gab ℚ Ω) (a : (ℚ →+* ℂ) → ℤ), GlobalTheory.HeckeGal.IsGlobalArtin art ∧
        GlobalTheory.HeckeGal.IsAlgPos χ a ∧ GlobalTheory.HeckeGal.IsLAdicOf art ι χ a (θ * cycBar ℚ Ω l ^ ((n : ℤ) - 1))

end UpperTheory.V.Af
