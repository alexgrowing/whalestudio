import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Bc

namespace UpperTheory.V.Br

def SigP (K : Type) [Field K] [NumberField K] [IsCMField K] {n : ℕ} (m : Fin n → ℤ) (M : ℕ) : Set (CuspSub K n) :=
  {π | (∀ τ, π.HasInfChar τ (infOf m)) ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ HasFixed π.finPart (KLev K n M)}

structure LevelS {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] {n : ℕ} (M : ℕ)
    (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    ∃ κ, FlagAt M m r A κ
  safe : l ∣ M ∨ ∀ i j, m i ≠ m j + 1

structure AdmP {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G K Ω →* GL (Fin n) (Qbar l)) : Prop where
  irr : IsIrr r
  aut : ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π
  level : LevelS l M m r

structure LevelC {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] {n : ℕ} (M : ℕ)
    (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧
    (∃ κ, FlagAt M m r A κ) ∧ PotCrysAt r A

def CardP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ), StrictAnti m → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ S : Finset (CuspSub K n), (∀ π ∈ S, π ∈ SigP K m M) → (∀ π ∈ S, ∀ π' ∈ S, π.Iso π' → π = π') →
        S.card ≤ c * (M * (H + 1)) ^ A

def CharConj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 1 → ∀ (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a → ∀ σ : ℂ ≃+* ℂ,
    ∃ χ' : HChar F, (∀ v, χ'.locInf v (-1) = χ.locInf v (-1)) ∧
      ∀ w, χ.UnrAt w → χ'.UnrAt w ∧ ((χ'.val w : ℂˣ) : ℂ) = σ ((χ.val w : ℂˣ) : ℂ)

def SatOfPol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy P ψ →
    ∀ w : HeightOneSpectrum (𝓞 E), ψ.UnrAt w → ∀ B B', (CG.mk P).HasSat w B → (CG.mk P).HasSat (cPl w) B' →
      B'.map (·⁻¹) = B.map (· * (ψ.val w)⁻¹)

def ConjP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (σ : ℂ ≃+* ℂ), ∀ π ∈ SigP K m M, ∃ π' ∈ SigP K m M, ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ

def PureP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m →
    (∀ i, m i + m i.rev = wt) → ∀ M : ℕ, ∀ π ∈ SigP K m M, ∀ w B, (CG.mk π).HasSat w B → ∀ b ∈ algSat n (normV w) B,
      ‖b‖ = (normV w : ℝ) ^ (-(wt : ℝ) / 2)

def IntP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ π ∈ SigP K m M, ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M →
      ¬ (p : ℤ) ∣ discr K → ∀ B, (CG.mk π).HasSat w B → SlopesIn (normV w) m (algSat n (normV w) B)

def CompatP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (l : ℕ) [Fact l.Prime]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n),
    Continuous r → (CG.mk π).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw),
      IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype) = rc (algNorm σ)

def LevelP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m →
    ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), LevelS l M m r → (CG.mk π).IsRegAlg →
      (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) → AttC ι r π →
      π ∈ SigP K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

def CountP : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
    ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) → ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
    ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
      ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
        ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
          D.Classifies (Ω := Ω) ι w (AdmP ι M m)

def QuadFam : Prop :=
  ∀ N : ℕ, ∃ (K : Fin N → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, IsCMField (K i)),
    (∀ i, Module.finrank ℚ (K i) = 2) ∧ ∀ i j, i ≠ j → IsCoprime (discr (K i)) (discr (K j))

def SignNe : Prop :=
  ∀ (K K' Ω : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower ℚ K Ω] [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → IsCoprime (discr K) (discr K') →
    (res ℚ Ω K).range ≠ (res ℚ Ω K').range

def TwCard : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k), IsIrr r → ∀ S : Finset (Γ →* kˣ),
    (∀ δ ∈ S, RepIso r (tw r δ)) → S.card ≤ n ^ 2

def ResTwo : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] [CharZero k] (n : ℕ) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
    (∀ s, δ s = 1 ↔ s ∈ φ.range) → (∀ s, δ s = 1 ∨ δ s = -1) → ∀ r : Γ →* GL (Fin n) k,
    (IsIrr r → ¬ RepIso r (tw r δ) → IsIrr (r.comp φ)) ∧
    ∀ r' : Γ →* GL (Fin n) k, IsIrr (r.comp φ) → RepIso (r.comp φ) (r'.comp φ) → RepIso r r' ∨ RepIso (tw r δ) r'

def FrobEx : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)),
    (∀ B B', FrobEig ι r w B → FrobEig ι r w B' → B = B') ∧
    ∀ M : ℕ, LevelAway l M r → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ((M : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ B, FrobEig ι r w B

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

def PotMove : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (A A' : ValuationSubring Ω) (g : G F Ω), (∀ x, x ∈ A' ↔ g x ∈ A) → PotCrysAt r A → PotCrysAt r A'

def PotRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (A : ValuationSubring Ω), PotCrysAt r A → PotCrysAt (r.comp (res F Ω K)) A

def LevelRes : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), LevelC l M m r → Level l M m (r.comp (res F Ω K))

def LevelPot : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      AdmR ι M m wt r → LevelC l M m r

def AdmRes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ),
    StrictAnti m → ∀ M : ℕ, 1 ≤ M → ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [IsScalarTower ℚ K Ω] [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      AdmR ι M m wt r → IsIrr (r.comp (res ℚ Ω K)) → AdmP ι M m (r.comp (res ℚ Ω K))

def FinCompR : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (π : TR.CuspSub F a), ∃ τ, π.IsFinComp τ

end UpperTheory.V.Br
