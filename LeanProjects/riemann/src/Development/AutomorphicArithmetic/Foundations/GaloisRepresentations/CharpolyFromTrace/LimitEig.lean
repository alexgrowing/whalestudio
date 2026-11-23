import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {k Γ I : Type} [Field k] [Group Γ] {a c : ℕ}

abbrev mat (ρ : Γ →* GL (Fin a) k) (g : Γ) : Matrix (Fin a) (Fin a) k := ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)

def word (ρ : Γ →* GL (Fin a) k) (L : List (Γ × k)) : Matrix (Fin a) (Fin a) k :=
  (L.map fun p => mat ρ p.1 - p.2 • (1 : Matrix (Fin a) (Fin a) k)).prod

def Kills (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (χ : I → k) (ω : Fin c → I → k) : Prop :=
  ∀ (σ : Fin c → I) (s : I), word ρ (List.ofFn (fun b => (j (σ b), ω b (σ b))) ++ [(j s, χ s)]) = 0

def TrSum (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k) : Prop :=
  ∀ s, trc ρ (j s) = ∑ i, κ i s

theorem word_nil (ρ : Γ →* GL (Fin a) k) : word ρ [] = 1 := rfl

theorem word_cons (ρ : Γ →* GL (Fin a) k) (p : Γ × k) (L : List (Γ × k)) :
    word ρ (p :: L) = (mat ρ p.1 - p.2 • 1) * word ρ L := by simp [word]

theorem word_append (ρ : Γ →* GL (Fin a) k) (L M : List (Γ × k)) : word ρ (L ++ M) = word ρ L * word ρ M := by
  simp [word]

end Abstract

section Limit

variable {k Γ I : Type} [NormedField k] [Group Γ] {a c : ℕ}

structure Near (r : Γ →* GL (Fin a) k) (H : Subgroup Γ) (ε : ℝ) where

  n : ℕ

  c : Fin n → k

  z : Fin n → k

  ρ : Fin n → (H →* GL (Fin a) k)
  le : ∀ (m : ℕ) (g : H), ‖trc r g - ∑ i, c i * z i ^ m * trc (ρ i) g‖ ≤ ε

def Near.self (r : Γ →* GL (Fin a) k) (H : Subgroup Γ) {ε : ℝ} (hε : 0 ≤ ε) : Near r H ε :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => r.comp H.subtype, fun m g => by simpa [trc] using hε⟩

def Near.restrict {r : Γ →* GL (Fin a) k} {H H' : Subgroup Γ} {ε : ℝ} (F : Near r H ε) (h : H' ≤ H) : Near r H' ε :=
  ⟨F.n, F.c, F.z, fun i => (F.ρ i).comp (Subgroup.inclusion h), fun m g => F.le m (Subgroup.inclusion h g)⟩

def NearTr (r : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (H : Subgroup Γ) (hj : ∀ s, j s ∈ H) (F : Near r H ε) (e : Fin a → I → ℕ),
    ∀ i, TrSum (F.ρ i) (fun s => ⟨j s, hj s⟩) fun t s => κ t s * F.z i ^ e t s

def NearKills (r : Γ →* GL (Fin a) k) (j : I → Γ) (χ : I → k) (ω : Fin c → I → k) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (H : Subgroup Γ) (_ : H.Normal) (hj : ∀ s, j s ∈ H) (F : Near r H ε) (e₀ : I → ℕ) (e : Fin c → I → ℕ),
    ∀ i, Kills (F.ρ i) (fun s => ⟨j s, hj s⟩) (fun s => χ s * F.z i ^ e₀ s) fun b s => ω b s * F.z i ^ e b s

end Limit

def TraceNormal : Prop :=
  ∀ (k Γ : Type) [Field k] [CharZero k] [IsAlgClosed k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r →
    ∀ H : Subgroup Γ, H.Normal → ∀ M ∈ Submodule.span k (Set.range fun g : H => mat r g),
      (∀ g : H, (M * mat r g).trace = 0) → M = 0

def TrLimit : Prop :=
  ∀ (k Γ I : Type) [NormedField k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k),
    NearTr r j κ → TrSum r j κ

def KillsLimit : Prop :=
  ∀ (k Γ I : Type) [NormedField k] [CharZero k] [IsAlgClosed k] [Group Γ] (a c : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r →
    ∀ (j : I → Γ) (χ : I → k) (ω : Fin c → I → k), NearKills r j χ ω → Kills r j χ ω

def CharpolyOfTr : Prop :=
  ∀ (k Γ I : Type) [Field k] [CharZero k] [IsAlgClosed k] [Group Γ] [Group I] (a : ℕ) (r : Γ →* GL (Fin a) k) (j : I →* Γ)
    (κ : Fin a → I →* kˣ), TrSum r j (fun i s => (κ i s : k)) → ∀ s, (mat r (j s)).charpoly = ∏ i, (X - C (κ i s : k))

def KillsOfTr : Prop :=
  ∀ (k Γ I : Type) [Field k] [CharZero k] [Group Γ] [Group I] (a c : ℕ) (r : Γ →* GL (Fin a) k) (j : I →* Γ),
    IsSSRep (r.comp j) → ∀ (κ : Fin a → I →* kˣ) (χ : I → k) (ω : Fin c → I → k), TrSum r j (fun i s => (κ i s : k)) →
    (∀ i, (∀ s, (κ i s : k) = χ s) ∨ ∃ b, ∀ s, (κ i s : k) = ω b s) → Kills r j χ ω

section Weil

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def EigZero (x : WD h) (ξ : ↥(Ine (F := E) A) → ℂ) : Prop :=
  ∀ (n : ℕ) (x' : WDRep h (Fin n → ℂ)), WD.mk x' = x → ∀ v, (∀ s, x'.ρ (ineIncl h s) v = ξ s • v) → x'.N v = 0

def InePol {a : ℕ} (x : WD h) (κ : Fin a → ↥(Ine (F := E) A) → ℂ) : Prop :=
  ∀ s, x.charPol (ineIncl h s) = ∏ i, (X - C (κ i s))

end Weil

def EigOfKills : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ι : Qbar l ≃+* ℂ) (a c : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (χ : ↥(Ine (F := E) A) → Qbar l) (ω : Fin c → ↥(Ine (F := E) A) → Qbar l),
      Kills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) χ ω →
      ∀ ξ : ↥(Ine (F := E) A) → ℂ, (∀ b, ∃ s, ι (ω b s) ≠ ξ s) → EigZero (wdOf h hl ι r) ξ

def SSOfMono0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → (wdOf h hl ι r).mono0 →
      IsSSRep (r.comp (Ine (F := E) A).subtype)

def Mono0OfEig : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (a : ℕ) (κ : Fin a → ↥(Ine (F := E) A) →* ℂˣ),
    InePol x (fun i s => (κ i s : ℂ)) → (∀ ξ : ↥(Ine (F := E) A) → ℂ, EigZero x ξ) → x.mono0

def LimitPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ κ : Fin a → ↥(Ine (F := E) A) →* ℂˣ,
      NearTr r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (κ i s)) →
      InePol (wdOf h hl ι r) fun i s => (κ i s : ℂ)

def LimitEig : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (ι : Qbar l ≃+* ℂ) (a c : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r →
    ∀ (ξ : ↥(Ine (F := E) A) → ℂ) (ω : Fin c → ↥(Ine (F := E) A) → ℂ),
      NearKills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (ξ s)) (fun b s => ι.symm (ω b s)) →
      (∀ b, ∃ s, ω b s ≠ ξ s) → EigZero (wdOf h hl ι r) ξ

end UpperTheory.Gal.NearKilling
