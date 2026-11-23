import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds

noncomputable section

namespace Formalism.L2.SG.IdCell

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S

def StarIsConj (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

def TraceNondeg (K E : Type) [Field K] [Field E] [Algebra K E] : Prop :=
  ∀ a : E, (∀ x : E, Algebra.trace K E (a * x) = 0) → a = 0

def SameFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
    (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E) : Prop :=
  ∀ i : Fin (r + 1), F'.fvec i - c i • F.fvec i ∈ F.Xa i.val

def RelevScalar (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] : Prop :=
  ∀ (S : HSpace E) (r : ℕ) (T T' : E) (F : FlagG S r T) (F' : FlagG S r T') (c : Fin (r + 1) → E),
    TraceNondeg K E → T ≠ 0 → T' ≠ 0 → SameFlag F F' c → Relevant K F F' →
    ∀ i : Fin (r + 1), c i = c (Fin.last r)

def NormRoot (E : Type) [Field E] [NumberField E] [StarRing E] : Prop :=
  ∀ (S : HSpace E) (r : ℕ) (T T' : ℕ) (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E))
    (c : Fin (r + 1) → E) (ζ : (𝓞 E)ˣ),
    StarIsConj E → 0 < T → 0 < T' → SameFlag F F' c → c (Fin.last r) = ((ζ : 𝓞 E) : E) →
    T = T' ∧ ∃ n : ℕ, 0 < n ∧ ζ ^ n = 1

def RootModP (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ (g : ℕ) (P : HeightOneSpectrum (𝓞 E)) (ζ : 𝓞 E),
    g.Prime → 3 ≤ g → (g : 𝓞 E) ∈ P.asIdeal → (g : 𝓞 E) ∉ P.asIdeal ^ 2 →
    (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ζ - 1 ∈ P.asIdeal → ζ = 1

def IdCellFrame (E K : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E] : Prop :=
  ∀ (S : HSpace E) (r : ℕ) (T T' : ℕ) (F : FlagG S r (T : E)) (F' : FlagG S r (T' : E))
    (c : Fin (r + 1) → E) (ζ : (𝓞 E)ˣ) (g : ℕ) (P : HeightOneSpectrum (𝓞 E)),
    StarIsConj E → TraceNondeg K E → 0 < T → 0 < T' →
    SameFlag F F' c → c (Fin.last r) = ((ζ : 𝓞 E) : E) → Relevant K F F' →
    g.Prime → 3 ≤ g → (g : 𝓞 E) ∈ P.asIdeal → (g : 𝓞 E) ∉ P.asIdeal ^ 2 →
    (ζ : 𝓞 E) - 1 ∈ P.asIdeal →
    T = T' ∧ ∀ i : Fin (r + 1), c i = 1

theorem idCellFrame_of {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Algebra K E]
    (hR : RelevScalar E K) (hN : NormRoot E) (hM : RootModP E) : IdCellFrame E K := by
  intro S r T T' F F' c ζ g P hstar htr hT hT' hsame hc hrel hg hg3 hgP hgP2 hζ
  obtain ⟨hTT, n, hn, hζn⟩ := hN S r T T' F F' c ζ hstar hT hT' hsame hc
  have hζ1 : (ζ : 𝓞 E) = 1 :=
    hM g P ζ hg hg3 hgP hgP2 ⟨n, hn, by rw [← Units.val_pow_eq_pow_val, hζn, Units.val_one]⟩ hζ
  refine ⟨hTT, fun i => ?_⟩
  have hT0 : ((T : ℕ) : E) ≠ 0 := by exact_mod_cast hT.ne'
  have hT0' : ((T' : ℕ) : E) ≠ 0 := by exact_mod_cast hT'.ne'
  rw [hR S r (T : E) (T' : E) F F' c htr hT0 hT0' hsame hrel i, hc, hζ1]
  simp

end Formalism.L2.SG.IdCell
