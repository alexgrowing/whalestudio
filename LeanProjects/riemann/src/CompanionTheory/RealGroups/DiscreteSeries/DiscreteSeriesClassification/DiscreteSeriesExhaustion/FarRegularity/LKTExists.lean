import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding

noncomputable section

open Finset

namespace CompanionTheory.RgExh.U

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd Ft Sup Wt om cpt allT wt LocFin)
open CompanionTheory.D.DSIC (KRel KUnit)
open PI.UpqRep (vNormSq rhoC nsq CDom)

variable {n : ℕ}

def Lc (n : ℕ) : ℝ := 8 * ((n : ℝ) + 1) ^ 3

def xv (ε : Fin n → Bool) (γ : Fin n → ℝ) : Fin n → ℝ := γ + (2 : ℝ) • rhoC ε

def IsMinG {V : Type} [AddCommGroup V] [Module ℂ V] (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (γ : Fin n → ℝ) : Prop :=
  ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → vNormSq ε γ ≤ vNormSq ε μ

def Gapped (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (L : ℝ) : Prop :=
  Antitone (xv ε γ) ∧ Monotone lev ∧ ∀ a b, lev a < lev b → L ≤ xv ε γ a - xv ε γ b

abbrev inU (lev : Fin n → ℕ) (i : Pos n) : Prop := lev i.1.1 < lev i.1.2

abbrev inR (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Pos n) : Prop := cpt ε i ∨ inU lev i

def SuppIn {V : Type} [AddCommGroup V] [Module ℂ V] (P : Pos n → Prop) (y : Cn n V) : Prop :=
  ∀ A, y A ≠ 0 → ∀ i ∈ A, P i

def Deg {V : Type} [AddCommGroup V] [Module ℂ V] (j : ℕ) (y : Cn n V) : Prop := ∀ A, y A ≠ 0 → A.card = j

def omU (ε : Fin n → Bool) (lev : Fin n → ℕ) : Finset (Pos n) := univ.filter fun i => ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2

section Chains

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def adC (p q : Fin n) (i k : Pos n) : ℂ :=
  (if q = i.1.1 ∧ k.1 = (p, i.1.2) then 1 else 0) - (if i.1.2 = p ∧ k.1 = (i.1.1, q) then 1 else 0)

def adL (p q : Fin n) : Module.End ℂ (Cn n V) :=
  ∑ i : Pos n, ∑ k : Pos n, adC p q i k • (cre k * ann i)

def lF (E : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cn n V) := lift n (E p q) + adL p q

def evL (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ fun p => if lev p.1 = lev p.2 then E p.1 p.2 else 0

def evLc (lev : Fin n → ℕ) (E : Fin n → Fin n → Module.End ℂ V) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (Cn n V) :=
  FreeAlgebra.lift ℂ fun p => if lev p.1 = lev p.2 then lF E p.1 p.2 else 0

end Chains

def NumKG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (ν : Fin n → ℝ) (B C : Finset (Pos n)),
    Gapped ε γ lev (Lc n) → B.Nonempty → (∀ i ∈ B, ¬cpt ε i ∧ inU lev i) → (∀ i ∈ C, cpt ε i) →
    (∀ c d, c < d → ε c = ε d → ν d ≤ ν c) →
    (∀ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) → CDom ε ((xv ε γ - wt B - wt C) ∘ w) ν) →
    nsq (ν + rhoC ε) = nsq (xv ε γ - rhoC ε - wt B) → vNormSq ε ν < vNormSq ε γ

def VanKG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Gapped ε γ lev (Lc n) → KRel ε E → KUnit ε E →
    LocFin ε E → IsMinG ε E γ →
    ∀ (B : Finset (Pos n)) (j : ℕ) (z : Cn n V), B.Nonempty → (∀ i ∈ B, inU lev i) → Sup ε B j z →
      Wt (allT n) E (xv ε γ) z → bd ε E z = 0 →
      ∃ t : Cn n V, Sup ε B (j + 1) t ∧ Wt (allT n) E (xv ε γ) t ∧ bd ε E t = z

def InjR : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Gapped ε γ lev (Lc n) → GlRel E → KUnit ε E →
    LocFin ε E → IsMinG ε E γ →
    ∀ (u : V) (y : Cn n V), IsWeight E γ u → SuppIn (inR ε lev) y → Sup (allT n) ∅ ((CompanionTheory.D.LK.om ε).card + 1) y →
      bd (allT n) E y = Pi.single (CompanionTheory.D.LK.om ε) u → u = 0

def GenCOU : Prop :=
  ∀ (n : ℕ) (lev : Fin n → ℕ) (a b : FreeAlgebra ℂ (Fin n × Fin n)), Monotone lev →
    (∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (CompanionTheory.D.LK.ev E a)) ∧
      ∀ x : V, ∃ w : Pos n → V, CompanionTheory.D.LK.ev E a x - evL lev E b x = ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      ∀ (j : ℕ) (x : Cn n V), SuppIn (inU lev) x → Deg j x → bd (allT n) E x = 0 →
        ∃ w : Cn n V, SuppIn (inU lev) w ∧ Deg (j + 1) w ∧
          lift n (CompanionTheory.D.LK.ev E a) x - evLc lev E b x = bd (allT n) E w

def InjU : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Gapped ε γ lev (Lc n) → GlRel E → KUnit ε E →
    LocFin ε E → IsMinG ε E γ →
    ∀ (u : V) (y : Cn n V), KHighest ε E γ u → SuppIn (inU lev) y → Deg ((omU ε lev).card + 1) y →
      bd (allT n) E y = Pi.single (omU ε lev) u → u = 0

def COBlock : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, ∀ (ε : Fin n → Bool) (γ : Fin n → ℝ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ),
    Gapped ε γ lev (Lc n) → KUnit ε E → LocFin ε E → IsMinG ε E γ → ScalChar ⟨V, E, hE⟩ χ →
    (∃ u : V, u ≠ 0 ∧ KHighest ε E γ u) →
    ∃ σ : Equiv.Perm (Fin n), ∀ c : ℕ,
      ‖∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a) - ∑ a ∈ univ.filter (fun a => lev a = c), ((xv ε γ a : ℝ) : ℂ)‖ ≤ K

def UnitIneq : Prop :=
  ∀ n : ℕ, ∃ K : ℝ, ∀ (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ) (γ : Fin n → ℝ) (u : V),
    IsUnitary ε E → ScalChar ⟨V, E, hE⟩ χ → u ≠ 0 → KHighest ε E γ u →
    ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) ≤ nsq (γ + rhoC ε) + K

def FarNum : Prop :=
  ∀ (n : ℕ) (C δ K : ℝ), 0 < δ → ∃ N₀ : ℝ, ∀ (χ : Fin n → ℂ) (x r : Fin n → ℝ) (lev : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) (N : ℝ), Antitone x → Monotone lev → (∀ a, |r a| ≤ n) →
    (∀ a b, lev a = lev b → |x a - x b| ≤ n * Lc n) →
    (∀ c : ℕ, ‖∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a) - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)‖ ≤ K) →
    ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) ≤ ∑ a, (x a - r a) ^ 2 + K →
    (∀ a b, a ≠ b → δ * N ≤ |(χ a).re - (χ b).re|) → (∀ a, |(χ a).re| ≤ C * N ∧ |(χ a).im| ≤ C) → N₀ ≤ N →
    Function.Injective lev

def LKTExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E), Nontrivial V → IsUnitary ε E → LocFin ε E →
    IntWt ⟨V, E, hE⟩ →
    ∃ (γ : Fin n → ℝ) (u : V), u ≠ 0 ∧ KHighest ε E γ u ∧ IsMinG ε E γ ∧ (∀ a, ∃ m : ℤ, γ a = m) ∧
      ∀ a b, a < b → ε a = ε b → γ b ≤ γ a

def Renumber : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (s : Equiv.Perm (Fin n)),
    (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) →
    ∃ hE' : GlRel (fun a b => E (s a) (s b)),
      (IsUnitary ε E → IsUnitary (ε ∘ s) (fun a b => E (s a) (s b))) ∧
      (LocFin ε E → LocFin (ε ∘ s) (fun a b => E (s a) (s b))) ∧
      (∀ χ, ScalChar ⟨V, E, hE⟩ χ → ScalChar ⟨V, fun a b => E (s a) (s b), hE'⟩ χ) ∧
      (∀ γ u, KHighest ε E γ u ↔ KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) u) ∧
      (∀ γ, IsMinG ε E γ ↔ IsMinG (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s)) ∧
      rhoC (ε ∘ s) = rhoC ε ∘ s

end CompanionTheory.RgExh.U
