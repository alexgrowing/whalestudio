import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def SubSystem.twistPows (F : SubSystem S x E) : (t : ℕ) → (Fin t → SubSystem S x Ω) → (Fin t → ℕ) → SubSystem S x E
  | 0, _, _ => F
  | t + 1, L, n => (F.twistPows t (fun j => L j.castSucc) (fun j => n j.castSucc)).twist ((L (Fin.last t)).pow (n (Fin.last t)))

variable (k : Type u) [Field k] [Algebra k Ω] [Module k E] [IsScalarTower k Ω E]

def eulerChar (F : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (F.H i) : ℤ)

end Defs

def SnapperFinite.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x)
    (n : Fin t → ℕ) (c : ℤ) (i : ℕ),
    FiniteDimensional k (((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c)).H i)

def Snapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ),
    IsSubvar x (primeOf (S := k) x) e →
    ∀ (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
      (F : SubFamily k x E), (∀ I, (F.sub I).FG) → ∀ (t : ℕ) (L : Fin t → LineBundle k x),
    ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, Q.totalDegree ≤ e ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        ((eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist
          (twistSys k x c)) : ℤ) : ℚ) =
          MvPolynomial.eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

def TwistVanishAll.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (G B : LineBundle S x) (r : ℕ) (η : Fin (r + 1) → Ω),
    (∀ j, η j ∈ B.secs) → (∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) →
    ∃ c₀ : ℤ, ∀ (i b : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton (((G.twist (B.pow b)).twist (twistSys S x c)).H i)

def AmpleVanish.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ H : LineBundle S x, IsVeryAmple H.toSubSystem →
    ∃ a₀ : ℕ, ∀ (i a : ℕ), 1 ≤ i → a₀ ≤ a → Subsingleton ((F.twist (H.pow a)).H i)

section Hypotheses

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
