import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def adjM (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  Matrix.of fun i j => IsCMField.complexConj E (γ j i)

def IsUnitaryM (γ : Matrix (Fin n) (Fin n) E) : Prop := adjM γ * γ = 1

def actLat (γ : Matrix (Fin n) (Fin n) E) (Λ : GenLat E n) : GenLat E n :=
  ⟨Λ.La.map ((Matrix.mulVecLin γ).restrictScalars (𝓞 E))⟩

def CongAt (m : ℕ) (x y : Fin n → E) : Prop :=
  ∃ k : ℕ, Nat.Coprime k m ∧ ∀ j, ∃ b : 𝓞 E, (k : E) * (x j - y j) = (m : E) * (b : E)

abbrev StdMod (E : Type) [Field E] (n m : ℕ) : Type := Fin n → 𝓞 E ⧸ Ideal.span {(m : 𝓞 E)}

def IsIsomMod (Λ : GenLat E n) (m : ℕ) (ι : Λ.La →ₗ[𝓞 E] StdMod E n m) : Prop :=
  Function.Surjective ι ∧
  (∀ v : Λ.La, ι v = 0 ↔ ∃ u ∈ Λ.La, (v : Fin n → E) = (m : E) • u) ∧
  ∀ (v w : Λ.La) (x y : Fin n → 𝓞 E), (∀ j, ι v j = Ideal.Quotient.mk _ (x j)) →
    (∀ j, ι w j = Ideal.Quotient.mk _ (y j)) →
    ∃ b : 𝓞 E, ∑ j, (v : Fin n → E) j * IsCMField.complexConj E ((w : Fin n → E) j) -
      ∑ j, (x j : E) * IsCMField.complexConj E (y j : E) = (m : E) * (b : E)

def IsRep (Λ : GenLat E n) (m : ℕ) (ι : Λ.La →ₗ[𝓞 E] StdMod E n m) (bad : ℕ)
    (γ : Matrix (Fin n) (Fin n) E) : Prop :=
  IsUnitaryM γ ∧ (actLat γ Λ).TrivAt bad ∧ (actLat γ Λ).TrivAt m ∧
  ∀ (v : Λ.La) (x : Fin n → 𝓞 E), (∀ j, ι v j = Ideal.Quotient.mk _ (x j)) →
    CongAt m (γ.mulVec v) fun j => (x j : E)

def RepExists (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Prop :=
  Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) →
  ∀ (m bad : ℕ), 0 < m → 0 < bad → ∀ (Λ : GenLat E n) (ι : Λ.La →ₗ[𝓞 E] StdMod E n m),
    Λ.Unimod → IsIsomMod Λ m ι → ∃ γ, IsRep Λ m ι bad γ

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def pushLet {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ : LtN Dw n => letB c ℓ.1 ℓ.2.1 fun k => γ k ℓ.2.2

set_option autoImplicit false in
open NumberField MvPolynomial in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} in
variable (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet_letB {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet c γ (_root_.Formalism.L2.Pj.letB c σ i b) = _root_.Formalism.L2.Pj.letB c σ i (γ.mulVec b) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet _root_.Formalism.L2.Pj.letB
  simp only [map_sum, map_mul, aeval_C, aeval_X, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Finset.sum_mul, MvPolynomial.algebraMap_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def LevMoves {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (q q' : Fin n → LevQ Dw l) : Prop :=
  ∃ (k : ℕ) (g : Matrix (Fin n) (Fin n) (𝓞 E)), Nat.Coprime k l.M ∧ (∀ i j, (g i j : E) = (k : E) * γ i j) ∧
    ∀ i, (k : 𝓞 E) • q' i = ∑ j, g i j • q j

def FixesDatum {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (w : (Fin n → LevQ Dw l) → c.F) : Prop :=
  ∀ q q', LevMoves γ q q' → w q' = w q

variable (Dw) in

def IsBeta {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

variable (l) in

def BadOK (bad : ℕ) : Prop :=
  0 < bad ∧ 2 ∣ bad ∧ l.M ∣ bad ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∣ bad

def HidaSetting [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  IsGalois ℚ E ∧ Odd (Dw.p + Dw.q) ∧ Even n ∧ IsNab Xo c nab

def RepId (nab : NabV Xo c) {n : ℕ} (Λ : GenLat E n) (β : c.F) (γ : Matrix (Fin n) (Fin n) E) (β' ζ : c.F) : Prop :=
  ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c γ w →
  ∀ (N N' : ℕ), Λ.LevOK N l.M → (actLat γ Λ).LevOK N' l.M →
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
    ShortValAt Xo c nab w Λ β N P y v → ShortValAt Xo c nab w (actLat γ Λ) β' N' (pushLet c γ P) y v' →
      v' = algebraMap c.F S ζ * v

def ChangeWith [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (good : c.F → Prop) : Prop :=
  HidaSetting Xo c nab n → ∀ (bad : ℕ), BadOK l bad →
  ∀ (Λ : GenLat E n) (γ : Matrix (Fin n) (Fin n) E) (β β' : c.F),
    Λ.Unimod → IsUnitaryM γ → Λ.TrivAt bad → (actLat γ Λ).TrivAt bad →
    IsBeta Dw c Λ β → IsBeta Dw c (actLat γ Λ) β' →
    ∃ ζ : c.F, good ζ ∧ RepId Xo c nab Λ β γ β' ζ

def ChangeId [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  ChangeWith Xo c nab n fun ζ => ζ ≠ 0

def ChangeAbs [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  ChangeWith Xo c nab n fun ζ => ∀ σ : c.F →+* ℂ, ‖σ ζ‖ = 1

def ChangeRoot [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  ChangeWith Xo c nab n fun ζ => ∃ k : ℕ, 0 < k ∧ ζ ^ k = 1

def IsTh (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ShortValAt Xo c nab w Λ β N P y (f p y)

def thSpan (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) : Submodule (𝓞 c.F) (Rul Xo c) :=
  Submodule.span (𝓞 c.F) {f | f ∈ sec Xo c a n ∧ ∃ P ∈ harmL c Λ a, IsTh Xo c nab w Λ β N P f}

def SpanClass [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  HidaSetting Xo c nab n → ∀ (bad : ℕ), BadOK l bad →
  ∀ (Λ : GenLat E n) (γ : Matrix (Fin n) (Fin n) E) (β β' : c.F),
    Λ.Unimod → IsUnitaryM γ → Λ.TrivAt bad → (actLat γ Λ).TrivAt bad →
    IsBeta Dw c Λ β → IsBeta Dw c (actLat γ Λ) β' →
    ∀ (w : (Fin n → LevQ Dw l) → c.F), FixesDatum c γ w →
    ∀ (N N' : ℕ), Λ.LevOK N l.M → (actLat γ Λ).LevOK N' l.M → ∀ a : (E →+* ℂ) × ℕ → ℕ,
      thSpan Xo c nab w (actLat γ Λ) β' N' a = thSpan Xo c nab w Λ β N a

def OnPairs [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  HidaSetting Xo c nab n → ∀ (bad : ℕ), BadOK l bad →
  ∀ (Λ₀ : GenLat E n) (ι : Λ₀.La →ₗ[𝓞 E] StdMod E n l.M) (γ₁ γ₂ : Matrix (Fin n) (Fin n) E) (β₁ β₂ : c.F),
    Λ₀.Unimod → IsIsomMod Λ₀ l.M ι → IsRep Λ₀ l.M ι bad γ₁ → IsRep Λ₀ l.M ι bad γ₂ →
    IsBeta Dw c (actLat γ₁ Λ₀) β₁ → IsBeta Dw c (actLat γ₂ Λ₀) β₂ →
    ∃ ζ : c.F, (∃ k : ℕ, 0 < k ∧ ζ ^ k = 1) ∧
      ∀ (w : (Fin n → LevQ Dw l) → c.F) (N₁ N₂ : ℕ),
        (actLat γ₁ Λ₀).LevOK N₁ l.M → (actLat γ₂ Λ₀).LevOK N₂ l.M → ∀ a : (E →+* ℂ) × ℕ → ℕ,
        (∀ P ∈ harmL c Λ₀ a, ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v₁ v₂ : S),
          ShortValAt Xo c nab w (actLat γ₁ Λ₀) β₁ N₁ (pushLet c γ₁ P) y v₁ →
          ShortValAt Xo c nab w (actLat γ₂ Λ₀) β₂ N₂ (pushLet c γ₂ P) y v₂ →
            v₂ = algebraMap c.F S ζ * v₁) ∧
        thSpan Xo c nab w (actLat γ₂ Λ₀) β₂ N₂ a = thSpan Xo c nab w (actLat γ₁ Λ₀) β₁ N₁ a

def ChangeOfRepresentative [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) : Prop :=
  RepExists E n ∧ ChangeId Xo c nab n ∧ ChangeAbs Xo c nab n ∧ ChangeRoot Xo c nab n ∧
    SpanClass Xo c nab n ∧ OnPairs Xo c nab n

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
