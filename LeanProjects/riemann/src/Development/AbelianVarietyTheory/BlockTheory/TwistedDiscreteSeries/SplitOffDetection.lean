import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.ThetaTrace

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (l) in

structure IsSplitOff (P : Ideal (𝓞 E)) (p : ℕ) : Prop where
  max : P.IsMaximal
  split : P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤
  prime : p.Prime
  under : (p : 𝓞 E) ∈ P
  off : ¬ p ∣ l.M'

variable (Xo : Moduli Dw l) (c : Coeff l)

def HasTransform (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  HkEx (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y')
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
    (ex Dw a n) (hkScal c cq P i n)

def Detects (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  PtsDetect (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (fun t y y' => FrBor t y y') (ex Dw a n)

def FinKer (P : Ideal (𝓞 E)) (p i : ℕ) : Prop :=
  HkFin (K := c.F) (fun S _ _ => FrPt Xo c S) (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y)

def IsTransform (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (n : ℕ) (f g : Rul Xo c) : Prop :=
  HkRel (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun Ω _ _ _ y => hkKer (Xo := Xo) P p i Ω y) (fun Ω _ _ _ y C z => hkRelFr P p i (hkTr Xo c p) Ω y C z)
    (hkScal c cq P i n) f g

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cuspIn (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (sec Xo c a n) :=
  (cusp Xo c U a n).comap (sec Xo c a n).subtype

def KeepsCusp (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (hE : HasTransform Xo c P p i cq a n) (hD : Detects Xo c a n) (hF : FinKer Xo c P p i),
    HeckeStabW hE hD hF (cuspIn Xo c U a n)

variable {Xo c U} {P : Ideal (𝓞 E)} {p i : ℕ} {cq : c.F} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}

theorem keepsCusp_iff_exists (hE : HasTransform Xo c P p i cq a n) (hD : Detects Xo c a n)
    (hF : FinKer Xo c P p i) : KeepsCusp Xo c U P p i cq a n ↔
      ∀ f ∈ cusp Xo c U a n, ∃ g ∈ cusp Xo c U a n, IsTransform Xo c P p i cq n f g := by
  constructor
  · intro h f hf
    exact ⟨_, h hE hD hF ⟨f, hf.1⟩ hf, hkOp_spec hE hD hF ⟨f, hf.1⟩⟩
  · intro h hE' hD' hF' f hf
    obtain ⟨g, hg, hr⟩ := h f hf
    have e := hkRel_unique hD' (hkOp hE' hD' hF' f).2 hg.1 (hkOp_spec hE' hD' hF' f) hr
    show (hkOp hE' hD' hF' f).1 ∈ cusp Xo c U a n
    rw [e]
    exact hg

theorem IsSplitOff.absNorm_ne_zero (h : IsSplitOff l P p) : (Ideal.absNorm P : c.F) ≠ 0 := by
  rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  rintro rfl
  exact h.prime.ne_zero (by exact_mod_cast Ideal.mem_bot.1 h.under)

end Local

def SecTransform : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ) (cq : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
    1 ≤ Dw.p + Dw.q → IsSplitOff l P p → i ≤ Dw.p + Dw.q → Even n → HasTransform Xo c P p i cq a n

def CuspTransform : Prop :=
  ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j →
    ∀ (P : Ideal (𝓞 D.host.E)) (p i : ℕ) (cq : T.Q.c.F) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      IsSplitOff T.Q.l P p → i ≤ D.R.r → Dom a n → KeepsCusp (T.Q.Xo j) T.Q.c (T.U j) P p i cq a n

def HeckeTransform : Prop := SecTransform ∧ CuspTransform

end GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection
