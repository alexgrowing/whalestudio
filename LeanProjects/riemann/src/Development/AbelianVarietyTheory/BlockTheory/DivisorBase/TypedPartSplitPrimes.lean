import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

open NumberField MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth

section Hom

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def IsIntHom {d d' : ℕ} (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
    (M : Matrix (Fin d') (Fin d) C) : Prop :=
  (∀ b, constantCoeff (φ b) = 0) ∧ (∀ b, MvIsInt v (φ b)) ∧
    ∀ b, subst φ (G'.lg b) = ∑ a, M b a • G.lg a

def intSpan (v : AddValuation C (WithTop ℝ)) {ι : Type} [Fintype ι] {d : ℕ} (u : ι → Fin d → C) : Set (Fin d → C) :=
  {x | ∃ a : ι → C, (∀ k, IsIntV v (a k)) ∧ x = ∑ k, a k • u k}

example {d : ℕ} (G : LogFGL v d) : IsIntHom G G (fun a => X a) 1 := by
  refine ⟨fun b => by simp, fun b α => ?_, fun b => ?_⟩
  · unfold IsIntV; rw [coeff_X]; split_ifs <;> simp
  · rw [show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
    simp [Matrix.one_apply, ite_smul]

end Hom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def UnramIn (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop := ¬ (p : ℤ) ∣ discr E

def SplitInK (H : Host E) (p : ℕ) : Prop := (H.d : ZMod p) ≠ 0 ∧ IsSquare (-(H.d : ZMod p))

def InertInK (H : Host E) (p : ℕ) : Prop := ¬ IsSquare (-(H.d : ZMod p))

example (H : Host E) : SplitInK H 2 := by
  have h : (H.d : ZMod 2) = 1 := by
    have := H.d_mod
    rw [← ZMod.natCast_mod H.d 2, show H.d % 2 = 1 by omega]; rfl
  refine ⟨by rw [h]; decide, 1, by rw [h]; decide⟩

variable {Dw : Datum H} {l : Level H}

section Labels

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def embX (τ : E →+* ℂ) : 𝓞 E →+* X.C := X.ιF.comp (io.comp (embK c τ))

theorem v_embX_le_one (τ : E →+* ℂ) (a : 𝓞 E) : X.v (embX io X τ a) ≤ 1 := by
  have h1 : IsIntegral ℤ (embX io X τ a) := map_isIntegral_int _ (RingOfIntegers.isIntegral a)
  exact X.ints.isIntegral_iff_v_le_one.1 h1.tower_top

def primeBelow (τ : E →+* ℂ) : Ideal (𝓞 E) where
  carrier := {a | X.v (embX io X τ a) < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    exact X.v.map_add_lt ha hb
  smul_mem' := fun a b hb => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hb ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right (v_embX_le_one io X τ a) zero_le hb

def IsFrob (σ σ' : E →+* ℂ) : Prop :=
  ∀ a : 𝓞 E, X.v (embX io X σ' a - embX io X σ a ^ p) < 1

def IsOrbit (τ : E →+* ℂ) {h : ℕ} (lab : ZMod h → (E →+* ℂ)) : Prop :=
  lab 0 = τ ∧ (∀ s, IsFrob io X (lab s) (lab (s + 1))) ∧ Function.Injective lab ∧
    ∀ σ, primeBelow io X σ = primeBelow io X τ ↔ ∃ s, lab s = σ

def FrobOnType : Prop :=
  ∀ σ σ' : E →+* ℂ, IsFrob io X σ σ' →
    (SplitInK H p → (InPsi H σ' ↔ InPsi H σ)) ∧
    (InertInK H p → (InPsi H σ' ↔ InPsi H (ComplexEmbedding.conjugate σ)))

end Labels

variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (Ch : IntegralChartA3 Xo c T io y) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

def IsPartAt (w : Ideal (𝓞 E)) {d' : ℕ} (G' : LogFGL (vX_vp X) d')
    (I : Matrix (Fin (chD Ch.ch)) (Fin d') X.C) (P : Matrix (Fin d') (Fin (chD Ch.ch)) X.C) : Prop :=
  (∃ ι, IsIntHom G' (fgl Ch X) ι I) ∧ (∃ π, IsIntHom (fgl Ch X) G' π P) ∧ P * I = 1 ∧
    ∀ ℓ : Lt1 Dw, (primeBelow io X ℓ.1 = w → (I * P).mulVec (lieVec Ch X ℓ) = lieVec Ch X ℓ) ∧
      (primeBelow io X ℓ.1 ≠ w → (I * P).mulVec (lieVec Ch X ℓ) = 0)

open Classical in

def TypedPartAt (τ : E →+* ℂ) : Prop :=
  ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧
  ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
  ∃ (d' : ℕ) (G' : LogFGL (vX_vp X) d') (ty : Fin d' → ZMod h)
    (I : Matrix (Fin (chD Ch.ch)) (Fin d') X.C) (P : Matrix (Fin d') (Fin (chD Ch.ch)) X.C),
    IsPartAt Ch X (primeBelow io X τ) G' I P ∧
    Nonempty (MuAction G' p h ty) ∧
    (∀ s, intSpan (vX_vp X) (fun b : {b : Fin d' // ty b = s} => fun e => I e b.1) =
      intSpan (vX_vp X) (fun k : Fin (Dw.mult (lab s)) => lieVec Ch X ⟨lab s, k⟩)) ∧
    (∀ s, Fintype.card {b : Fin d' // ty b = s} =
      if InPsi H (lab s) then Module.finrank (𝓞 E) Dw.La - Dw.q else Dw.q) ∧
    ∀ (s : ZMod h) (f : Lt1 Dw), f.1 = lab s →
      IsSatFrame (vX_vp X) (fun a => P.mulVec (frame Ch X f a)) ∧
      (∀ a b, ty b ≠ s → P.mulVec (frame Ch X f a) b = 0) ∧
      ∀ k : ℕ, nuFacC Ch X f k = detDepth G' (fun a => P.mulVec (frame Ch X f a)) k

omit [StarRing (𝓞 E)] in

example : Module.finrank (𝓞 E) Dw.La - Dw.q = Dw.p := by rw [Dw.rank]; omega

def FormalGroupTypes : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (p : ℕ) [Fact p.Prime], UnramIn E p →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p),
      FrobOnType io X ∧
      ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ), TypedPartAt Ch X τ

end GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes
