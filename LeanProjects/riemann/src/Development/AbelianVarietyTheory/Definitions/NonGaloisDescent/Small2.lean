import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.StepTwo

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def idl : Ideal (X.O0 i) := Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i)

def Small2 (M : ℕ) (L : Subgroup (GE N)) (z : GE N) : Prop :=
  Small i s L z ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ idl i

variable (M : ℕ) {R n : ℕ} (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))))

def PiLocalization₂ (A : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host) : Prop :=
  SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
    (∀ a, (∀ v, Over (P (.inl a)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ L) ∧
      ∀ σ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ a, DecV N (P (.inr a)) ≤ L ∧ ∀ (b : Fin R) (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (P (.inl b)) σ = Multiplicative.ofAdd (if a.val = b.val then 1 else 0)

def NF (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.det →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ F.coeff m ∉ idl i

def NFit (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → a = 0 ∨ ∃ b b', ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.adjugate b b' →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ (∀ j : Fin R, n ≤ j.val → m (.inl j) = 0) ∧ IsUnit (F.coeff m)

def Ext (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) : Prop :=
  ∀ q, P' (Sum.map id Fin.castSucc q) = P q

def Start : Prop :=
  ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (φ φ' : Fin n → GE N), n ≤ R → 4 * D.R.r * n + 2 < X.l i ^ M →
    IsTameInertiaElementAtTwistPrime X i z → Small i s L z → PiLocalization₂ i M d A L z P →
    (∀ a, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧ IsCj X (φ a) (φ' a)) → Corank bkP i s φ φ' 1 →
    NFit bkP i s M d P (4 * D.R.r * n + 1)

def Grow : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) (c : ℕ), n < R →
    c + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P' → Ext P P' →
    (NF bkP i s M d P c → NF bkP i s M d P' (c + 2 * D.R.r)) ∧ (NFit bkP i s M d P c → NFit bkP i s M d P' (c + 2 * D.R.r))

def Step : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) H S d A L z (P : Fin R ⊕ Fin n → PlE D.host) (w e : ℕ), n < R →
    IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e →
    2 * (e + 1) * w + 2 + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M →
    AdmFam X i M H S d → L ≤ H → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P → NFit bkP i s M d P (w + 1) →
    ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A L z P' ∧
      NF bkP i s M d P' (2 * (e + 1) * w + 2 + 2 * D.R.r)

end GlobalTheory.StepTwo
