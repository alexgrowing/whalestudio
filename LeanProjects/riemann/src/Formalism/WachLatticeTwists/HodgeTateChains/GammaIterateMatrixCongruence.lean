import Formalism.WachLatticeTwists.HodgeTateChains.FrobeniusPowerCongruence

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

def OverSub {AA WC : Type} [CommRing AA] [CommRing WC] (ι : AA →+* WC) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) WC) : Prop := ∃ M' : Matrix (Fin r) (Fin r) AA, M'.map ι = M

structure HypW (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ) where

  Xx : Matrix (Fin r) (Fin r) WC

  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1

  fixH : ∀ h ∈ H, Xx.map (act h) * ((ρ h : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC)) = Xx

  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx

  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P

  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] WC))
    = ((Gm g).map jA).map ι * Xx

  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}

  W4 : ∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ], (∀ g, E * (ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = ρ g * E) →
    ∃ E' : Matrix (Fin r) (Fin r) As, Xx * E.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

def LemmaAProp {AA WC : Type} [CommRing AA] [CommRing WC] (ι : AA →+* WC) (φ : WC →+* WC) (r : ℕ) :
    Prop :=
  ∀ Z S S' Y : Matrix (Fin r) (Fin r) WC, OverSub ι S → OverSub ι S' → OverSub ι Y →
    Z.map φ = S * Z * S' + Y → OverSub ι Z

def StatLemmaAMat : Prop :=
  ∀ (ℓ : ℕ) (AA WC : Type) [CommRing AA] [CommRing WC] (ι : AA →+* WC) (φ : WC →+* WC) (r : ℕ),
    (∀ M : Matrix (Fin r) (Fin r) WC, OverSub ι (ℓ • M) → OverSub ι M) →
    (∀ M : Matrix (Fin r) (Fin r) WC,
      (∀ n : ℕ, ∃ A B : Matrix (Fin r) (Fin r) WC, OverSub ι A ∧ M = A + (ℓ ^ n) • B) → OverSub ι M) →
    (∀ M : Matrix (Fin r) (Fin r) WC, OverSub ι M → OverSub ι (M.map φ)) →
    (∀ Z S S' : Matrix (Fin r) (Fin r) WC, OverSub ι S → OverSub ι S' →
      (∃ A B : Matrix (Fin r) (Fin r) WC, OverSub ι A ∧ Z.map φ - S * Z * S' = A + ℓ • B) →
      ∃ A B : Matrix (Fin r) (Fin r) WC, OverSub ι A ∧ Z = A + ℓ • B) →
    LemmaAProp ι φ r

def StatSandwichAA : Prop :=
  ∀ (AA WC : Type) [CommRing AA] [CommRing WC] (ι : AA →+* WC) (φ : WC →+* WC) (x ξ : AA)
    (r M0 h0 : ℕ) (Xx Xi P : Matrix (Fin r) (Fin r) WC) (P1 Q1 : Matrix (Fin r) (Fin r) AA),
    LemmaAProp ι φ r → φ (ι x) = ι (x * ξ) → (∀ a : WC, ι ξ * a = 0 → a = 0) →
    Xx * Xi = 1 → Xi * Xx = 1 → Xx.map φ = P * Xx → P1.map ι = (ι ξ) ^ M0 • P →
    P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) →
    OverSub ι ((ι x) ^ M0 • Xx) ∧ OverSub ι ((ι x) ^ h0 • Xi)

def StatSandwichOC : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (AA OC : Type) [CommRing AA] [CommRing OC] (ϑ : AA →+* OC) (x : AA)
    (c : OC) (r M0 h0 : ℕ) (A A' : Matrix (Fin r) (Fin r) AA),
    (ϑ x) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * c = (ℓ : OC) →
    A * A' = (x ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) →
    A' * A = (x ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) AA) →
    ∃ Y' : Matrix (Fin r) (Fin r) OC,
      A.map ϑ * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      Y' * A.map ϑ = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC)

def gamN {As : Type} [CommRing As] (σ : As →+* As) {r : ℕ} (G : Matrix (Fin r) (Fin r) As) :
    (Fin r → As) →+ (Fin r → As) where
  toFun v := (fun i => σ (v i)) ᵥ* G
  map_zero' := by ext; simp [Matrix.vecMul, dotProduct]
  map_add' a b := by
    ext j
    simp [Matrix.vecMul, dotProduct, add_mul, Finset.sum_add_distrib]

def GammaIterateMatrixCongruence : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (As R : Type) [CommRing As] [CommRing R] (σ : As →+* As) (πs : As)
    (ϑ : As →+* R) (z ϖ ϖ' : R) (r s n : ℕ) (G : Matrix (Fin r) (Fin r) As),
    (∀ a, σ a - a ∈ Ideal.span {(ℓ : As), πs}) →
    (∀ a ∈ Ideal.span {(ℓ : As), πs}, σ a - a ∈ (Ideal.span {(ℓ : As), πs}) ^ 2) →
    (∀ i j, (G - 1) i j ∈ Ideal.span {(ℓ : As), πs}) →
    ϑ πs = ϖ' → ϖ' ∣ (ℓ : R) → z ∣ (ℓ : R) → ϖ ∣ (ℓ : R) → z * ϖ ∣ ϖ' ^ (ℓ ^ (s + n)) →
    ∀ i j, z * ϖ ∣ ϑ (((⇑(gamN σ G))^[ℓ ^ (s + n + 1)] (Pi.single i 1)) j
      - (1 : Matrix (Fin r) (Fin r) As) i j)

def StatTwistUm : Prop :=
  ∀ (R : Type) [CommRing R] (t c : R) (r : ℕ) (Um : Matrix (Fin r) (Fin r) R),
    t ∣ c - 1 → (∀ i j, t ∣ (Um - 1) i j) → ∀ i j, t ∣ (c • Um - 1) i j

def StatGenM : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s H0 : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    PadicInt.valuation (((u ^ (ℓ ^ (s + n0 ℓ H0 + 1)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) = mOf ℓ s H0 ∧
      1 ≤ mOf ℓ s H0 ∧ 2 ≤ mOf ℓ s H0 ∧ s ≤ mOf ℓ s H0

def StatTopsAtM : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) (s H0 : ℕ), 1 ≤ s → (ℓ = 2 → 2 ≤ s) →
    PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s →
    (∀ (U : Finset ℤ) (a : ℤ) (n d : ℕ) (D : LLData ℓ n), d ≠ 0 →
      (∀ k, (D.piece k).Inputs (u ^ (ℓ ^ (s + n0 ℓ H0 + 1))) U (a + k)) → D.LES → D.T5 → D.CorRes d →
      TorsKilled ℓ D.HK (cLL ℓ (mOf ℓ s H0) U a (a + n) d)) ∧
    (∀ (U : Finset ℤ), 0 ∉ U → U.Nonempty → ∀ D : InvariantsCohomologyData ℓ,
      D.piece.Inputs (u ^ (ℓ ^ (s + n0 ℓ H0 + 1))) U 0 → D.Union → D.Flat → D.LES → D.Inv →
      ∀ x : D.M, ((ℓ : ℤ_[ℓ]) ^ c0 ℓ (mOf ℓ s H0) U) • x = 0) ∧
    (∀ (e d : ℕ) (U : Finset ℤ) (D : TBData ℓ) (L : LLData ℓ (e + 1)) (K : XiAdicFiltrationData ℓ)
      (T : Twist ℓ D.HGe) (_ : D.HYL ≃ₗ[ℤ_[ℓ]] L.HK) (_ : D.HWe ≃ₗ[ℤ_[ℓ]] K.H e), d ≠ 0 →
      (∀ k, (L.piece k).Inputs (u ^ (ℓ ^ (s + n0 ℓ H0 + 1))) U (0 + k)) → L.LES → L.T5 →
      L.CorRes (ℓ ^ (mOf ℓ s H0 - s)) → K.Inputs u e →
      T.InfRes 1 → T.T4 → T.T3 → (∀ x : D.HB, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
      (∀ x, ((ℓ : ℤ_[ℓ]) ^ (s + ceilE ℓ e)) • D.bW (D.gE (T.infm x)) ∈ D.La0) →
      D.Comm → D.LES → D.DeRham → D.tateDualityKillsH2 s e → D.Recip (beta ℓ s e) → D.Cor d →
      ((ℓ : ℤ_[ℓ]) ^ cTB ℓ s (mOf ℓ s H0) e (padicValNat ℓ d) U) • D.yK ∈ D.HfK)

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
