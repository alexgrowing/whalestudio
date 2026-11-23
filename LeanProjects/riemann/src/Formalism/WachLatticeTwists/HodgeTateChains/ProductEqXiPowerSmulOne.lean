import Formalism.WachLatticeTwists.HodgeTateChains.UnitCongruenceGivesPerturbation

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

structure HypW' (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ) where

  Xx : Matrix (Fin r) (Fin r) WC

  Xi : Matrix (Fin r) (Fin r) WC
  inv1 : Xx * Xi = 1
  inv2 : Xi * Xx = 1

  fixH : ∀ h ∈ H,
    Xx.map (act h) * ((ρ (inc h) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC)) = Xx

  P : Matrix (Fin r) (Fin r) WC
  W1 : Xx.map φ = P * Xx

  P1 : Matrix (Fin r) (Fin r) As
  map_eq_xi_power_smul : (P1.map jA).map ι = (ι (jA ξ)) ^ M0 • P

  Q1 : Matrix (Fin r) (Fin r) As
  product_eq_xi_power_smul_one : P1 * Q1 = (ξ ^ (M0 + h0)) • (1 : Matrix (Fin r) (Fin r) As)

  Gm : Gg → Matrix (Fin r) (Fin r) As
  W2 : ∀ g, Xx.map (act g) * ((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC))
    = ((Gm g).map jA).map ι * Xx

  W3 : ∀ g i j, (Gm g - 1) i j ∈ Ideal.span {(ℓ : As), πs}

  W4 : ∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ],
    (∀ g : GK, E * (ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = ρ g * E) →
    ∃ E' : Matrix (Fin r) (Fin r) As, Xx * Eᵀ.map (algebraMap ℤ_[ℓ] WC) = (E'.map jA).map ι * Xx

def StatHypWComm : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (r : ℕ) (ρ : Gg →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ),
    HypW ℓ As AA WC jA ι φ Gg H act r ρ πs ξ M0 h0 →
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Function.Injective (algebraMap ℤ_[ℓ] WC) →
    ∀ h ∈ H, ∀ h' ∈ H, ρ h * ρ h' = ρ h' * ρ h

def StatWSandwich' : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC) (c : OC),
    LemmaAProp ι φ r → Function.Injective ι → φ (ι (jA x)) = ι (jA x * jA ξ) →
    (∀ a : WC, ι (jA ξ) * a = 0 → a = 0) →
    (ϑ (jA x)) ^ (ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)) * c = (ℓ : OC) →
    ∃ (A : Matrix (Fin r) (Fin r) AA) (Y' : Matrix (Fin r) (Fin r) OC),
      A.map ι = (ι (jA x)) ^ M0 • W.Xx ∧
      A.map ϑ * Y' = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC) ∧
      Y' * A.map ϑ = (ℓ : OC) • (1 : Matrix (Fin r) (Fin r) OC)

def StatWFix : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0),
    Function.Injective (fun a : As => ι (jA a)) → ∀ h ∈ H, W.Gm h = 1

def StatWCocycle : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0),
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    ((W.Gm 1).map jA).map ι = 1 ∧
    ∀ g g', ((W.Gm (g * g')).map jA).map ι
      = (((W.Gm g').map jA).map ι).map (act g) * ((W.Gm g).map jA).map ι

def StatWGam : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (γ : Gg) (σ : As →+* As),
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Function.Injective (fun a : As => ι (jA a)) → (∀ a, act γ (ι (jA a)) = ι (jA (σ a))) →
    ∀ (k : ℕ) (i : Fin r), (⇑(gamN σ (W.Gm γ)))^[k] (Pi.single i 1) = W.Gm (γ ^ k) i

def StatWUm : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC R : Type) [CommRing As] [CommRing AA] [CommRing WC] [CommRing R]
    [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (γ : Gg) (σ : As →+* As)
    (ϑ : As →+* R) (z ϖ ϖ' : R) (s n : ℕ),
    (∀ g (c : ℤ_[ℓ]), act g (algebraMap ℤ_[ℓ] WC c) = algebraMap ℤ_[ℓ] WC c) →
    Function.Injective (fun a : As => ι (jA a)) → (∀ a, act γ (ι (jA a)) = ι (jA (σ a))) →
    (∀ a, σ a - a ∈ Ideal.span {(ℓ : As), πs}) →
    (∀ a ∈ Ideal.span {(ℓ : As), πs}, σ a - a ∈ (Ideal.span {(ℓ : As), πs}) ^ 2) →
    ϑ πs = ϖ' → ϖ' ∣ (ℓ : R) → z ∣ (ℓ : R) → ϖ ∣ (ℓ : R) → z * ϖ ∣ ϖ' ^ (ℓ ^ (s + n)) →
    ∀ i j, z * ϖ ∣ ϑ ((W.Gm (γ ^ (ℓ ^ (s + n + 1))) - 1) i j)

def StatWEnd : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (As AA WC OC : Type) [CommRing As] [CommRing AA] [CommRing WC]
    [CommRing OC] [Algebra ℤ_[ℓ] AA] [Algebra ℤ_[ℓ] WC] (jA : As →+* AA) (ι : AA →+* WC) (φ : WC →+* WC)
    (Gg : Type) [Group Gg] (H : Subgroup Gg) (act : Gg →* (WC ≃+* WC))
    (GK : Type) [Group GK] (inc : Gg →* GK)
    (r : ℕ) (ρ : GK →* (Matrix (Fin r) (Fin r) ℤ_[ℓ])ˣ) (πs ξ x : As) (M0 h0 : ℕ)
    (W : HypW' ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0) (ϑ : AA →+* OC)
    (A : Matrix (Fin r) (Fin r) AA),
    Function.Injective ι → (∀ c : ℤ_[ℓ], ι (algebraMap ℤ_[ℓ] AA c) = algebraMap ℤ_[ℓ] WC c) →
    A.map ι = (ι (jA x)) ^ M0 • W.Xx →
    ∀ E : Matrix (Fin r) (Fin r) ℤ_[ℓ],
      (∀ g : GK, E * (ρ g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = ρ g * E) →
      ∃ E' : Matrix (Fin r) (Fin r) As,
        A.map ϑ * (Eᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ = (E'.map jA).map ϑ * A.map ϑ

def StatFreeGm' : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (a : ℤ) (D : FreeData ℓ), D.Inputs →
    (∀ i, (D.piece i).Inputs w U (a + i)) →
    (∀ i, ∀ a0 : (D.piece i).Wm, (D.piece i).gm a0 = a0 →
      ∃ z : D.H0 i (i + 1), ((ℓ : ℤ_[ℓ]) ^ m) • (D.piece i).io ((D.piece i).infm a0) = D.cup i (i + 1) z) →
    (∀ i k j, i < k → k < j → Function.Exact (D.dl i k j) (D.i1 i k j)) →
    ∀ i j, i < j → FreeIn ℓ (D.cup i j)
      (∑ x ∈ Finset.Ico i j, (rI ℓ m U (a + x) + m + 2) +
        (∑ x ∈ Finset.Ico i j, (2 + max 1 (rI ℓ m U (a + x)))) * Nat.clog 2 (j - i))

def StatFreeKTop : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (InvariantsKilledOverCyclotomic H1K H1m H0m H0KQ H1KQ H0mQ H1mQ : Type)
    [AddCommGroup InvariantsKilledOverCyclotomic] [Module ℤ_[ℓ] InvariantsKilledOverCyclotomic]
    [AddCommGroup H1K] [Module ℤ_[ℓ] H1K] [AddCommGroup H1m] [Module ℤ_[ℓ] H1m]
    [AddCommGroup H0m] [Module ℤ_[ℓ] H0m] [AddCommGroup H0KQ] [Module ℤ_[ℓ] H0KQ]
    [AddCommGroup H1KQ] [Module ℤ_[ℓ] H1KQ]
    [AddCommGroup H0mQ] [Module ℤ_[ℓ] H0mQ] [AddCommGroup H1mQ] [Module ℤ_[ℓ] H1mQ]
    (cupK : InvariantsKilledOverCyclotomic →ₗ[ℤ_[ℓ]] H1K) (b0 : InvariantsKilledOverCyclotomic →ₗ[ℤ_[ℓ]] H0KQ) (b1 : H1K →ₗ[ℤ_[ℓ]] H1KQ)
    (cupKQ : H0KQ →ₗ[ℤ_[ℓ]] H1KQ) (resQ : H1KQ →ₗ[ℤ_[ℓ]] H1mQ)
    (res : H1K →ₗ[ℤ_[ℓ]] H1m) (cup : H0m →ₗ[ℤ_[ℓ]] H1m) (a0 : H0m →ₗ[ℤ_[ℓ]] H0mQ)
    (a1 : H1m →ₗ[ℤ_[ℓ]] H1mQ) (r0 : H0KQ →ₗ[ℤ_[ℓ]] H0mQ) (cupQ : H0mQ →ₗ[ℤ_[ℓ]] H1mQ) (al : ℕ),
    (∀ z, a1 (cup z) = cupQ (a0 z)) → (∀ z, b1 (cupK z) = cupKQ (b0 z)) →
    (∀ y, a1 (res y) = resQ (b1 y)) → (∀ z, resQ (cupKQ z) = cupQ (r0 z)) →
    Function.Injective cupQ → Function.Surjective cupKQ →
    (∀ x : H1mQ, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    (∀ y : H1K, b1 y = 0 → ∃ t : ℕ, ((ℓ : ℤ_[ℓ]) ^ t) • y = 0) →
    (∀ (z : H0KQ) (zm : H0m), a0 zm = r0 z → ∃ zK : InvariantsKilledOverCyclotomic, b0 zK = z) →
    FreeIn ℓ cup al → FreeIn ℓ cupK al

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
