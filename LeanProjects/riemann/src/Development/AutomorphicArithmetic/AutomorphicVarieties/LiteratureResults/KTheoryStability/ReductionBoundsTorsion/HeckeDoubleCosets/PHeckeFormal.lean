import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.MapPartialProd

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

def PEvDC : Prop :=
  ∀ (G H Y : Type) [Group G] [Group H] [MulAction H Y] (ρ : G →* H) (m : ℕ) (E : (Fin (m + 1) → Y) → ℝ),
    Inv ρ E → ∀ (y : Y) (z : Chn G (m + 1)), ev ρ (dC E) y z = ev ρ E y (bd G m z)

def PCob : Prop :=
  ∀ (G : Type) [Group G] (m : ℕ) (F : (Fin (m + 2) → G) → ℝ), Inv (MonoidHom.id G) F →
    (∀ z : Chn G (m + 1), IsCyc z → ev (MonoidHom.id G) F 1 z = 0) →
    ∃ E : (Fin (m + 1) → G) → ℝ, Inv (MonoidHom.id G) E ∧ dC E = F

def PPrism : Prop :=
  ∀ (H Y : Type) [Group H] [MulAction H Y] (v : Y → Y), (∀ (h : H) (y : Y), v (h • y) = h • v y) →
    ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ), (∀ (h : H) (y : Fin (m + 2) → Y), F (fun j => h • y j) = F y) →
      dC F = 0 → ∃ Ψ : (Fin (m + 1) → Y) → ℝ, (∀ (h : H) (y : Fin (m + 1) → Y), Ψ (fun j => h • y j) = Ψ y) ∧
        ∀ y, dC Ψ y = F y - F (v ∘ y)

def PCobSub : Prop :=
  ∀ (Γ : Type) [Group Γ] (H : Subgroup Γ) (m : ℕ) (Φ : (Fin (m + 2) → Γ) → ℝ), Inv H.subtype Φ → dC Φ = 0 →
    (∀ w : Chn H (m + 1), IsCyc w → ev H.subtype Φ 1 w = 0) →
    ∃ Ψ : (Fin (m + 1) → Γ) → ℝ, Inv H.subtype Ψ ∧ dC Ψ = Φ

def stabR {Γ X : Type} [Group Γ] (act : X → Γ → X) (h1 : ∀ x, act x 1 = x)
    (hm : ∀ x g h, act x (g * h) = act (act x g) h) (x : X) : Subgroup Γ where
  carrier := {g | act x g = x}
  one_mem' := h1 x
  mul_mem' := fun {a b} (ha : act x a = x) (hb : act x b = x) => show act x (a * b) = x by rw [hm, ha, hb]
  inv_mem' := fun {a} (ha : act x a = x) => show act x a⁻¹ = x by
    conv_lhs => rw [← ha]
    rw [← hm, mul_inv_cancel, h1]

def PTransfer : Prop :=
  ∀ (Γ X : Type) [Group Γ] [Finite X] (act : X → Γ → X) (h1 : ∀ x, act x 1 = x)
    (hm : ∀ x g h, act x (g * h) = act (act x g) h) (m : ℕ) (Φ : X → (Fin (m + 2) → Γ) → ℝ),
    (∀ x g y, Φ (act x g) y = Φ x fun j => g * y j) → (∀ x, dC (Φ x) = 0) →
    (∀ x (w : Chn (stabR act h1 hm x) (m + 1)), IsCyc w → ev (stabR act h1 hm x).subtype (Φ x) 1 w = 0) →
    ∀ z : Chn Γ (m + 1), IsCyc z → ev (MonoidHom.id Γ) (fun y => ∑ᶠ x, Φ x y) 1 z = 0

def PFactor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (s : ℕ) (p : V →ₗ[ℝ] (Fin s → ℝ)) (T : V →ₗ[ℝ] V),
    (∀ v, p v = 0 → p (T v) = 0) → ∃ M : ℝ, 0 ≤ M ∧ ∀ v, ‖p (T v)‖ ≤ M * ‖p v‖

def PDecay : Prop :=
  ∀ (s : ℕ) (a b : ℕ → Fin s → ℝ) (ε M C : ℝ), 0 ≤ ε → 0 ≤ M → ε * (M + 1) ≤ 1 / 5 →
    (∀ r, ‖b r‖ ≤ M * ‖a r‖) → (∀ r, a (r + 1) = (1 - ε) • a r + ε • b r) →
    (∀ r, ‖a r‖ ≤ C * (3 / 5 : ℝ) ^ r) → a 0 = 0

def Gq {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) : Subgroup G :=
  (ρ.range.map (MulAut.conj q⁻¹).toMonoidHom).comap ρ

def PHeckeFormal : Prop :=
  ∀ (G K : Type) [Group G] [Group K] (ρ : G →* K) (q : K), Finite (Quotient (QuotientGroup.rightRel (Gq ρ q))) →
    ∀ (m : ℕ) (F F' : (Fin (m + 1) → K) → ℝ) (c : ℝ), Inv ρ F →
      Inv ρ (hecke ρ (MonoidHom.id K) q F) ∧
      dC (hecke ρ (MonoidHom.id K) q F) = hecke ρ (MonoidHom.id K) q (dC F) ∧
      hecke ρ (MonoidHom.id K) q (F + c • F') = hecke ρ (MonoidHom.id K) q F + c • hecke ρ (MonoidHom.id K) q F'

def PHeckeKer : Prop :=
  SEv → ∀ (G K : Type) [Group G] [Group K] (ρ : G →* K), Function.Injective ρ → ∀ q : K,
    Finite (Quotient (QuotientGroup.rightRel (Gq ρ q))) →
    ∀ (m : ℕ) (F : (Fin (m + 2) → K) → ℝ), Inv ρ F → dC F = 0 →
      (∀ z : Chn G (m + 1), IsCyc z → ev ρ F 1 z = 0) →
      ∀ z : Chn G (m + 1), IsCyc z → ev ρ (hecke ρ (MonoidHom.id K) q F) 1 z = 0

def PIndex : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (π : 𝓞 L) (hπ : Prime π),
    Finite (Quotient (QuotientGroup.rightRel (Gq (toK L N) (qel L N π hπ.ne_zero)))) ∧
      N ≤ (Gq (toK L N) (qel L N π hπ.ne_zero)).index

def PGqStab : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (π : 𝓞 L) (hπ : Prime π) (n r : ℕ), 1 ≤ n → ∀ c : Gm L n,
    stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c ∈ Gq (toK L (n + r)) (qel L (n + r) π hπ.ne_zero) ↔
      c ∈ Gq (toK L n) (qel L n π hπ.ne_zero)

def PStabK : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (π : 𝓞 L) (hπ : π ≠ 0) (n r : ℕ), 1 ≤ n →
    (∀ c : Gm L n, toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c) =
      stab L n (n + r) (Nat.le_add_right n r) (toK L n c)) ∧
    qel L (n + r) π hπ = stab L n (n + r) (Nat.le_add_right n r) (qel L n π hπ)

def PLow : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (π : 𝓞 L) (hπ : Prime π) (n r : ℕ) (hn : 1 ≤ n) (c : Gm L (n + r)),
    (∀ i : Fin r, ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n i)
      ⟨0, by omega⟩ ∈ Ideal.span {π}) →
    ∃ c' : Gm L n, c * (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c')⁻¹ ∈
      Gq (toK L (n + r)) (qel L (n + r) π hπ.ne_zero)

def PStabVan : Prop :=
  SChain → SEv → SAff → ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ,
    k + 1 < nrComplexPlaces L → ∀ (π : 𝓞 L) (hπ : Prime π) (n r : ℕ) (hn : 1 ≤ n), 1 ≤ r →
    ∀ c : Gm L (n + r), (∃ i : Fin r, ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
      (Fin.natAdd n i) ⟨0, by omega⟩ ∉ Ideal.span {π}) →
    ∀ F : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) F → dC F = 0 →
    ∀ H : Subgroup (Gm L n), (∀ h ∈ H, c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) h * c⁻¹ ∈
      Gq (toK L (n + r)) (qel L (n + r) π hπ.ne_zero)) →
    ∀ w : Chn H (k + 1), IsCyc w →
      ev H.subtype (fun y => F fun j => qel L (n + r) π hπ.ne_zero *
        toK L (n + r) (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w =
      ev H.subtype (fun y => F fun j => toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w

def PKey : Prop :=
  SChain → SEv → SAff → ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ,
    k + 1 < nrComplexPlaces L → ∀ (π : 𝓞 L) (hπ : Prime π) (n r : ℕ), 1 ≤ n → 1 ≤ r →
    ∀ F : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) F → dC F = 0 →
    ∀ z : Chn (Gm L n) (k + 1), IsCyc z →
      ev (toK L (n + r)) (hecke (toK L (n + r)) (MonoidHom.id (GK L (n + r))) (qel L (n + r) π hπ.ne_zero) F) 1
          (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z) =
        (1 - ((Gq (toK L n) (qel L n π hπ.ne_zero)).index : ℝ) /
            (Gq (toK L (n + r)) (qel L (n + r) π hπ.ne_zero)).index) *
            ev (toK L (n + r)) F 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z) +
          ((Gq (toK L n) (qel L n π hπ.ne_zero)).index : ℝ) /
              (Gq (toK L (n + r)) (qel L (n + r) π hπ.ne_zero)).index *
            ev (toK L n) (hecke (toK L n) (MonoidHom.id (GK L n)) (qel L n π hπ.ne_zero)
              (fun y => F fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))) 1 z

end PositivityTheory.KB.AffineStabilizerVanishing

end
