import Mathlib

noncomputable section

open Classical

namespace Formalism.IrreducibleCountingLemmas.TOP

def sg (f ℓ : ℕ) (h : ZMod f → ℕ) (i : ZMod f) : ℤ :=
  ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod f)) : ℝ) / (ℓ : ℝ) ^ (j + 1)⌋

def InWinN (G : Bool) (h η : ℕ) (x : ℤ) : Prop :=
  if G then 1 ≤ x ∧ x ≤ η else (h : ℤ) - η ≤ x ∧ x ≤ (h : ℤ) - 1

def ClN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (fun x => ¬ InWinN G h η x)

def GlobalTheory (w t : ℕ) : Finset ℤ := Finset.Icc (w : ℤ) ((w : ℤ) + t - 1)

def ResidueAvoidance (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ ClN G h η U, ∀ m : ℤ, -2 * σ - 2 ≤ m → m ≤ (η : ℤ) + 2 * σ + 3 →
    (((if G then x else (h : ℤ) - x) : ℤ) : ZMod ℓ) ≠ (m : ZMod ℓ)

def SgBound : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (m : ZMod f → ℤ),
    2 ≤ ℓ → (∀ i, (ℓ : ℤ) * m (i - 1) ≤ m i + h i) → ∀ i, m i ≤ sg f ℓ h i

def IneqI : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    sg f ℓ h i < (ℓ : ℤ) * (sg f ℓ h (i - 1) + 1) - h i

def SgLe : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h : ZMod f → ℕ) (H : ℕ), 2 ≤ ℓ → (∀ j, h j ≤ H) →
    ∀ i, (sg f ℓ h i : ℝ) ≤ H / ((ℓ : ℝ) - 1)

def SgRange : Prop :=
  ∀ (ℓ : ℕ) (ℓs b H : ℝ), 0 ≤ H → 1 < ℓs → ℓs < ℓ → H * ℓs ≤ 2 * b * (ℓs - 1) →
    H / ((ℓ : ℝ) - 1) ≤ 2 * b / ℓs

def LowN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (InWinN G h η)

def WindowSmall (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def WindowSeparated (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ LowN G h η U, ∀ y ∈ GlobalTheory w t, σ + 2 < |x - y|

def Slot (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  0 ≤ σ ∧ 1 ≤ t ∧ (∀ x ∈ U, 1 ≤ x ∧ x ≤ (h : ℤ) - 1) ∧ w + t ≤ h ∧
    1 ≤ w ∧ (G = true → w + t - 1 ≤ η) ∧ (G = false → (h : ℤ) - η ≤ w) ∧
    WindowSmall ℓ η σ ∧ WindowSeparated G h η w t σ U ∧ ResidueAvoidance ℓ G h η σ U

def Residues : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ G h η w t σ U →
    (∀ x ∈ U, ∀ e : ℤ, -σ - 1 ≤ e → e ≤ (t : ℤ) + σ →
      ((x : ℤ) : ZMod ℓ) ≠ (((w : ℤ) + e : ℤ) : ZMod ℓ)) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ GlobalTheory w t) → ∀ a : ℤ, 0 ≤ a → a ≤ (h : ℤ) - w →
      ((u - w - a : ℤ) : ZMod ℓ) = 0 → u - w - a = 0) ∧
    (G = true → ∀ x ∈ U, ∀ e : ℤ, 1 ≤ e → e ≤ σ → ((x + e : ℤ) : ZMod ℓ) ≠ 0) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ GlobalTheory w t) → ∀ e : ℤ, 1 ≤ e → e ≤ σ + 1 →
      ((u : ℤ) : ZMod ℓ) ≠ (((h : ℤ) + e : ℤ) : ZMod ℓ))

def resCount (ℓ : ℕ) (U : Multiset ℤ) (x : ZMod ℓ) : ℕ := U.countP (fun u => ((u : ℤ) : ZMod ℓ) = x)

def CountG : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ true h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.range w, S (n : ZMod ℓ) = U.countP (fun u => u < (w : ℤ))

def CountBd : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ false h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      (∀ x, S x ≠ 0 → ∃ u : ℤ, (u ∈ U ∨ u ∈ GlobalTheory w t) ∧ x = ((u : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.Icc (w : ℤ) (h : ℤ), S ((n : ℤ) : ZMod ℓ) =
        Multiset.card U - U.countP (fun u => u < (w : ℤ))

def KerCount : Prop :=
  ∀ (ℓ w : ℕ) (S : Multiset (ZMod ℓ)), 1 ≤ w → w < ℓ →
    Multiset.card ((S ×ˢ (Finset.Icc 1 w).val).filter
        (fun p : ZMod ℓ × ℕ => p.1 - (w : ZMod ℓ) + (p.2 : ZMod ℓ) = 0)) =
      S.countP (fun s => ∃ n < w, s = (n : ZMod ℓ))

def KerCountBd : Prop :=
  ∀ (ℓ w h : ℕ) (S : Multiset (ZMod ℓ)), w ≤ h → h - w < ℓ →
    Multiset.card ((S ×ˢ (Finset.range (h - w + 1)).val).filter
        (fun p : ZMod ℓ × ℕ => p.1 - (w : ZMod ℓ) - (p.2 : ZMod ℓ) = 0)) =
      S.countP (fun s => ∃ n, w ≤ n ∧ n ≤ h ∧ s = (n : ZMod ℓ))

def KerGr : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (m : ℕ) (F : ℕ → Submodule k V),
    F 0 = ⊥ → F m = ⊤ → (∀ i, F i ≤ F (i + 1)) → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
    Module.finrank k (LinearMap.ker f) ≤
      ∑ i ∈ Finset.range m,
        (Module.finrank k ↥(F (i + 1) ⊓ (F i).comap f) - Module.finrank k ↥(F i))

def KerEig : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (g : V →ₗ[k] V),
    Module.finrank k (LinearMap.ker g) ≤ (LinearMap.charpoly g).rootMultiplicity 0

def KerEqMult : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (g : V →ₗ[k] V),
    (∀ x, (∃ n : ℕ, (g ^ n) x = 0) → g x = 0) →
    Module.finrank k (LinearMap.ker g) = (LinearMap.charpoly g).rootMultiplicity 0

def GenKerGr : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (m : ℕ) (F : ℕ → Submodule k V),
    F 0 = ⊥ → F m = ⊤ → (∀ i, F i ≤ F (i + 1)) → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
    (LinearMap.charpoly f).rootMultiplicity 0 =
      ∑ i ∈ Finset.range m,
        (Module.finrank k ↥(F (i + 1) ⊓ ⨆ n : ℕ, (F i).comap (f ^ n)) - Module.finrank k ↥(F i))

def Close : Prop :=
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (KK L N : Submodule k V) (r d : ℕ),
      L ≤ KK ⊓ N → Module.finrank k KK - Module.finrank k L ≤ r →
      Module.finrank k ↥(KK ⊓ N) - Module.finrank k L = r - d → d ≤ r →
      Module.finrank k KK - Module.finrank k ↥(KK ⊓ N) ≤ d) ∧
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Hf adm : Submodule k V), Hf ≤ adm → Module.finrank k adm ≤ Module.finrank k Hf →
      adm = Hf)

def DepthSteps : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h w : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    sg f ℓ h i + 2 * ℓ < (ℓ : ℤ) * (sg f ℓ h (i - 1) + 3) - h i ∧
    (w i ≤ h i → ((h i : ℤ) - w i) + 2 < (ℓ : ℤ) * (sg f ℓ h (i - 1) + 3) - w i) ∧
    ∀ s : ℕ, sg f ℓ h i + 1 + ℓ * s ≤ (ℓ : ℤ) * (sg f ℓ h (i - 1) + 1 + s) - h i

def PsiPow : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime)
    (ψ : PowerSeries k →+ PowerSeries k),
    (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) →
    (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0) →
    (∀ j < ℓ, ψ (PowerSeries.X ^ j) = (-1) ^ j) ∧
    ∀ s : ℕ, ψ '' {x | PowerSeries.X ^ s ∣ x} = {y | PowerSeries.X ^ (s / ℓ) ∣ y}

def PsiExists : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime),
    ∃ ψ : PowerSeries k →+ PowerSeries k,
      (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) ∧
      (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0)

def KerCoker : Prop :=
  ∀ (k V W : Type) [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k V] [FiniteDimensional k W] (g : V →ₗ[k] W),
    Module.finrank k V = Module.finrank k W →
    Module.finrank k ↥(LinearMap.ker g) = Module.finrank k (W ⧸ LinearMap.range g)

def LemmaE : Prop :=
  ∀ (O M : Type) [CommRing O] [IsLocalRing O] [AddCommGroup M] [Module O M]
    (f : M →ₗ[O] M) (S : Finset O),
    (∀ c ∈ S, c ∈ IsLocalRing.maximalIdeal O → c = 0) →
    Polynomial.aeval f (∏ c ∈ S, (Polynomial.X - Polynomial.C c)) = 0 →
    ∀ P Q : Submodule O M, P ≤ Q →
      (∀ x ∈ P, f x ∈ P) → (∀ x ∈ Q, f x ∈ Q) →
      ∀ x ∈ Q, (∃ n : ℕ, (f ^ n) x ∈ P) → f x ∈ P

def TriDiag : Prop :=
  ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) (m : ℕ)
    (F : ℕ → Submodule R M) (c : ℕ → R) (S : Finset R),
    F 0 = ⊥ → (∀ i < m, ∀ x ∈ F (i + 1), f x - c i • x ∈ F i) →
    (∀ i < m, ∀ j < m, c i = c j → i = j) → (∀ i < m, c i ∈ S) →
    ∀ x ∈ F m, Polynomial.aeval f (∏ a ∈ S, (Polynomial.X - Polynomial.C a)) x = 0

def CaVal : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ a b : ℕ, b < a →
    padicValInt ℓ ((1 + (ℓ : ℤ)) ^ a - (1 + (ℓ : ℤ)) ^ b) = 1 + padicValNat ℓ (a - b) ∧
    ((((1 + (ℓ : ℤ)) ^ a - 1) / ℓ : ℤ) : ZMod ℓ) = (a : ZMod ℓ)

def CaValZ : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ a b : ℤ, a ≠ b →
    padicValRat ℓ ((1 + (ℓ : ℚ)) ^ a - (1 + (ℓ : ℚ)) ^ b) = 1 + (padicValInt ℓ (a - b) : ℤ)

def PoleOrder : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ), 1 ≤ ℓ → ∀ u : PowerSeries k, PowerSeries.constantCoeff u ≠ 0 →
    ∀ g : PowerSeries k,
      PowerSeries.order (PowerSeries.subst (u * PowerSeries.X ^ ℓ) g : PowerSeries k) =
        (ℓ : ℕ∞) * PowerSeries.order g

def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)

def LemmaChar : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ t M : ℕ) (h w η σ : ZMod f → ℕ) (G : ZMod f → Bool)
    (k : ℕ → ℕ → ZMod f → ℤ),
    1 ≤ t → 1 ≤ M →
    (∀ i, G i = true → 1 ≤ w i ∧ w i + t - 1 ≤ η i) →
    (∀ i, G i = false → (h i : ℤ) - η i ≤ w i ∧ w i + t ≤ h i) →
    (∀ i, η i + 4 * σ i + 6 < ℓ) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → |k c μ i| ≤ σ i) →
    (∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M →
      0 ≤ (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ∧
      (w i : ℤ) + c - 1 + (ℓ : ℤ) * k c μ (i - 1) - k c μ i ≤ h i) →
    (∀ i, (Finset.Icc 1 t ×ˢ Finset.Icc 1 M).val.map
        (fun cμ : ℕ × ℕ => (((w i : ℤ) + cμ.1 - 1 - k cμ.1 cμ.2 i : ℤ) : ZMod ℓ)) =
      M • (Finset.Icc 1 t).val.map (fun c : ℕ => (((w i : ℤ) + c - 1 : ℤ) : ZMod ℓ))) →
    ∀ c μ i, c ∈ Finset.Icc 1 t → μ ∈ Finset.Icc 1 M → k c μ i = 0

def AdmissibleTensorEq : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (H : Type) [AddCommGroup H] [Module O H]
    (Hf : Submodule O H)
    (adm : ∀ (X : Type) [AddCommGroup X] [Module O X], Submodule O (TensorProduct O H X)),
    (∀ (X Y : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y],
      IsFiniteLength O X → IsFiniteLength O Y → ∀ g : X →ₗ[O] Y,
        (adm X).map (g.lTensor H) ≤ adm Y) →
    (∀ (X : Type) [AddCommGroup X] [Module O X], IsFiniteLength O X →
      LinearMap.range (Hf.subtype.rTensor X) ≤ adm X) →
    (∀ (X : Type) [AddCommGroup X] [Module O X] (X₁ : Submodule O X), IsFiniteLength O X →
      (adm X).comap (X₁.subtype.lTensor H) = adm X₁) →
    adm (IsLocalRing.ResidueField O) = LinearMap.range (Hf.subtype.rTensor _) →
    ∀ (X : Type) [AddCommGroup X] [Module O X], IsFiniteLength O X →
      adm X = LinearMap.range (Hf.subtype.rTensor X)

def Ord {k : Type} [Field k] (j : ℤ) (x : LaurentSeries k) : Prop := ∀ i < j, x.coeff i = 0

def vv (k : Type) [Field k] : LaurentSeries k := HahnSeries.single 1 1

def IsUnitR {k : Type} [Field k] (x : LaurentSeries k) : Prop := Ord 0 x ∧ x.coeff 0 ≠ 0

structure FrobeniusGammaData (k : Type) [Field k] (ℓ : ℕ) where
  φ : LaurentSeries k →ₐ[k] LaurentSeries k
  γ : LaurentSeries k →ₐ[k] LaurentSeries k
  ψ : LaurentSeries k →+ LaurentSeries k
  u : LaurentSeries k
  c : LaurentSeries k
  c₀ : k
  hu : IsUnitR u
  φ_v : φ (vv k) = u * vv k ^ ℓ
  φ_ord : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x → Ord (ℓ * j) (φ x)
  hc : IsUnitR c
  γ_v : γ (vv k) = vv k + c * vv k ^ 2
  γ_bij : Function.Bijective γ
  γ_φ : ∀ x, γ (φ x) = φ (γ x)
  hc₀ : c₀ ≠ 0
  γ_lead : ∀ (j : ℤ) (x : LaurentSeries k), Ord j x →
    Ord (j + 1) (γ x - x) ∧ Ord (j + 2) (γ x - x - ((j : k) * c₀) • (vv k * x))
  ψ_φ : ∀ a x, ψ (φ a * x) = a * ψ x
  ψ_one : ψ 1 = 1
  ψ_γ : ∀ x, ψ (γ x) = γ (ψ x)

def LemmaPSI : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ], ℓ.Prime → 5 ≤ ℓ →
    ∀ (P : FrobeniusGammaData k ℓ),
    (∀ a : ℤ, 2 - (ℓ : ℤ) ≤ a → a ≤ 1 → P.ψ '' {x | Ord a x} = {x | Ord 0 x}) →
    ∀ (n : ℕ) (g : Fin n → Fin n → LaurentSeries k),
    (∀ i j, Ord 1 (g i j - if i = j then 1 else 0)) →
    ∀ a : ℤ, 2 - (ℓ : ℤ) ≤ a → a ≤ 0 →
    let Γ : (Fin n → LaurentSeries k) → (Fin n → LaurentSeries k) :=
      fun x m => ∑ j, P.γ (x j) * P.φ (g j m)
    let X : ℤ → Set (Fin n → LaurentSeries k) := fun b => {x | ∀ j, Ord b (x j) ∧ P.ψ (x j) = 0}
    (∀ x ∈ X a, Γ x - x ∈ X (a + 1)) ∧ (∀ x ∈ X a, Γ x = x → x = 0) ∧
      (∀ y ∈ X (a + 1), ∃ x ∈ X a, Γ x - x = y)

def PsiApplic : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ false h η w t σ U →
    2 - (ℓ : ℤ) ≤ -((h : ℤ) - w) ∧ -((h : ℤ) - w) ≤ 0

def PsiPowZ : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime)
    (φ : LaurentSeries k →+* LaurentSeries k) (ψ : LaurentSeries k →+ LaurentSeries k),
    (∀ a : PowerSeries k, φ (a : LaurentSeries k) =
      ((PowerSeries.expand ℓ hℓ.ne_zero a : PowerSeries k) : LaurentSeries k)) →
    (∀ a x : LaurentSeries k, ψ (φ a * x) = a * ψ x) →
    (∀ j < ℓ, ψ ((1 + vv k) ^ j) = if j = 0 then 1 else 0) →
    ∀ s : ℤ, ψ '' {x | Ord s x} = {y | Ord (s / (ℓ : ℤ)) y}

def PsiExistsZ : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime),
    ∃ (φ : LaurentSeries k →+* LaurentSeries k) (ψ : LaurentSeries k →+ LaurentSeries k),
    (∀ a : PowerSeries k, φ (a : LaurentSeries k) =
      ((PowerSeries.expand ℓ hℓ.ne_zero a : PowerSeries k) : LaurentSeries k)) ∧
    (∀ a x : LaurentSeries k, ψ (φ a * x) = a * ψ x) ∧
    (∀ j < ℓ, ψ ((1 + vv k) ^ j) = if j = 0 then 1 else 0)

def NuLow : Prop :=
  ∀ (ℓ a : ℤ), 2 ≤ ℓ → 2 - ℓ ≤ a → a ≤ 1 →
    -(ℓ - 2) ≤ a * (ℓ - 1) / ℓ ∧ a * (ℓ - 1) / ℓ ≤ 0 ∧
    ∀ n : ℤ, (ℓ - 1) ∣ n → (a * (ℓ - 1) / ℓ ≤ n ↔ 0 ≤ n)

def PsiAverage : Prop :=
  ∀ (k E D : Type) [Field k] [AddCommGroup E] [Module k E] [Group D] [Fintype D]
    [DistribMulAction D E] [SMulCommClass D k E] (ψ : E →+ E) (S T : Submodule k E),
    ((Fintype.card D : ℕ) : k) ≠ 0 → (∀ (d : D) (x : E), ψ (d • x) = d • ψ x) →
    (∀ d : D, ∀ x ∈ S, d • x ∈ S) → ψ '' (S : Set E) = (T : Set E) →
    ψ '' {x | x ∈ S ∧ ∀ d : D, d • x = x} = {y | y ∈ T ∧ ∀ d : D, d • y = y}

def Sec4Res : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (e j : ℤ), η < ℓ → 0 ≤ e → e ≤ (t : ℤ) - 1 → 1 ≤ j →
    (G = true → w + t - 1 ≤ η ∧ j ≤ w) →
    (G = false → h - w ≤ η ∧ w ≤ h ∧ j ≤ (h : ℤ) - w - e) →
    ((e + j : ℤ) : ZMod ℓ) ≠ 0

def DistinctChars : Prop :=
  ∀ (F : Type) [Field F] (ℓ t : ℕ) (x : F), orderOf x = ℓ - 1 → t + 1 < ℓ →
    ∏ c ∈ Finset.Icc 2 t, (1 - x ^ (c - 1)) ≠ 0

def EtaRange : Prop :=
  ∀ (t η c₀ : ℕ) (Z : Finset ℤ) (μm μp : ℤ), t = 2 * c₀ + 1 → (∀ z ∈ Z, |z| ≤ (η : ℤ) + c₀) →
    μm ∈ insert (-(c₀ : ℤ)) Z → μp ∈ insert (c₀ : ℤ) Z → μp - μm + 1 ≤ 2 * (η : ℤ) + t

def WindowSmallOfBounds : Prop :=
  ∀ (ℓ ηi η t : ℕ) (ℓs σ b : ℝ), (ηi : ℝ) ≤ 2 * η + t + 1 → σ ≤ 2 * b / ℓs →
    2 * (η : ℝ) + t + 8 * b / ℓs + 7 < ℓs → ℓs < ℓ → (ηi : ℝ) + 4 * σ + 6 < ℓ

def SeparationOfBounds : Prop :=
  ∀ (t : ℕ) (σ B h₀ c y z : ℝ), 0 ≤ B → σ ≤ 2 * B → 12 * B + 2 * t + 6 ≤ h₀ →
    |y - c| ≤ ((t : ℝ) - 1) / 2 → h₀ / 2 ≤ |z - c| → σ + 2 < |z - y|

def SeparationOfBoundsAlt : Prop :=
  ∀ (t : ℕ) (σ B c y z : ℝ), σ ≤ 2 * B → |y - c| ≤ ((t : ℝ) - 1) / 2 →
    2 * B + t / 2 + 3 ≤ |z - c| → σ + 2 < |z - y|

def ResidueAvoidanceOfSmall : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ : ℤ) (U : Multiset ℤ), 0 ≤ σ →
    (∀ x ∈ U, 0 ≤ x ∧ x ≤ h) → (h : ℤ) + 2 * σ + 2 < ℓ →
    (∀ x ∈ ClN G h η U, (η : ℤ) + 2 * σ + 3 < (if G then x else (h : ℤ) - x)) →
    ResidueAvoidance ℓ G h η σ U

def AvoidanceSizeBound : Prop :=
  ∀ (ηi η t : ℕ) (σ size : ℤ) (B w₂ : ℝ), ηi ≤ 2 * η + t + 1 → (σ : ℝ) ≤ 2 * B →
    2 * (η : ℝ) + t + 4 * B + 4 < w₂ → w₂ ≤ size → (ηi : ℤ) + 2 * σ + 3 < size

def ResidueAvoidanceOfPrimes : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η : ℕ) (σ sp : ℤ) (U : Multiset ℤ) (Sz : Finset ℤ),
    (∀ x ∈ ClN G h η U, ∃ W ∈ Sz, 0 ≤ (if G then x else (h : ℤ) - x) - W ∧
      (if G then x else (h : ℤ) - x) - W ≤ sp) →
    (∀ W ∈ Sz, ∀ j ∈ Finset.Icc (-2 * σ - 2 - sp) ((η : ℤ) + 2 * σ + 3), W - j ≠ 0) →
    (¬ ∃ W ∈ Sz, ∃ j ∈ Finset.Icc (-2 * σ - 2 - sp) ((η : ℤ) + 2 * σ + 3),
      W - j ≠ 0 ∧ (ℓ : ℤ) ∣ W - j) →
    ResidueAvoidance ℓ G h η σ U

def LamCount : Prop :=
  ∀ (ηi η t S : ℕ) (σ : ℤ) (B : ℝ), 0 ≤ σ → ηi ≤ 2 * η + t + 1 → (σ : ℝ) ≤ 2 * B →
    ((Finset.Icc (-2 * σ - 2 - ((S : ℤ) + η + 1)) ((ηi : ℤ) + 2 * σ + 3)).card : ℝ) ≤
      S + 3 * η + t + 8 * B + 8

def OnePrimeFactor : Prop :=
  ∀ (n : ℤ) (L p q : ℕ), n ≠ 0 → |n| ≤ (L : ℤ) ^ 2 → p.Prime → q.Prime → L < p → L < q →
    (p : ℤ) ∣ n → (q : ℤ) ∣ n → p = q

def ExcCount : Prop :=
  ∀ (L : ℕ) (Sz J : Finset ℤ), (∀ W ∈ Sz, ∀ j ∈ J, |W - j| ≤ (L : ℤ) ^ 2) →
    ∀ E : Finset ℕ, (∀ p ∈ E, p.Prime ∧ L < p ∧ ∃ W ∈ Sz, ∃ j ∈ J, W - j ≠ 0 ∧ (p : ℤ) ∣ W - j) →
      E.card ≤ Sz.card * J.card

end Formalism.IrreducibleCountingLemmas.TOP
