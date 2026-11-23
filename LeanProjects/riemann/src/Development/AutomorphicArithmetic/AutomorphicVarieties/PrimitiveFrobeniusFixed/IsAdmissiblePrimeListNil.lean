import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick
open scoped nonZeroDivisors

namespace UpperTheory.V.ML

def th (M b : ℕ) (t : ZMod M) : ℤ := ((t.val * b / M : ℕ) : ℤ) - (((-t).val * b / M : ℕ) : ℤ)

theorem th_neg (M b : ℕ) (t : ZMod M) : th M b (-t) = -th M b t := by simp [th]

def IsX (M : ℕ) [NeZero M] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {M} ℚ K] (b : ℕ)
    (𝔞 : Ideal (𝓞 K)) (X : K) : Prop :=
  X * sg M K (-1) X = 1 ∧ FractionalIdeal.spanSingleton (𝓞 K)⁰ X =
    ∏ t : (ZMod M)ˣ, ((conjI M K 𝔞 t : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ th M b t

def AdmP (l F r q : ℕ) : Prop := q.Prime ∧ q ≡ 1 [MOD F] ∧ q ≠ r ∧ ¬ l ∣ orderOf (r : ZMod q)

def admitted (l F r d : ℕ) : Prop := Squarefree d ∧ ∀ q : ℕ, q.Prime → q ∣ d → AdmP l F r q

def AdmL (l F r : ℕ) (L : List ℕ) : Prop := L.Nodup ∧ ∀ q ∈ L, AdmP l F r q

theorem isAdmissiblePrimeList_nil (l F r : ℕ) : AdmL l F r [] := ⟨List.nodup_nil, by simp⟩

section Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def Pows (N k : ℕ) (g : G ℚ Ω) : Prop := ∀ x : Ω, x ^ N = 1 → g x = x ^ k

abbrev Lifts (N : ℕ) (b : (ZMod N)ˣ) (g : G ℚ Ω) : Prop := Pows N (b : ZMod N).val g

abbrev Over (A : ValuationSubring Ω) (n : ℕ) : Prop := A.valuation (n : Ω) < 1

def GenAt (q : ℕ) (τ : G ℚ Ω) : Prop := ∃ b : (ZMod q)ˣ, (∀ x, x ∈ Subgroup.zpowers b) ∧ Lifts q b τ

def IsTau (q : ℕ) (τ : G ℚ Ω) : Prop := (∀ k : ℕ, k.Coprime q → τ ∈ fixMu ℚ Ω k) ∧ GenAt q τ

def nrm (q : ℕ) (τ : G ℚ Ω) (u : Ω) : Ω := ∏ i ∈ Finset.range (q - 1), (τ ^ i) u

def der1 (q : ℕ) (τ : G ℚ Ω) (u : Ω) : Ω := ∏ i ∈ Finset.range (q - 1), (τ ^ i) u ^ i

def der (τ : ℕ → G ℚ Ω) : List ℕ → Ω → Ω
  | [], u => u
  | q :: L, u => der1 q (τ q) (der τ L u)

def opP (δ : G ℚ Ω) (a : ℕ) (u : Ω) : Ω := δ u / u ^ a

structure Lax (l F r : ℕ) (X : ℕ → Ω) (s : ℕ → ℕ → ℕ) : Prop where
  ne : ∀ d, admitted l F r d → X d ≠ 0
  fix : ∀ d, admitted l F r d → ∀ g ∈ fixMu ℚ Ω (F * d), g (X d) = X d
  unit : ∀ d, admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (X d) = 1
  cop : ∀ d q, q.Prime → admitted l F r (q * d) → ¬ l ∣ s d q
  norm : ∀ d q, q.Prime → admitted l F r (q * d) → ∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
    ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧ nrm q τ (X (q * d)) = ζ * (X d / φ⁻¹ (X d)) ^ s d q
  cong : ∀ d q, q.Prime → admitted l F r (q * d) → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
    ∃ ζ : Ω, ζ ^ (2 * F * (q * d)) = 1 ∧
      ∀ A : ValuationSubring Ω, Over A q → A.valuation (X (q * d) - ζ * φ⁻¹ (X d) ^ s d q) < 1

structure Sys (l F r : ℕ) (x : ℕ → Ω) (s : ℕ → ℕ → ℕ) : Prop where
  ne : ∀ d, admitted l F r d → x d ≠ 0
  fix : ∀ d, admitted l F r d → ∀ g ∈ fixMu ℚ Ω (F * d), g (x d) = x d
  unit : ∀ d, admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (x d) = 1
  cop : ∀ d q, q.Prime → admitted l F r (q * d) → ¬ l ∣ s d q
  norm : ∀ d q, q.Prime → admitted l F r (q * d) → ∀ τ ∈ fixMu ℚ Ω (F * d), GenAt q τ → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
    nrm q τ (x (q * d)) = (x d / φ⁻¹ (x d)) ^ s d q
  cong : ∀ d q, q.Prime → admitted l F r (q * d) → ∀ φ : G ℚ Ω, Pows (F * d) q φ →
    ∀ A : ValuationSubring Ω, Over A q → A.valuation (x (q * d) - φ⁻¹ (x d) ^ s d q) < 1

def HasOrd (F r : ℕ) (A₀ : ValuationSubring Ω) (u : Ω) (k : (ZMod F)ˣ → ℤ) : Prop :=
  ∀ (t : (ZMod F)ˣ) (σ : G ℚ Ω), Lifts F t σ → A₀.valuation (σ u) = A₀.valuation (r : Ω) ^ k t

def IsKol (M F n : ℕ) (ζ : Ω) (δ : G ℚ Ω) (a : ℕ) (y : Ω) (κ : G ℚ Ω → ZMod M) : Prop :=
  ∃ Y : Ω, Y ^ M = y ∧ ∀ g ∈ fixMu ℚ Ω F, ∃ z : Ω, (∀ h ∈ fixMu ℚ Ω (F * n), h z = z) ∧ z ^ M = g y / y ∧
    ζ ^ (κ g).val = g (opP δ a Y) / opP δ a Y / opP δ a z

variable {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]

def nu {M F : ℕ} [NeZero F] (β : G ℚ Ω →* Oˣ) (σ : (ZMod F)ˣ → G ℚ Ω) (w : W) (κ : G ℚ Ω → ZMod M) (u : G ℚ Ω) : W :=
  ∑ t : (ZMod F)ˣ, (κ ((σ t)⁻¹ * u * σ t)).val • ((β (σ t) : O) • w)

structure IsNu (M F n : ℕ) (β : G ℚ Ω →* Oˣ) (ν : G ℚ Ω → W) : Prop where
  add : ∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, ν (u * v) = ν u + ν v
  lc : IsLocallyConstant fun u : fixMu ℚ Ω F => ν u
  eqv : ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, ν (g * u * g⁻¹) = (β g : O) • ν u
  tors : ∀ u ∈ fixMu ℚ Ω F, M • ν u = 0
  unr : ∀ A : ValuationSubring Ω, ¬ Over A n → ∀ g ∈ Ine (F := ℚ) A, ν g = 0

structure NuSys (l M F r : ℕ) (β : G ℚ Ω →* Oˣ) (A₀ : ValuationSubring Ω) (w₁ : W) (ν : List ℕ → G ℚ Ω → W) : Prop where
  isNu : ∀ L, AdmL l F r L → IsNu M F (F * r * L.prod) β (ν L)
  step : ∀ q L, AdmL l F r (q :: L) → ∀ A : ValuationSubring Ω, Over A q → ∀ φ : G ℚ Ω, IsFrob (F := ℚ) A q φ →
    ∃ τ ∈ Ine (F := ℚ) A, ∃ u : Oˣ, ν (q :: L) τ = (u : O) • ν L φ
  init : ∃ τ ∈ Ine (F := ℚ) A₀, ∃ u : Oˣ, ν [] τ = (u : O) • w₁

def IsCoc (α : G ℚ Ω →* Oˣ) (c : G ℚ Ω → W) : Prop :=
  IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + (α g : O) • c h

variable (W) in

def ShT (α : G ℚ Ω →* Oˣ) (δ : G ℚ Ω) (F : ℕ) (a : O) : Submodule O (G ℚ Ω → W) where
  carrier := {c | IsCoc α c ∧ c δ = 0 ∧ (∀ g, a • c g = 0) ∧
    (∀ A : ValuationSubring Ω, ¬ Over A F → ∀ g ∈ Ine (F := ℚ) A, c g = 0) ∧
    ∀ A : ValuationSubring Ω, Over A F → ∃ m : W, a • m = 0 ∧ ∀ g ∈ Dec (F := ℚ) A, c g = (α g : O) • m - m}
  zero_mem' := ⟨⟨IsLocallyConstant.const _, by simp⟩, rfl, by simp, by simp, fun _ _ => ⟨0, by simp⟩⟩
  add_mem' {x y} hx hy := ⟨⟨hx.1.1.add hy.1.1, fun g h => by simp only [Pi.add_apply, hx.1.2, hy.1.2, smul_add]; abel⟩,
    by simp [hx.2.1, hy.2.1], fun g => by simp [hx.2.2.1 g, hy.2.2.1 g],
    fun A hA g hg => by simp [hx.2.2.2.1 A hA g hg, hy.2.2.2.1 A hA g hg], fun A hA => by
      obtain ⟨m, hm, h⟩ := hx.2.2.2.2 A hA
      obtain ⟨m', hm', h'⟩ := hy.2.2.2.2 A hA
      exact ⟨m + m', by simp [hm, hm'], fun g hg => by simp only [Pi.add_apply, h g hg, h' g hg, smul_add]; abel⟩⟩
  smul_mem' t x hx := ⟨⟨hx.1.1.comp (t • ·), fun g h => by simp only [Pi.smul_apply, hx.1.2, smul_add, smul_comm t]⟩,
    by simp [hx.2.1], fun g => by rw [Pi.smul_apply, smul_comm, hx.2.2.1 g, smul_zero],
    fun A hA g hg => by simp [hx.2.2.2.1 A hA g hg], fun A hA => by
      obtain ⟨m, hm, h⟩ := hx.2.2.2.2 A hA
      exact ⟨t • m, by rw [smul_comm, hm, smul_zero], fun g hg => by
        simp only [Pi.smul_apply, h g hg, smul_sub, smul_comm t]⟩⟩

def zSum {F : ℕ} [NeZero F] (α : G ℚ Ω →* Oˣ) (σ : (ZMod F)ˣ → G ℚ Ω) (k : (ZMod F)ˣ → ℤ) : O :=
  ∑ t : (ZMod F)ˣ, (k t : O) * (((α (σ t))⁻¹ : Oˣ) : O)

abbrev zVal {F : ℕ} [NeZero F] (α : G ℚ Ω →* Oˣ) (σ : (ZMod F)ˣ → G ℚ Ω) (b : ℕ) : O := zSum α σ fun t => th F b t

variable (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]

structure Dat (N₀ m F : ℕ) (α : G ℚ Ω →* Oˣ) : Prop where
  odd_l : l ≠ 2
  cop : N₀.Coprime l
  pos : 1 ≤ m
  lev : F = N₀ * l ^ m
  triv : ∀ g ∈ fixMu ℚ Ω F, (l : O) ^ m ∣ (α g : O) - 1
  odd : ∀ g : G ℚ Ω, Lifts F (-1) g → (l : O) ^ m ∣ (α g : O) + 1
  notCyc : ∃ g : G ℚ Ω, IsUnit ((α g : O) - (chiO ℚ Ω l O g : O))

abbrev dualChar (α : G ℚ Ω →* Oˣ) : G ℚ Ω →* Oˣ := chiO ℚ Ω l O * α⁻¹

end Gal

def Rec : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (α : G ℚ Ω →* Oˣ) (a : O), a ≠ 0 → ∀ w₀ : QO l O, (∀ y : O, y • w₀ = 0 ↔ a ∣ y) →
    IsOpen {g : G ℚ Ω | a ∣ (α g : O) - 1} → ∀ (N q : ℕ), N ≠ 0 → l ∣ N → q.Prime → q ≠ l →
    ∀ c n : G ℚ Ω → QO l O, IsCoc α c → IsCoc (dualChar l α) n → (∀ g, a • c g = 0) → (∀ g, a • n g = 0) →
    (∀ A : ValuationSubring Ω, ¬ Over A (N * q) → ∀ g ∈ Ine (F := ℚ) A, a ∣ (α g : O) - 1 ∧ c g = 0 ∧ n g = 0) →
    (∀ A : ValuationSubring Ω, Over A N → ¬ Over A q →
      ∃ m : QO l O, a • m = 0 ∧ ∀ g ∈ Dec (F := ℚ) A, c g = (α g : O) • m - m) →
    ∀ A₀ : ValuationSubring Ω, Over A₀ q →
    (∀ g ∈ Dec (F := ℚ) A₀, a ∣ (α g : O) - 1 ∧ a ∣ (dualChar l α g : O) - 1) → (∀ g ∈ Ine (F := ℚ) A₀, c g = 0) →
    ∀ g ∈ Dec (F := ℚ) A₀, ∀ τ ∈ Ine (F := ℚ) A₀, ∀ y : O, n τ = y • w₀ → y • c g = 0

end UpperTheory.V.ML

end
