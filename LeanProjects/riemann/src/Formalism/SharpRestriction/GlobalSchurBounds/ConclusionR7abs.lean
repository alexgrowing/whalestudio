import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas

noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Ideal
open scoped Pointwise

abbrev gl (D : D7) (σ : D.host.E ≃ₐ[ℚ] D.host.E) : D.R.GG :=
  D.host.galE σ

def GaloisGroupProductIsomorphism (D : D7) : Prop :=
  Module.finrank ℚ D.host.E = 4 * D.R.n ∧
  (∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, gl D (σ * τ) = gl D σ * gl D τ) ∧
  Function.Bijective (gl D) ∧
  (∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
    σ (D.host.sqq) =
      ((((gl D σ).1.1 : ℤˣ) : ℤ) : D.host.E) * D.host.sqq ∧
    σ D.host.sqrtMinusD = ((((gl D σ).1.2 : ℤˣ) : ℤ) : D.host.E) * D.host.sqrtMinusD) ∧
  ∃ (θ : D.host.E) (ζ : CyclotomicField D.host.condN ℚ),
    IsPrimitiveRoot ζ (2 ^ (D.R.e + 2)) ∧ D.host.cycEmb θ = ζ + ζ⁻¹ ∧
    ∀ (σ : D.host.E ≃ₐ[ℚ] D.host.E) (u : (ZMod (2 ^ (D.R.e + 2)))ˣ),
      D.R.hH (gl D σ).2 = hcl D.R.e u ↔
        D.host.cycEmb (σ θ) =
          ζ ^ (u : ZMod (2 ^ (D.R.e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (D.R.e + 2))).val

def ComplexConjugationFixedField (D : D7) : Prop :=
  gl D D.host.conj = D.R.cc ∧
  (∀ (φ : D.host.E →+* ℂ) (x : D.host.E), φ (D.host.conj x) = starRingEnd ℂ (φ x)) ∧
  (∀ x : D.host.E, x ∈ D.host.F ↔ D.host.conj x = x) ∧
  (∀ x : D.host.E, x ∈ D.host.F ↔
    x ∈ IntermediateField.adjoin ℚ (insert (D.host.sqq * D.host.sqrtMinusD)
      {y : D.host.E | ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, (gl D σ).2 = 1 → σ y = y})) ∧
  Module.finrank ℚ D.host.F = D.R.f ∧
  (∀ (φ : D.host.E →+* ℂ), ∀ x ∈ D.host.F, starRingEnd ℂ (φ x) = φ x)

def DiscriminantSquareBounds (D : D7) : Prop :=
  discr D.host.E = discr D.host.F ^ 2 ∧
  ((∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr D.host.E → p ∣ D.host.condN) ∧
    (2 : ℤ) ∣ discr D.host.E ∧ (D.host.d : ℤ) ∣ discr D.host.E) ∧
  (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) * Real.sqrt D.host.d ≤ D.host.rdE ∧
  D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ∧
  (2 * D.R.f : ℝ) ≤ D.host.rdE ^ 2

def InertiaGroupCharacterization (D : D7) : Prop :=
  (∀ l : ℕ, l.Prime → l ∣ D.host.QS * D.host.q →
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(l : ℤ)}) →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      (σ ∈ P.inertia (D.host.E ≃ₐ[ℚ] D.host.E) ↔ ∃ u : (ZMod D.host.condN)ˣ,
        (u : ZMod D.host.condN).val ≡ 1 [MOD ordCompl[l] D.host.condN] ∧ gl D σ = D.host.art u) ∧
      (σ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P ↔ ∃ (u : (ZMod D.host.condN)ˣ) (k : ℕ),
        (u : ZMod D.host.condN).val ≡ l ^ k [MOD ordCompl[l] D.host.condN] ∧ gl D σ = D.host.art u) ∧
      (σ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P → gl D σ ∈ D.R.Psi)) ∧
  (∃ a : HH D, 2 • a = 0 ∧ D.R.h a = 0 ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(D.host.q : ℤ)}) →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      (σ ∈ P.inertia (D.host.E ≃ₐ[ℚ] D.host.E) ↔ (gl D σ = 1 ∨ gl D σ = D.R.tau2 a))) ∧
  ordH (hOf D.R.e D.host.q) = 2 ^ D.R.e ∧
  (∃ α : HH D, D.R.hH (D.R.iota α) = iotaH D.R.e (hOf D.R.e D.host.d) ∧
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(D.host.d : ℤ)}) →
    ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      (σ ∈ P.inertia (D.host.E ≃ₐ[ℚ] D.host.E) ↔ (gl D σ = 1 ∨ gl D σ = gOf D sgc0 0)) ∧
      (σ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P ↔
        gl D σ ∈ Subgroup.closure {gOf D sgc0 0, gOf D c0 α})) ∧
  2 * ordH (hOf D.R.e D.host.d) = 2 ^ D.R.e ∧
  jacobiSym (-(D.host.q : ℤ)) D.host.d = -1 ∧
  (∀ l : ℕ, l.Prime → l ∣ D.host.condN →
    ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(l : ℤ)}) →
      D.host.conj ∉ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P)

def projection_sandwich_lattice (D : D7) : Prop :=
  ∀ φ : D.host.E →+* ℂ, φ ∈ PhiEmb D ↔ ∀ x : D.host.E, x ∈ D.host.K → φ x = D.host.φ₀ x

def FrobeniusOrbitParity (D : D7) : Prop :=
  ∀ h : HH D,
    (∀ φ₀ : G0, (φ₀ = c0 ∨ φ₀ = sgc0) → ∀ τ ∈ D.R.Psi, ∀ i : ℤ,
      (Even i → (gOf D φ₀ h) ^ i * τ ∈ D.R.Psi) ∧
      (Odd i → D.R.cc * ((gOf D φ₀ h) ^ i * τ) ∈ D.R.Psi)) ∧
    (∀ (t : HH D) (i : ℤ),
      Formalism.HC.Frame.placeOf ((gOf D c0 h) ^ i * D.R.tau1 t) = D.R.tau1 (t + i • h)) ∧
    (∀ (t : HH D) (i : ℤ), Formalism.HC.Frame.placeOf ((gOf D sgc0 h) ^ i * D.R.tau1 t) =
      if Even i then D.R.tau1 (t + i • h) else D.R.tau2 (t + i • h))

def DefiniteLiftChain (D : D7) : Prop :=
  ∀ φ : D.R.GG,
    (D.R.cc ∈ Subgroup.zpowers φ ↔ φ.1 = c0 ∧ Odd (orderOf φ.2)) ∧
    (∀ p : ℕ, p.Prime → (span {(p : ℤ)}).ramificationIdxIn (𝓞 D.host.E) = 1 → frob D p = φ →
      ∀ 𝔭 : Ideal (𝓞 D.host.F), 𝔭.IsPrime → 𝔭.LiesOver (span {(p : ℤ)}) →
        (Inert D 𝔭 ↔ D.R.cc ∈ Subgroup.zpowers φ) ∧
        (D.R.cc ∉ Subgroup.zpowers φ → (primesOver 𝔭 (𝓞 D.host.E)).ncard = 2))

def FrobeniusOrbitPlaceCount (D : D7) : Prop :=
  ∀ h : HH D, ∀ τ ∈ D.R.Psi,
    (Set.range fun i : ℤ => Formalism.HC.Frame.placeOf ((gOf D c0 h) ^ i * τ)).ncard = addOrderOf h ∧
    (∀ i i' : ℤ,
      (Formalism.HC.Frame.placeOf ((gOf D c0 h) ^ i * τ) = Formalism.HC.Frame.placeOf ((gOf D c0 h) ^ i' * τ) ↔
        ((addOrderOf h : ℕ) : ℤ) ∣ i - i')) ∧
    (D.R.h h ≠ 0 → Even (addOrderOf h))

def SignTwistedOrbitOrder (D : D7) : Prop :=
  ∀ h : HH D,
    orderOf (gOf D sgc0 h) = Nat.lcm 2 (addOrderOf h) ∧
    ∀ τ ∈ D.R.Psi, ∀ i i' : ℤ,
      (Formalism.HC.Frame.placeOf ((gOf D sgc0 h) ^ i * τ) = Formalism.HC.Frame.placeOf ((gOf D sgc0 h) ^ i' * τ) ↔
        ((Nat.lcm 2 (addOrderOf h) : ℕ) : ℤ) ∣ i - i')

def Conclusion4a (D : D7) : Prop :=
  ∀ l : ℕ, Odd l → ∀ j : ℕ, j ≤ D.R.e →
    ((2 ^ j : ℕ) • hOf D.R.e l = 0 ↔
      ((l : ZMod (4 * 2 ^ D.R.e / 2 ^ j)) = 1 ∨ (l : ZMod (4 * 2 ^ D.R.e / 2 ^ j)) = -1))

def Conclusion4b (D : D7) : Prop :=
  ∀ J : ℝ, 1 ≤ J → ∀ j₀ : ℕ, (2 : ℝ) ^ j₀ ≤ min J ((2 ^ D.R.e : ℕ) : ℝ) → min J ((2 ^ D.R.e : ℕ) : ℝ) < (2 : ℝ) ^ (j₀ + 1) →
    4 ≤ 4 * 2 ^ D.R.e / 2 ^ j₀ ∧ 4 * ((2 ^ D.R.e : ℕ) : ℝ) / J ≤ ((4 * 2 ^ D.R.e / 2 ^ j₀ : ℕ) : ℝ) ∧
    ∀ l : ℕ, l.Prime → l ≠ 2 → (ordH (hOf D.R.e l) : ℝ) ≤ J →
      ((l : ZMod (4 * 2 ^ D.R.e / 2 ^ j₀)) = 1 ∨ (l : ZMod (4 * 2 ^ D.R.e / 2 ^ j₀)) = -1) ∧
      4 * 2 ^ D.R.e / 2 ^ j₀ ≤ l + 1

def PrimeSumLogBound (D : D7) : Prop :=
  ∀ J : ℝ, 1 ≤ J → ∀ S : Finset ℕ,
    (∀ l ∈ S, l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤ 2 * J ^ 2 * Real.log ((2 ^ D.R.e : ℕ) : ℝ) / ((2 ^ D.R.e : ℕ) : ℝ) ^ 2

open Classical in

def SmallOrderPrimeLogSumBound (D : D7) : Prop :=
  ∀ J : ℝ, 1 ≤ J → ∀ Y : ℝ,
    ∑ l ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
        (fun l => l.Prime ∧ l ≠ 2 ∧ (ordH (hOf D.R.e l) : ℝ) ≤ J),
      Real.log l / (l : ℝ) ≤ J * Real.log (((2 ^ D.R.e : ℕ) : ℝ) * Y) ^ 2 / ((2 ^ D.R.e : ℕ) : ℝ)

def GGEveryPlace (D : D7) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∃ T₂ : Finset ℕ,
    (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) ∧ NoThreeTermRelation T₂ Lw ∧
    (D.R.n0 : ℝ) / Lw * Real.exp (-7 * Real.sqrt (Real.log D.R.n0 * Real.log Lw)) ≤ T₂.card

open Classical in

def WeightBudgetBound (D : D7) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∀ T₂ : Finset ℕ,
    (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) → NoThreeTermRelation T₂ Lw →
    ∀ u₀ t h : HH D,
      (Lw < addOrderOf h → ∀ i₀ : ℤ,
        ((Finset.Icc i₀ (i₀ + Lw)).filter (fun i : ℤ => t + i • h ∈ transl T₂ u₀)).card ≤ 2) ∧
      (addOrderOf h ≤ 4 * Lw → (coset t h ∩ transl T₂ u₀).ncard ≤ 1)

def thickOf (D : D7) (T₂ : Finset ℕ) (u₀ : HH D) : Set (D.R.GG) :=
  {g | ∃ s ∈ T₂, g = D.R.tau2 (D.R.dig s + u₀)}

def ThickPlacesFreeSet (D : D7) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∀ T₂ : Finset ℕ,
    (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) → NoThreeTermRelation T₂ Lw → ∀ u₀ : HH D,
    ∀ φ : D.R.GG, φ ∉ D.R.Psi → φ ≠ D.R.cc → ∀ τ : D.R.GG, ∀ i : ℤ,
      ¬ (Formalism.HC.Frame.placeOf (φ ^ i * τ) ∈ thickOf D T₂ u₀ ∧ Formalism.HC.Frame.placeOf (φ ^ (i + 1) * τ) ∈ thickOf D T₂ u₀ ∧
        Formalism.HC.Frame.placeOf (φ ^ (i + 2) * τ) ∈ thickOf D T₂ u₀)

def NoConsecutiveThickPlaces (D : D7) : Prop :=
  ∀ (T₂ : Finset ℕ) (u₀ h : HH D) (τ : D.R.GG) (i : ℤ),
    ¬ (Formalism.HC.Frame.placeOf ((gOf D sgc0 h) ^ i * τ) ∈ thickOf D T₂ u₀ ∧
      Formalism.HC.Frame.placeOf ((gOf D sgc0 h) ^ (i + 1) * τ) ∈ thickOf D T₂ u₀)

def TranslateSetCardinality (D : D7) : Prop :=
  ∀ Lw : ℕ, 2 ≤ Lw → ∀ T₂ : Finset ℕ, (∀ s ∈ T₂, (s : ℝ) < (D.R.n0 : ℝ) / (4 * Lw)) →
    (∀ u₀ : HH D, (transl T₂ u₀).ncard = T₂.card) ∧
    ∀ y : HH D, {u₀ : HH D | y ∈ transl T₂ u₀}.ncard = T₂.card

open Classical in

def SecondMomentBadEventsBound (D : D7) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 16 ≤ δ * D.R.n →
  ∀ β : ℝ, 0 ≤ β → ∀ H₀ : Set (HH D), ∀ BAD : HH D → HH D → Finset (HH D) → Prop,
    (∀ h ∈ H₀, ∀ t : HH D,
      (∑ T : Finset (HH D), if t ∈ T ∧ BAD h t T then bern δ T else 0) ≤ β * δ) →
    ∀ (P : Finset ℕ) (hp : ℕ → HH D) (ω : ℕ → ℝ),
      (∀ p ∈ P, hp p ∈ H₀) → (∀ p ∈ P, 0 ≤ ω p) →
      ∃ T : Finset (HH D), δ * D.R.n / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 3 / 2 * δ * D.R.n ∧
        ∑ p ∈ P, ω p * ((T.filter (fun t => BAD (hp p) t T)).card : ℝ) ≤
          4 * β * δ * D.R.n * ∑ p ∈ P, ω p

theorem classMap_estimate_of_partial (D : D7) (sc : Scale) (h : SecondMomentBadEventsBound D) : Conclusion6 D sc := by
  classical
  intro δ h0 h1 h16 β BAD _ hb P hp ω hP hω
  by_cases hβ : 0 ≤ β
  · obtain ⟨T, a, b, c⟩ := h δ h0 h1 h16 β hβ {h | sc.x ^ (sc.eps / 4) ≤ (addOrderOf h : ℝ)} BAD
      (fun h hh t => hb h hh t) P hp ω hP hω
    refine ⟨T, a, le_trans b ?_, c⟩
    have : 0 ≤ δ * D.R.n := by linarith
    nlinarith
  · rcases P.eq_empty_or_nonempty with rfl | ⟨p, hp'⟩
    · obtain ⟨T, a, b, _⟩ := h δ h0 h1 h16 0 le_rfl ∅ BAD (fun h hh => absurd hh (by simp)) ∅ hp ω
        (by simp) (by simp)
      refine ⟨T, a, le_trans b ?_, by simp⟩
      have : 0 ≤ δ * D.R.n := by linarith
      nlinarith
    · exfalso
      have h2 := hb (hp p) (hP p hp') 0
      have h3 : 0 ≤ ∑ T : Finset (HH D), if (0 : HH D) ∈ T ∧ BAD (hp p) 0 T then bern δ T else 0 := by
        refine Finset.sum_nonneg fun T _ => ?_
        split_ifs
        · exact mul_nonneg (pow_nonneg h0.le _) (pow_nonneg (by linarith) _)
        · exact le_rfl
      have : β * δ < 0 := mul_neg_of_neg_of_pos (not_le.mp hβ) h0
      linarith

open Classical in

def PairwiseIndependentOrbitPoints (D : D7) : Prop :=
  (∀ t h : HH D, ∀ i i' : ℕ, i < addOrderOf h → i' < addOrderOf h → t + i • h = t + i' • h → i = i') ∧
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    (∀ S A : Finset (HH D), A ⊆ S →
      (∑ T : Finset (HH D), if T ∩ S = A then bern δ T else 0) =
        δ ^ A.card * (1 - δ) ^ (S.card - A.card)) ∧
    (∀ (t : HH D) (S A : Finset (HH D)), t ∉ S → A ⊆ S →
      (∑ T : Finset (HH D), if t ∈ T ∧ T ∩ S = A then bern δ T else 0) =
        δ * (δ ^ A.card * (1 - δ) ^ (S.card - A.card)))

def ProPrimeIwahoriSubgroupExists : Prop :=
  ∀ (g k : ℕ) [Fact g.Prime], ∃ P : Subgroup (GL (Fin k) ℤ_[g]),
    (∀ M : GL (Fin k) ℤ_[g], M ∈ P ↔ ∀ i j : Fin k,
      (j < i → PadicInt.toZMod ((M : Matrix (Fin k) (Fin k) ℤ_[g]) i j) = 0) ∧
      PadicInt.toZMod ((M : Matrix (Fin k) (Fin k) ℤ_[g]) i i) = 1) ∧
    IsProG g P

def DoubleCosetFreeActionOfNormal : Prop :=
  ∀ (G : Type) [Group G] (Γ U₀ U₁ : Subgroup G), U₁ ≤ U₀ →
    (∀ u ∈ U₀, ∀ v ∈ U₁, u⁻¹ * v * u ∈ U₁) →
    (∀ y : G, Γ ⊓ U₀.map (MulAut.conj y).toMonoidHom = ⊥) →
    (∀ y y' u : G, u ∈ U₀ → (∃ γ ∈ Γ, ∃ v ∈ U₁, y' = γ * y * v) →
      ∃ γ ∈ Γ, ∃ v ∈ U₁, y' * u = γ * (y * u) * v) ∧
    (∀ y u : G, u ∈ U₁ → ∃ γ ∈ Γ, ∃ v ∈ U₁, y * u = γ * y * v) ∧
    (∀ y u : G, u ∈ U₀ → (∃ γ ∈ Γ, ∃ v ∈ U₁, y * u = γ * y * v) → u ∈ U₁) ∧
    (∀ y y' : G, (∃ γ ∈ Γ, ∃ u ∈ U₀, y' = γ * y * u) ↔
      ∃ u ∈ U₀, ∃ γ ∈ Γ, ∃ v ∈ U₁, y' = γ * (y * u) * v)

def DoubleCosetIndexFormula : Prop :=
  ∀ (G : Type) [Group G] (Γ U₀ U₁ : Subgroup G), U₁ ≤ U₀ →
    (∀ u ∈ U₀, ∀ v ∈ U₁, u⁻¹ * v * u ∈ U₁) →
    (∀ y : G, Γ ⊓ U₀.map (MulAut.conj y).toMonoidHom = ⊥) →
    Nat.card (DoubleCoset.Quotient (Γ : Set G) (U₁ : Set G)) =
      U₁.relIndex U₀ * Nat.card (DoubleCoset.Quotient (Γ : Set G) (U₀ : Set G))

def EquivariantFunctionsByDoubleCosetValues : Prop :=
  ∀ (G : Type) [Group G] (Γ U : Subgroup G) (W : Type) [MulAction U W] (ι : Type) (y : ι → G),
    (∀ x : G, ∃! c : ι, ∃ γ ∈ Γ, ∃ u ∈ U, x = γ * y c * u) →
    (∀ φ : G → W, (∀ γ ∈ Γ, ∀ (x : G) (u : U), φ (γ * x * u) = u⁻¹ • φ x) →
      ∀ (c : ι) (u : U), (∃ γ ∈ Γ, (u : G) = (y c)⁻¹ * γ * y c) → u • φ (y c) = φ (y c)) ∧
    (∀ w : ι → W,
      (∀ (c : ι) (u : U), (∃ γ ∈ Γ, (u : G) = (y c)⁻¹ * γ * y c) → u • w c = w c) →
      ∃! φ : G → W, (∀ γ ∈ Γ, ∀ (x : G) (u : U), φ (γ * x * u) = u⁻¹ • φ x) ∧ ∀ c, φ (y c) = w c)

def DifferentIdealPrimeFactorization (D : D7) : Prop :=
  (∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
    σ • differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) = differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) ∧
  ∃ δ : ℕ → ℕ, (∀ l ∈ (D.host.QS * D.host.q).primeFactors, 1 ≤ δ l) ∧
    differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) =
      ∏ l ∈ (D.host.QS * D.host.q).primeFactors,
        (∏ P ∈ IsDedekindDomain.primesOverFinset (span {(l : ℤ)}) (𝓞 D.host.E), P) ^ δ l

abbrev cA (D : D7) (cc : Ideal (𝓞 D.host.K))
    (aa : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * aa

def Unimod8 (D : D7) (aa : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Prop :=
  ∀ y : D.host.E, y ∈ aa ↔
    ∀ x ∈ aa, Algebra.trace D.host.K D.host.E (x * D.host.conj y) ∈
      (algebraMap (𝓞 D.host.K) D.host.K).range

def Pol8 (D : D7) (aa : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    (∀ φ ∈ PhiEmb D, 0 < (φ (-1 / ((Ideal.absNorm cc : D.host.E) * D.host.sqrtMinusD))).im) ∧
    ∀ y : D.host.E, y ∈ cA D cc aa ↔
      ∀ x ∈ cA D cc aa,
        Algebra.trace ℚ D.host.E
          (-1 / ((Ideal.absNorm cc : D.host.E) * D.host.sqrtMinusD) * D.host.conj x * y) ∈
            (algebraMap ℤ ℚ).range

def InverseDifferentSquareRootIdeal (D : D7) : Prop :=
  ∃ aa aab : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E,
    (∀ x : D.host.E, x ∈ aab ↔ D.host.conj x ∈ aa) ∧
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = aa * aab ∧
    (∀ σ : D.host.E ≃ₐ[ℚ] D.host.E, gl D σ ∈ D.R.Psi → ∀ x : D.host.E, x ∈ aa ↔ σ x ∈ aa) ∧
    Unimod8 D aa ∧ Pol8 D aa

def AdmissibleIdealUnimodular (D : D7) : Prop := Unimod8 D D.host.AA0 ∧ Pol8 D D.host.AA0

def FieldLemmasAllHold (D : D7) : Prop :=
  GaloisGroupProductIsomorphism D ∧ ComplexConjugationFixedField D ∧ DiscriminantSquareBounds D ∧ InertiaGroupCharacterization D ∧ projection_sandwich_lattice D ∧ FrobeniusOrbitParity D ∧ DefiniteLiftChain D ∧ FrobeniusOrbitPlaceCount D ∧ SignTwistedOrbitOrder D ∧
  Conclusion4a D ∧ Conclusion4b D ∧ PrimeSumLogBound D ∧ SmallOrderPrimeLogSumBound D ∧ GGEveryPlace D ∧ WeightBudgetBound D ∧ ThickPlacesFreeSet D ∧ NoConsecutiveThickPlaces D ∧ TranslateSetCardinality D ∧
  SecondMomentBadEventsBound D ∧ PairwiseIndependentOrbitPoints D ∧ DifferentIdealPrimeFactorization D ∧ InverseDifferentSquareRootIdeal D ∧ AdmissibleIdealUnimodular D

def ConclusionR7abs : Prop := ProPrimeIwahoriSubgroupExists ∧ DoubleCosetFreeActionOfNormal ∧ DoubleCosetIndexFormula ∧ EquivariantFunctionsByDoubleCosetValues

end Formalism.MainNotions.UnusedSlot33

end
