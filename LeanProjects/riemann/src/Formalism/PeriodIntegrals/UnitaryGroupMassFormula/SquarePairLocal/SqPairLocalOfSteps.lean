import Mathlib
import Formalism.PeriodIntegrals.SqPair

noncomputable section
open NumberField Matrix

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

def cj (E : Type) [Field E] [NumberField E] [StarRing E] : 𝓞 E →+* 𝓞 E :=
  RingOfIntegers.mapRingHom (starRingEnd E)

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Pres {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (e : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ y ∈ L, e *ᵥ y ∈ L

def SmallAt {N : ℕ} (Q : Ideal (𝓞 E)) (c : 𝓞 E) (L : Submodule (𝓞 E) (Fin N → E))
    (M : Matrix (Fin N) (Fin N) E) : Prop :=
  ∀ y ∈ L, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ m ∈ L, s • (M *ᵥ y) = c • m

def Good {N : ℕ} (Q : Ideal (𝓞 E)) (c : 𝓞 E) (L' L'' : Submodule (𝓞 E) (Fin N → E))
    (e : Matrix (Fin N) (Fin N) E) : Prop :=
  SmallAt Q c L' (e * e - e) ∧ SmallAt Q c L'' (e * e - e) ∧
    SmallAt Q c L' (e + eᴴ - 1) ∧ SmallAt Q c L'' (e + eᴴ - 1)

def IntAt (Q : Ideal (𝓞 E)) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, (s : E) * x = (w : E)

def DivAt (Q : Ideal (𝓞 E)) (c : 𝓞 E) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, (s : E) * x = (c : E) * (w : E)

def LocGlob : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (X : Submodule (𝓞 E) W) (x : W) (p : ℕ), p.Prime →
    (∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q → ∃ s : 𝓞 E, s ∉ Q ∧ s • x ∈ X) →
    ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ (s : 𝓞 E) • x ∈ X

def IntMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)), IsSDG E N L' → IsSDG E N L'' → ∀ n : 𝓞 E, n ≠ 0 →
    ∃ c : ℕ, c ≠ 0 ∧ ∀ y, (y ∈ L' ∨ y ∈ L'') → ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (c : 𝓞 E) • y = n • m

def PowLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E)), Q.IsMaximal → ∀ c : 𝓞 E, c ≠ 0 →
    ∃ K : ℕ, ∀ x ∈ Q ^ K, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = c * w

def Glued : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ p : ℕ, p.Prime → ∀ a : ℕ, ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
        ∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q → Good Q ((p : 𝓞 E) ^ a) L' L'' e

def OnePlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
          Good Q c L' L'' e ∧ Good (Q.comap (cj E)) c L' L'' e

def Glue : Prop := OnePlace → Glued

def SplitPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) ≠ Q → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧
          Good Q c L' L'' e ∧ Good (Q.comap (cj E)) c L' L'' e

def InertPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q → ∀ c : 𝓞 E, c ≠ 0 →
        ∃ e : Matrix (Fin N) (Fin N) E, Pres L' e ∧ Pres L'' e ∧ Good Q c L' L'' e

structure StModel (E : Type) [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)) where
  R : Type
  [cr : CommRing R]
  σ : R ≃+* R
  σσ : ∀ x, σ (σ x) = x
  R₀ : Subring R
  mem₀ : ∀ x, x ∈ R₀ ↔ σ x = x
  [dom : IsDomain R₀]
  [dvr : IsDiscreteValuationRing R₀]
  [hens : HenselianLocalRing R₀]
  [fin : Finite (IsLocalRing.ResidueField R₀)]
  unram : ∃ θ : R, IsUnit (θ - σ θ)
  j : 𝓞 E →+* R
  j_cj : ∀ x : 𝓞 E, j (cj E x) = σ (j x)
  ϖ : 𝓞 E
  ϖ_cj : cj E ϖ = ϖ
  ϖ_Q : ϖ ∈ Q
  ϖ_mem : j ϖ ∈ R₀
  ϖ_irr : Irreducible (⟨j ϖ, ϖ_mem⟩ : R₀)
  unit_of : ∀ s : 𝓞 E, s ∉ Q → IsUnit (j s)
  dense : ∀ (x : R) (K : ℕ), ∃ y : 𝓞 E, ∃ z : R, x - j y = j ϖ ^ K * z
  detect : ∀ (x : 𝓞 E) (K : ℕ), (∃ z : R, j x = j ϖ ^ K * z) →
    ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * x = ϖ ^ K * w

def ModelEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q → Nonempty (StModel E Q)

def Dict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)), IsSDG E N L →
      ∀ Q : Ideal (𝓞 E), Q.IsMaximal → Q.comap (cj E) = Q →
        ∃ G : Matrix (Fin N) (Fin N) E, Gᴴ * G = 1 ∧ G * Gᴴ = 1 ∧
          ∀ y : Fin N → E, (∃ s : 𝓞 E, s ∉ Q ∧ s • y ∈ L) ↔ ∀ i, IntAt Q ((Gᴴ *ᵥ y) i)

def LocMat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (Q : Ideal (𝓞 E)), Q.IsMaximal →
    ∀ M : StModel E Q, LocCartanPair →
      ∀ (N : ℕ), Even N → ∀ u : Matrix (Fin N) (Fin N) E, uᴴ * u = 1 → u * uᴴ = 1 → ∀ K : ℕ,
        ∃ e₁ : Matrix (Fin N) (Fin N) E, (∀ i j, IntAt Q (e₁ i j)) ∧ (∀ i j, IntAt Q ((uᴴ * e₁ * u) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((e₁ * e₁ - e₁) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((uᴴ * (e₁ * e₁ - e₁) * u) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((e₁ + e₁ᴴ - 1) i j)) ∧
          (∀ i j, DivAt Q (M.ϖ ^ K) ((uᴴ * (e₁ + e₁ᴴ - 1) * u) i j))

def InertAsm : Prop := LocCartanPair → ModelEx → Dict → LocMat → PowLoc → InertPlace

section Alg

variable {N : ℕ}

theorem coe_smul (r : 𝓞 E) (v : Fin N → E) : (r : E) • v = r • v := by
  first
  | rfl
  | (ext i; rfl)
  | (ext i; simp [Algebra.smul_def])

theorem pres_one_sub {L : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E}
    (he : Pres L e) : Pres L (1 - e) := by
  intro y hy
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact L.sub_mem hy (he y hy)

variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}

theorem smallAt_add {M M' : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M)
    (h' : SmallAt Q c L M') : SmallAt Q c L (M + M') := by
  intro y hy
  obtain ⟨s, hs, m, hm, h1⟩ := h y hy
  obtain ⟨s', hs', m', hm', h2⟩ := h' y hy
  refine ⟨s * s', fun hss => (hQ.mem_or_mem hss).elim hs hs', s' • m + s • m',
    L.add_mem (L.smul_mem _ hm) (L.smul_mem _ hm'), ?_⟩
  have e1 : (s * s') • (M *ᵥ y) = s' • (c • m) := by rw [mul_comm, mul_smul, h1]
  have e2 : (s * s') • (M' *ᵥ y) = s • (c • m') := by rw [mul_smul, h2]
  rw [Matrix.add_mulVec, smul_add, e1, e2]
  module

theorem smallAt_neg {M : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M) : SmallAt Q c L (-M) := by
  intro y hy
  obtain ⟨s, hs, m, hm, h1⟩ := h y hy
  exact ⟨s, hs, -m, L.neg_mem hm, by rw [Matrix.neg_mulVec, smul_neg, h1, smul_neg]⟩

theorem smallAt_mul {M B : Matrix (Fin N) (Fin N) E} (h : SmallAt Q c L M) (hB : Pres L B) :
    SmallAt Q c L (M * B) := by
  intro y hy
  obtain ⟨s, hs, m, hm, h1⟩ := h _ (hB y hy)
  exact ⟨s, hs, m, hm, by rw [← Matrix.mulVec_mulVec, h1]⟩

omit hQ in
theorem adj_eq (e : Matrix (Fin N) (Fin N) E) : eᴴ * e = -(e * e - e) + (e + eᴴ - 1) * e := by
  noncomm_ring

omit hQ in
theorem adj_eq' (e : Matrix (Fin N) (Fin N) E) :
    (1 - e)ᴴ * (1 - e) = -(e * e - e) + -((e + eᴴ - 1) * (1 - e)) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  noncomm_ring

theorem three_small {L' L'' : Submodule (𝓞 E) (Fin N → E)} {e : Matrix (Fin N) (Fin N) E}
    (he' : Pres L' e) (he'' : Pres L'' e) (hg : Good Q c L' L'' e)
    (M : Matrix (Fin N) (Fin N) E)
    (hM : M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E))) :
    SmallAt Q c L' M ∧ SmallAt Q c L'' M := by
  obtain ⟨g1, g2, g3, g4⟩ := hg
  rcases hM with rfl | rfl | rfl
  · exact ⟨g1, g2⟩
  · rw [adj_eq]
    exact ⟨smallAt_add (smallAt_neg g1) (smallAt_mul g3 he'),
      smallAt_add (smallAt_neg g2) (smallAt_mul g4 he'')⟩
  · rw [adj_eq']
    exact ⟨smallAt_add (smallAt_neg g1) (smallAt_neg (smallAt_mul g3 (pres_one_sub he'))),
      smallAt_add (smallAt_neg g2) (smallAt_neg (smallAt_mul g4 (pres_one_sub he'')))⟩

end Alg

theorem nat_notMem {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c)
    (hpQ : (p : 𝓞 E) ∈ Q) : (c : 𝓞 E) ∉ Q := by
  intro hcQ
  have hcop : Nat.Coprime p c := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (c : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) hab
    push_cast at this
    exact this
  have h1Q : (1 : 𝓞 E) ∈ Q := h1 ▸ Q.add_mem (Q.mul_mem_left _ hpQ) (Q.mul_mem_left _ hcQ)
  exact hQ.ne_top ((Ideal.eq_top_iff_one _).mpr h1Q)

theorem pLocalAll_of_glued (h1 : LocGlob) (h2 : IntMul) (h3 : Glued) : PLocalAll := by
  unfold PLocalAll
  intro E _ _ _ hE N L' L'' hN h' h'' n hn p hp
  unfold PLocal
  obtain ⟨c, hc0, hc⟩ := h2 E N L' L'' h' h'' n hn
  obtain ⟨a, c', hc', hcc⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.ne_one
  obtain ⟨e, he', he'', hg⟩ := h3 E hE N L' L'' hN h' h'' p hp a
  refine ⟨e, he', he'', ?_⟩
  intro M hM y hy
  have hcast : ((c : ℕ) : 𝓞 E) = (c' : 𝓞 E) * (p : 𝓞 E) ^ a := by
    rw [hcc]; push_cast; ring
  let X : Submodule (𝓞 E) (Fin N → E) := (L' ⊓ L'').map (n • LinearMap.id)
  have hloc : ∀ Q : Ideal (𝓞 E), Q.IsMaximal → (p : 𝓞 E) ∈ Q →
      ∃ s : 𝓞 E, s ∉ Q ∧ s • ((c' : 𝓞 E) • (M *ᵥ y)) ∈ X := by
    intro Q hQ hpQ
    haveI : Q.IsPrime := hQ.isPrime
    have hsm := three_small he' he'' (hg Q hQ hpQ) M hM
    have key : ∃ s : 𝓞 E, s ∉ Q ∧ ∃ m, (m ∈ L' ∨ m ∈ L'') ∧
        s • (M *ᵥ y) = (p : 𝓞 E) ^ a • m := by
      rcases hy with hy | hy
      · obtain ⟨s, hs, m, hm, h⟩ := hsm.1 y hy
        exact ⟨s, hs, m, Or.inl hm, h⟩
      · obtain ⟨s, hs, m, hm, h⟩ := hsm.2 y hy
        exact ⟨s, hs, m, Or.inr hm, h⟩
    obtain ⟨s, hs, m, hm, h⟩ := key
    obtain ⟨m', hm1, hm2, hm'⟩ := hc m hm
    refine ⟨s, hs, ?_⟩
    rw [Submodule.mem_map]
    refine ⟨m', ⟨hm1, hm2⟩, ?_⟩
    show n • m' = s • ((c' : 𝓞 E) • (M *ᵥ y))
    rw [← hm', smul_smul, mul_comm s, ← smul_smul, h, smul_smul, ← hcast]
  obtain ⟨s, hsp, hsx⟩ := h1 E (Fin N → E) X ((c' : 𝓞 E) • (M *ᵥ y)) p hp hloc
  rw [Submodule.mem_map] at hsx
  obtain ⟨m, ⟨hm1, hm2⟩, hmeq⟩ := hsx
  have hmeq' : n • m = (s : 𝓞 E) • ((c' : 𝓞 E) • (M *ᵥ y)) := hmeq
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (p : ℤ) ∣ s * (c' : ℤ) := by
    intro hd
    rcases hpZ.dvd_or_dvd hd with hd | hd
    · exact hsp hd
    · exact hc' (by exact_mod_cast hd)
  have heq : (((s * (c' : ℤ)) : ℤ) : 𝓞 E) • (M *ᵥ y) = n • m := by
    rw [hmeq', smul_smul]
    push_cast
    rfl
  refine ⟨s * (c' : ℤ), hnd, m, hm1, hm2, ?_⟩
  first
  | exact heq
  | simpa only [coe_smul, Int.cast_smul_eq_zsmul] using heq
  | simpa [coe_smul] using heq

theorem glued_of (hG : Glue) (hS : SplitPlace) (hI : InertPlace) : Glued := by
  apply hG
  intro E _ _ _ hE N L' L'' hN h' h'' Q hQ c hc
  by_cases hq : Q.comap (cj E) = Q
  · obtain ⟨e, h1, h2, h3⟩ := hI E hE N L' L'' hN h' h'' Q hQ hq c hc
    refine ⟨e, h1, h2, h3, ?_⟩
    rw [hq]
    exact h3
  · exact hS E hE N L' L'' hN h' h'' Q hQ hq c hc

theorem sqPairLocal_of_steps (hLC : LocCartanPair) (h1 : LocGlob) (h2 : IntMul) (h3 : Glue)
    (h4 : SplitPlace) (h5 : InertAsm) (h6 : ModelEx) (h7 : Dict) (h8 : LocMat) (h9 : PowLoc) :
    PLocalAll := pLocalAll_of_glued h1 h2 (glued_of h3 h4 (h5 hLC h6 h7 h8 h9))

end PI.SqPairLocal
