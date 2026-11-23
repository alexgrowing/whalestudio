import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd UpperTheory.V.Br
open scoped ComplexConjugate

namespace UpperTheory.V.Af.Rn

def Sl2Two : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W R L : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    W * R - R * W = (2 : ℂ) • R → W * L - L * W = (-2 : ℂ) • L → (4 : ℂ) • (R * L) = -(W * W - (2 : ℂ) • W) →
    (4 : ℂ) • (L * R) = -(W * W + (2 : ℂ) • W) →
    (∀ x, H x x = 0 → x = 0) → (∀ x y, H (W x) y = H x (W y)) → (∀ x y, H (R x) y = -H x (L y)) → (∀ x y, H (L x) y = -H x (R y)) →
    (∃ x, x ≠ 0 ∧ ∃ n : ℤ, W x = (n : ℂ) • x) →
    ∃ x, x ≠ 0 ∧ ((W x = (2 : ℂ) • x ∧ L x = 0) ∨ (W x = (-2 : ℂ) • x ∧ R x = 0) ∨ (W x = 0 ∧ L x = 0))

def LowTwo : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (A B C J : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ),
    (∀ x, A (B x) = B (A x) + B x) → (∀ x, A (C x) = C (A x) - C x) → (∀ x, B (C x) = C (B x) + (2 : ℂ) • A x) →
    (∀ x, C (B x) = -A (A x) - A x) → (∀ x, H x x = 0 → x = 0) → (∀ x y, H (A x) y = -H x (A y)) → (∀ x y, H (B x) y = -H x (B y)) →
    (∀ x y, H (C x) y = -H x (C y)) → (∀ x, J x = 0 → x = 0) → (∀ x, A (J x) = J (A x)) → (∀ x, B (J x) = -J (B x)) →
    (∀ x, C (J x) = -J (C x)) → (∃ x, x ≠ 0 ∧ ∃ n : ℤ, B x - C x = (Complex.I * n) • x) →
    ∃ x, x ≠ 0 ∧ (B x - C x = (Complex.I * 2) • x ∨ B x - C x = 0) ∧ (2 : ℂ) • A x = Complex.I • (B x + C x)

def HolTwo : Prop :=
  ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {(1 / 2 : ℂ), -(1 / 2 : ℂ)}) → ∀ H, Gk.IsHerm π H →
    ∃ φ ∈ π.V, φ ≠ 0 ∧ (IsLow 2 φ ∨ IsLow 0 φ)

def NoLow : Prop := ∀ π : TR.CuspSub ℚ 2, ¬ ∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow 0 φ

def SatHerm : Prop :=
  ∀ (π : TR.CuspSub ℚ 2) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), Gk.IsHerm π H → ∀ (w : Pl ℚ) (α β : ℂˣ), π.HasSat w {α, β} →
    conj ((α : ℂ) + β) * ((α * β : ℂˣ) : ℂ) = (α : ℂ) + β

def HermOf : Prop :=
  ∀ (c : ℂ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {c, -c}) → ∃ H, Gk.IsHerm π H

def EigOfLow : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ) →
    ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (g : Eigenform k N χ), ∀ᶠ w : Pl ℚ in Filter.cofinite, ∃ α β : ℂˣ,
      π.HasSat w {α, β} ∧ g.a (normV w) = (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) ∧
        ((α * β : ℂˣ) : ℂ) = χ (normV w : ZMod N)

def UnitTw : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ π₀ : TR.CuspSub ℚ 2, (∀ v, π₀.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) ∧
      ∀ w : Pl ℚ, ∃ t : ℂˣ, (∀ B, π₀.HasSat w B ↔ π.HasSat w (B.map (· * t))) ∧ ∀ α β : ℂˣ,
        ((algSat 2 (normV w) {α * t, β * t}).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod =
          X ^ 2 - C ((((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β)) * X + C (((α * β : ℂˣ) : ℂ) * (normV w : ℂ) ^ (k - 1))

def EvPl : Prop :=
  (∀ P : ℕ → Prop, (∀ᶠ w : Pl ℚ in Filter.cofinite, P (normV w)) ↔ ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → P p) ∧
    ∀ M : ℕ, 0 < M → ∀ᶠ w : Pl ℚ in Filter.cofinite, ¬ normV w ∣ M

def NewHerm : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (f : Newform k) (w : Pl ℚ), ¬ normV w ∣ f.M → conj (f.a (normV w)) * f.χ (normV w : ZMod f.M) = f.a (normV w)

def PolyInj : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (j : ℤ) (B B' : Multiset ℂˣ),
    ((algSat 2 q B).map fun b => X - C ((q : ℂ) ^ j * b)).prod = ((algSat 2 q B').map fun b => X - C ((q : ℂ) ^ j * b)).prod → B = B'

def NewAE : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (j : ℤ) (π : TR.CuspSub ℚ 2), (∀ v, π.HasInfChar v {1 / 2 + (j : ℂ), 3 / 2 - (k : ℂ) + (j : ℂ)}) →
    ∃ f : Newform k, ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∃ B, π.HasSat w B ∧
      ((algSat 2 (normV w) B).map fun b => X - C ((normV w : ℂ) ^ j * b)).prod = f.heckePoly (normV w)

def HolAll : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ π : TR.CuspSub ℚ 2, (∀ v, π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}) →
    ∀ H, Gk.IsHerm π H → ∃ φ ∈ π.V, φ ≠ 0 ∧ IsLow k φ

theorem holAll_of (h3 : HolVec) (h2 : HolTwo) (h0 : NoLow) : HolAll := by
  intro k hk π hπ H hH
  rcases hk.eq_or_lt with rfl | hk
  · obtain ⟨φ, hφ, hne, h | h⟩ := h2 π (fun v => by convert hπ v using 2 <;> norm_num) H hH
    · exact ⟨φ, hφ, hne, h⟩
    · exact absurd ⟨φ, hφ, hne, h⟩ (h0 π)
  · exact h3 k hk π hπ H hH

theorem newAE_of (hT : UnitTw) (hO : HermOf) (hH : HolAll) (hE : EigOfLow) (hS : SatHerm) (hP : EvPl) (hN : NewHerm) (hM : MinNew)
    (hC : Rs.CharEq2) : NewAE := by
  intro k hk j π hπ
  have hk1 : 1 ≤ k := by omega
  obtain ⟨π₀, hi, ht⟩ := hT k hk1 j π hπ
  obtain ⟨H, hH'⟩ := hO _ π₀ hi
  obtain ⟨N, _, χ, g, hg⟩ := hE k hk1 π₀ (hH k hk π₀ hi H hH')
  obtain ⟨f, _, h, hf, ha⟩ := hM N k hk1 χ g
  have hfa : ∀ n, f.a n = h.a n := fun n => by rw [Newform.a, Eigenform.a, hf]
  have ha' := (hP.1 _).2 ha
  have hc := (hP.1 _).2 (hC k N f.M hk1 χ f.χ g h ((hP.1 _).1 (by
    filter_upwards [hg, ha', hP.2 f.M f.pos] with w ⟨α, β, hs, h1, h2⟩ h3 h4
    refine ⟨h3, ?_, by simpa only [hfa] using hN k hk f w h4⟩
    rw [h1, ← h2, map_mul, Complex.conj_ofReal, mul_assoc, hS π₀ H hH' w α β hs])))
  refine ⟨f, ?_⟩
  filter_upwards [hg, ha', hc] with w ⟨α, β, hs, h1, h2⟩ h3 h4
  obtain ⟨t, h5, h6⟩ := ht w
  refine ⟨_, (h5 _).1 hs, ?_⟩
  rw [Newform.heckePoly, hfa, h3, h1, ← h4, ← h2, ← h6]
  simp

theorem repNewform_of (hA : NewAE) (hP : EvPl) (hI : PolyInj) (hpos : ∀ w : Pl ℚ, 0 < normV w) (hN : Published.NewformRep)
    (hS : Published.StrongMultOneReal) : Published.RepNewform := by
  intro k hk j π hπ
  obtain ⟨f, hf⟩ := hA k hk j π hπ
  obtain ⟨π', -, hs⟩ := hN k hk f j
  have hiso : π'.Iso π := hS ℚ 2 one_le_two π' π (by
    filter_upwards [hf, hP.2 f.M f.pos] with w ⟨B, hB, e⟩ hw
    obtain ⟨B', hB', e'⟩ := hs w hw
    obtain rfl := hI _ (hpos w) j B B' (e.trans e'.symm)
    exact ⟨B, hB', hB⟩)
  refine ⟨f, fun w hw => ?_⟩
  obtain ⟨B, hB, e⟩ := hs w hw
  exact ⟨B, hiso.hasSat hB, e⟩

end UpperTheory.V.Af.Rn
