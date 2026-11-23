import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_natCast (m k : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ZMod m).val : ℕ) : ℂ) / (m : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_natCast]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk : 2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((k % m : ℕ) : ℂ) / (m : ℂ) + ((k / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    push_cast
    field_simp
  rw [hk, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_of_isRoot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f →
    IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ n x f a b hx hr
  obtain ⟨G1, -, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨M1, -, -, M4, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨ha, hb, hb0, hab0⟩ := hr
  have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  obtain ⟨M, hM, hlev⟩ := X.level (f : X.K)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (f : X.K)) (fun φ => ⟨φ, rfl⟩)
  have hab : (φ : Mero) * (b : Mero) ^ (l ^ n) = (a : Mero) ^ (l ^ n) := by rw [← hφ]; exact hab0
  have key : ∀ δ ∈ CongruenceSubgroup.Gamma M, ∃ k : ℕ, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) * (a z * b (mob (ofSL δ) z)) := by
    intro δ hδ
    have hφg : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = (φ : Mero) := by
      rw [← X.an_sl (ofSL δ) (f : X.K) φ hφ, hlev δ hδ, hφ]
    have dag : DifferentiableOn ℂ (fun z => a (mob (ofSL δ) z)) Hs :=
      ha.comp (M4 _) (fun z hz => M1 _ z hz)
    have dbg : DifferentiableOn ℂ (fun z => b (mob (ofSL δ) z)) Hs :=
      hb.comp (M4 _) (fun z hz => M1 _ z hz)
    have h1 : ((φ * b ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab
    have h2 : (((fun z => φ (mob (ofSL δ) z)) * (fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((fun z => a (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := G3 (ofSL δ) _ _ h1
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, hφg] at h2
    have h3 : ((((fun z => a (mob (ofSL δ) z)) * b) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((a * fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Filter.Germ.coe_mul, Filter.Germ.coe_mul]
      linear_combination (-(b : Mero) ^ (l ^ n)) * h2 +
        ((fun z => b (mob (ofSL δ) z) : ℂ → ℂ) : Mero) ^ (l ^ n) * hab
    have h4 := (G1 _ _ ((dag.mul hb).pow _) ((ha.mul dbg).pow _)).1 h3
    obtain ⟨k, hk⟩ := G5 (l ^ n) ((fun z => a (mob (ofSL δ) z)) * b) (a * fun z => b (mob (ofSL δ) z)) hm
      (dag.mul hb) (ha.mul dbg) h4
    exact ⟨k, hk⟩
  classical
  let χ : SL(2, ℤ) → ZMod (l ^ n) := fun δ =>
    if h : δ ∈ CongruenceSubgroup.Gamma M then ((key δ h).choose : ZMod (l ^ n)) else 0
  refine ⟨χ, f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab0⟩, fun δ hδ z hz => ?_⟩
  have hc : ((l : ℂ) ^ n) = ((l ^ n : ℕ) : ℂ) := by push_cast; rfl
  simp only [χ, dif_pos hδ]
  rw [hc, exp_val_natCast (l ^ n) _ hm]
  exact (key δ hδ).choose_spec z hz

end GlobalTheory.KZ.H3
