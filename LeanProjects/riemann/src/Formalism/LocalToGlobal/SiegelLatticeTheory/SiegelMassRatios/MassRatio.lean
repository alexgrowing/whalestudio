import Mathlib
import Formalism.HermitianLattices.StatementMass

open NumberField

noncomputable section

namespace Formalism.L2.SG.MassRatio

section Defs

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def IsCMPair : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram E ∧ Set.range (algebraMap F E) = {a : E | star a = a}

def dF : ℝ := |((discr F : ℤ) : ℝ)|

def fF : ℕ := Module.finrank ℚ F

def vF : ℝ := dF F ^ ((1 : ℝ) / (fF F : ℝ)) / 2

def etaF (v : Ideal (𝓞 F)) : ℝ :=
  by classical exact
    if ∃! P : Ideal (𝓞 E), P.IsMaximal ∧ Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) P = v then -1 else 1

def eulerF (M : ℕ) (v : Ideal (𝓞 F)) : ℝ :=
  (1 - etaF F E v ^ M * ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)))⁻¹

def lText (M : ℕ) : ℝ :=
  ∏' v : {v : Ideal (𝓞 F) // v.IsMaximal}, eulerF F E M v.1

def rText (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vF F / Real.pi) ^ M) ^ fF F * dF F ^ (-(1 : ℝ) / 2) *
    lText F E M

end Defs

def MassRatio : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E →
    ∀ (M : ℕ), 3 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module E V] [Module (RingOfIntegers E) V]
      [IsScalarTower (RingOfIntegers E) E V] [AddCommGroup V'] [Module E V']
      [Module (RingOfIntegers E) V'] [IsScalarTower (RingOfIntegers E) E V']
      (h : V →ₗ⋆[E] V →ₗ[E] E) (h' : V' →ₗ⋆[E] V' →ₗ[E] E)
      (L : Submodule (RingOfIntegers E) V) (L' : Submodule (RingOfIntegers E) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L M → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (M - 1) →
      Formalism.HermitianLatticesTheory.mass h L / Formalism.HermitianLatticesTheory.mass h' L' = rText F E M

def DegEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → fF F = Formalism.HermitianLatticesTheory.fDeg E

def DiscSq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → |((discr E : ℤ) : ℝ)| = dF F ^ 2

def EulerEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ M : ℕ, 3 ≤ M → lText F E M = Formalism.HermitianLatticesTheory.lValEta E M

def FormsEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ M : ℕ, 3 ≤ M → rText F E M = Formalism.HermitianLatticesTheory.massRatioRightSide E M

theorem formsEq_of (hD : DegEq) (hS : DiscSq) (hL : EulerEq) : FormsEq := by
  intro F E _ _ _ _ _ _ hFE M hM
  have hf : fF F = Formalism.HermitianLatticesTheory.fDeg E := hD F E hFE
  have hd : |((discr E : ℤ) : ℝ)| = dF F ^ 2 := hS F E hFE
  have hl : lText F E M = Formalism.HermitianLatticesTheory.lValEta E M := hL F E hFE M hM
  have h0 : (0 : ℝ) ≤ dF F := abs_nonneg _
  have hfpos : 0 < fF F := Module.finrank_pos
  have hfR : (fF F : ℝ) ≠ 0 := by exact_mod_cast hfpos.ne'

  have hv : Formalism.HermitianLatticesTheory.vInv E = vF F := by
    unfold Formalism.HermitianLatticesTheory.vInv vF
    rw [hd, ← hf, ← Real.rpow_natCast (dF F) 2, ← Real.rpow_mul h0]
    congr 2
    push_cast
    field_simp

  have h2v : (2 * vF F) ^ fF F = dF F := by
    unfold vF
    rw [mul_div_cancel₀ _ (two_ne_zero), ← Real.rpow_natCast, ← Real.rpow_mul h0,
      one_div_mul_cancel hfR, Real.rpow_one]
  unfold rText Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [hv, ← hf, h2v, hl, Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2) by ring,
    Real.rpow_neg h0]
  ring

def fixSub (K : Type) [Field K] [StarRing K] : Subfield K where
  carrier := {a | star a = a}
  mul_mem' {a b} ha hb := by
    change star a = a at ha
    change star b = b at hb
    change star (a * b) = a * b
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' {a b} ha hb := by
    change star a = a at ha
    change star b = b at hb
    change star (a + b) = a + b
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  neg_mem' {a} ha := by
    change star a = a at ha
    change star (-a) = -a
    rw [star_neg, ha]
  inv_mem' a ha := by
    change star a = a at ha
    change star a⁻¹ = a⁻¹
    rw [star_inv₀, ha]

def fixFld (K : Type) [Field K] [NumberField K] [StarRing K] : IntermediateField ℚ K :=
  (fixSub K).toIntermediateField (fun q => by
    change star (algebraMap ℚ K q) = algebraMap ℚ K q
    rw [eq_ratCast, star_ratCast])

theorem massRatio_of_siegel (hE : FormsEq) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio) : MassRatio := by
  intro F E _ _ _ _ _ _ hFE M hM V V' _ _ _ _ _ _ _ _ h h' L L' hh hh' hL hL'
  rw [hE F E hFE M hM]
  exact hS E hFE.1 M hM V V' h h' L L' hh hh' hL hL'

end Formalism.L2.SG.MassRatio
