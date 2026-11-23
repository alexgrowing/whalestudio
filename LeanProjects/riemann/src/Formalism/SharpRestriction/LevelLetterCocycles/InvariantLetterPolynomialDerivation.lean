import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Op

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def uniformizerInverse : W.EE := Ring.inverse (algebraMap (LetA O n) W.EE W.π₀)

def derivationOnWachModule : W.DD T →ₗ[O] W.DD T := Formalism.MainNotions.LiftingTheory.lifta_δ W T (uniformizerInverse W)

theorem derivation_on_wach_module_apply (x : W.DD T) : derivationOnWachModule W T x = uniformizerInverse W • (W.γ T x - x) := rfl

variable {W} in
theorem algebraMap_uniformizer_mul_inverse (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) :
    algebraMap (LetA O n) W.EE W.π₀ * uniformizerInverse W = 1 :=
  Ring.mul_inverse_cancel _ hU

theorem uniformizer_smul_derivation (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    W.π₀ • derivationOnWachModule W T x = W.γ T x - x := by
  rw [derivation_on_wach_module_apply, ← smul_assoc, Algebra.smul_def, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem inverse_smul_uniformizer_smul (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (x : W.DD T) :
    uniformizerInverse W • (W.π₀ • x) = x := by
  rw [← algebraMap_smul W.EE W.π₀ x, smul_smul, mul_comm, algebraMap_uniformizer_mul_inverse hU, one_smul]

theorem smul_comm_letA_EE (a : LetA O n) (e : W.EE) (x : W.DD T) : a • (e • x) = e • (a • x) := by
  rw [← smul_assoc a e x, Algebra.smul_def a e, mul_comm, mul_smul, algebraMap_smul W.EE a x]

theorem gammaA_idempotent (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((Pi.single c (1 : PowerSeries O) : LetA O n) i) = (Pi.single c (1 : PowerSeries O) : LetA O n) i
  rw [Pi.single_apply]
  split_ifs <;> simp

theorem idempotent_smul_gamma (c : ZMod n) (x : W.DD T) :
    (letE c : LetA O n) • W.γ T x = W.γ T ((letE c : LetA O n) • x) := by
  show (letE c : LetA O n) • W.γD T W.gam x = W.γD T W.gam ((letE c : LetA O n) • x)
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext,
    show letγ (W.γ₀ W.gam) (letE c : LetA O n) = letE c from gammaA_idempotent W W.gam c, algebraMap_smul]

theorem gammaD_gamma_comm (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.γ T x) = W.γ T (W.γD T δ x) := by
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam (W.γD T δ x)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem delta_fixes_inverse (a : LetA O n) (ha : a ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE a))
    (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γE δ (Ring.inverse (algebraMap (LetA O n) W.EE a)) = Ring.inverse (algebraMap (LetA O n) W.EE a) := by
  have ha' : ∀ δ ∈ W.DelF, W.γA δ a = a := ha
  have hfix : W.γE δ (algebraMap (LetA O n) W.EE a) = algebraMap (LetA O n) W.EE a := by
    rw [W.γE_ext]
    exact congrArg (algebraMap (LetA O n) W.EE) (ha' δ hδ)
  obtain ⟨u, hu⟩ := hU
  rw [← hu] at hfix ⊢
  rw [Ring.inverse_unit]
  have h1 : (u : W.EE) * W.γE δ ↑u⁻¹ = 1 := by
    rw [← hfix, ← map_mul, Units.mul_inv, map_one]
  exact (Units.inv_eq_of_mul_eq_one_right h1).symm

theorem invariantLetter_fixed_smul {c : ZMod n} (e : W.EE) (he : ∀ δ ∈ W.DelF, W.γE δ e = e) {x : W.DD T}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (e • x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_comm_letA_EE, h.1]
  · rw [W.γD_smul, he δ hδ, h.2 δ hδ]

theorem invariantLetter_gamma_sub {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (W.γ T x - x) := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [smul_sub, idempotent_smul_gamma, h.1]
  · rw [map_sub, gammaD_gamma_comm, h.2 δ hδ]

theorem invariantLetter_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (derivationOnWachModule W T x) := by
  rw [derivation_on_wach_module_apply]
  exact invariantLetter_fixed_smul W T (uniformizerInverse W)
    (fun δ hδ => delta_fixes_inverse W W.π₀ hπΔ hU δ hδ) (invariantLetter_gamma_sub W T h)

theorem invariantLetter_derivation_pow (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (k : ℕ) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c ((derivationOnWachModule W T ^ k) x) := by
  induction k with
  | zero => rw [pow_zero, Module.End.one_apply]; exact h
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact invariantLetter_derivation W T hπΔ hU ih

theorem invariantLetter_polynomial_derivation (hπΔ : W.π₀ ∈ W.AΔ) (hU : IsUnit (algebraMap (LetA O n) W.EE W.π₀))
    {c : ZMod n} (P : Polynomial O) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact ⟨by rw [smul_add, hp.1, hq.1], fun δ hδ => by rw [map_add, hp.2 δ hδ, hq.2 δ hδ]⟩
  next k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    have hk := invariantLetter_derivation_pow W T hπΔ hU k h
    exact ⟨by rw [smul_comm _ a, hk.1], fun δ hδ => by rw [map_smul, hk.2 δ hδ]⟩

def DerivationPreservesQLattice [NeZero n] : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (i : ZMod n) (k : ℤ) (x : W.DD T),
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k x → Formalism.MainNotions.CrystallineLiftingInputs.InQN W T i k (Formalism.MainNotions.CrystallineLiftingInputs.dOp W T x)

def QLattice (c : ZMod n) (k : ℕ) (x : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x ∧ Formalism.MainNotions.LiftingTheory.qp W ^ k • x ∈ W.N T

theorem qLattice_iff (c : ZMod n) (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.CrystallineLiftingInputs.InQN W T c (k : ℤ) x ↔ QLattice W T c k x := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.InQN QLattice
  simp

theorem qLattice_add {c : ZMod n} {k : ℕ} {x y : W.DD T} (hx : QLattice W T c k x)
    (hy : QLattice W T c k y) : QLattice W T c k (x + y) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_add, hx.1.1, hy.1.1]
  · rw [map_add, hx.1.2 δ hδ, hy.1.2 δ hδ]
  · rw [smul_add]
    exact add_mem hx.2 hy.2

theorem qLattice_smul {c : ZMod n} {k : ℕ} (a : O) {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k (a • x) := by
  refine ⟨⟨?_, fun δ hδ => ?_⟩, ?_⟩
  · rw [smul_comm _ a, hx.1.1]
  · rw [map_smul, hx.1.2 δ hδ]
  · rw [smul_comm _ a, ← algebraMap_smul (LetA O n) a]
    exact Submodule.smul_mem _ _ hx.2

theorem qLattice_mono {c : ZMod n} {k k' : ℕ} (hk : k ≤ k') {x : W.DD T} (hx : QLattice W T c k x) :
    QLattice W T c k' x := by
  refine ⟨hx.1, ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hx.2

theorem qLattice_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    {x : W.DD T} (h : QLattice W T c k x) : QLattice W T c k (derivationOnWachModule W T x) := by
  rw [← qLattice_iff] at h ⊢
  rw [derivation_on_wach_module_apply]
  exact hDS hA T hT c (k : ℤ) x h

theorem qLattice_polynomial_derivation [NeZero n] (hDS : DerivationPreservesQLattice W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hT : IsCrys PD T.ρ) (c : ZMod n) (k : ℕ)
    (P : Polynomial O) {x : W.DD T} (h : QLattice W T c k x) :
    QLattice W T c k (Polynomial.aeval (derivationOnWachModule W T) P x) := by
  have hpow : ∀ j : ℕ, QLattice W T c k ((derivationOnWachModule W T ^ j) x) := by
    intro j
    induction j with
    | zero => rw [pow_zero, Module.End.one_apply]; exact h
    | succ j ih => rw [pow_succ', Module.End.mul_apply]; exact qLattice_derivation W T hDS hA hT c k ih
  induction P using Polynomial.induction_on'
  next p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact qLattice_add W T hp hq
  next j a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact qLattice_smul W T a (hpow j)

end Op

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
