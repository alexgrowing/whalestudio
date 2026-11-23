import Formalism.SharpRestriction.LevelLetterCocycles.GammaSubCocycleComponent
import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem sigma_bound_le (l h η : ℕ) (hl : 11 ≤ l) :
    ((2 * S9.sigC l h η : ℕ) : ℝ) ≤ S9.ExtensionLemmaAlt.B2 l h η := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hx : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) + 1 := by
    have : 0 ≤ (((Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h : ℕ) : ℝ) + (η : ℝ)) / ((l : ℝ) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hc := Nat.ceil_lt_add_one hx
  unfold S9.ExtensionLemmaAlt.B2 Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig
  unfold S9.sigC
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  push_cast
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar at hc
  push_cast at hc
  linarith

theorem eta_le_parameter (l h η : ℕ) (hl : 2 ≤ l) (hη : η ≤ h) : η ≤ (l - 1) * Formalism.MainNotions.CrystallineLiftingInputs.Mpar l h := by
  unfold Formalism.MainNotions.CrystallineLiftingInputs.Mpar
  have := Nat.lt_mul_div_succ h (by omega : 0 < l - 1)
  omega

theorem jumps_bounds_of_set [NeZero n] (W : LocWach PD LL O v n) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) (hS : SetCS W d T₁ T₂ F b S η m) :
    (∀ i τ, Formalism.MainNotions.LiftingTheory.Over W τ i → JumpsInV PD T₂.ρ τ (Set.Ici (-((hpar n b S : ℕ) : ℤ)))) ∧
    ∀ (c' : ZMod n) τ, (c'.val + d) % 2 = 0 → Formalism.MainNotions.LiftingTheory.Over W τ (c' + 1) →
      JumpsInV PD T₂.ρ τ (Set.Ici (-(η : ℤ))) := by
  have hn : Even n := hS.2.2.1
  have hwin : ∀ i a, a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η i → -((hpar n b S : ℕ) : ℤ) ≤ a := by
    intro i a ha
    have hbi : b i ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ i)
    have hη := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    unfold hpar
    split_ifs at ha <;> simp only [Set.mem_union, Set.mem_Icc] at ha <;> push_cast at ha ⊢ <;> omega
  have hwinU : ∀ c' : ZMod n, (c'.val + d) % 2 = 0 → ∀ a,
      a ∈ Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS d b S η (c' + 1) → -(η : ℤ) ≤ a := by
    intro c' hc' a ha
    have hpar' := S9.parity_succ hn d c'
    unfold Formalism.MainNotions.RamifiedCoefficientChains.JumpWinS at ha
    rw [if_neg (by omega)] at ha
    simp only [Set.mem_union, Set.mem_Icc] at ha
    push_cast at ha
    omega
  exact ⟨fun i τ hτ a ha => hwin i a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS i τ hτ a ha),
    fun c' τ hc' hτ a ha => hwinU c' hc' a (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hEx hCs hDq hS (c' + 1) τ hτ a ha)⟩

theorem difference_of_factorisations {M' : Type} [AddCommGroup M'] [Module O M'] {R : Type} [CommRing R] [Module R M']
    [SMulCommClass O R M'] (f0 : R) (l : O) (φw tw t₁ t' t p₁ p₂ p₃ : M')
    (etw : tw - ((1 : O) • t₁ + (-l) • t') = f0 • p₁) (e₂ : t₁ = f0 • p₂) (e₃ : t - t' = f0 • p₃) :
    (l • φw - tw) - l • (φw + t) = f0 • (-(p₁ + p₂ + l • p₃)) := by
  have et' : t' = t - f0 • p₃ := by rw [← e₃]; abel
  have etw' : tw = f0 • p₁ + ((1 : O) • t₁ + (-l) • t') := by rw [← etw]; abel
  rw [etw', e₂, et']
  simp only [one_smul, neg_smul, smul_sub, smul_add, smul_neg]
  rw [smul_comm l f0 p₃]
  abel

theorem pow_smul_cocycle_sub_sum_mem_latticeCoboundaries (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (ev : Finset (ZMod n))
    (xc : ZMod n → ↥(W.wachCocyclesDelta T)) (κ : ZMod n → G → T.V) (hκ : ∀ c, κ c ∈ latticeCocycles T.L)
    (hP : ∀ c ∈ ev, W.clK T (xc c) = Submodule.Quotient.mk ⟨κ c, hκ c⟩)
    (x0 : ↥(W.wachCocyclesDelta T)) (gf : G → T.V) (hgf : gf ∈ latticeCocycles T.L)
    (hcl0 : W.clK T x0 = Submodule.Quotient.mk ⟨gf, hgf⟩) (e : ℕ)
    (hcls : ∑ c ∈ ev, W.clK T (xc c) = ((PD.p : ℕ) : O) ^ e • W.clK T x0) :
    (PD.p : O) ^ e • gf - ∑ c ∈ ev, κ c ∈ latticeCoboundaries T.L := by
  let Ks : ↥(latticeCocycles T.L) := ∑ c ∈ ev, ⟨κ c, hκ c⟩
  have hK : (Submodule.Quotient.mk Ks : LatticeCohomology T.L) = ∑ c ∈ ev, W.clK T (xc c) := by
    calc (Submodule.Quotient.mk Ks : LatticeCohomology T.L)
        = ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ Ks := rfl
      _ = ∑ c ∈ ev, ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype).mkQ ⟨κ c, hκ c⟩ := map_sum _ _ _
      _ = ∑ c ∈ ev, W.clK T (xc c) := Finset.sum_congr rfl fun c hc => (hP c hc).symm
  have hgf0 : (Submodule.Quotient.mk (((PD.p : ℕ) : O) ^ e • (⟨gf, hgf⟩ : ↥(latticeCocycles T.L)) - Ks) :
      LatticeCohomology T.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, hK, hcls, hcl0, sub_self]
  have hmem := (Submodule.Quotient.mk_eq_zero _).1 hgf0
  rw [Submodule.mem_comap] at hmem
  simpa [Ks, Submodule.coe_sum] using hmem

section Fam

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letterIdempotentMap (i : ZMod n) : W.DD T →ₗ[O] W.DD T where
  toFun x := (letE i : LetA O n) • x
  map_add' x y := smul_add _ x y
  map_smul' r x := Formalism.MainNotions.N.Pv.LocalLengthBound.osmul_comm W T (letE i) r x

@[simp] theorem letterIdempotentMap_apply (i : ZMod n) (x : W.DD T) :
    letterIdempotentMap W T i x = (letE i : LetA O n) • x := rfl

variable {W T}

theorem frobenius_lift_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1) =
      ((PD.p : ℕ) : O) ^ σ • W.φD T (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • yv) +
          W.φD T (μ c) - μ (c + 1)) - ((PD.p : ℕ) : O) ^ N • t c := by
  unfold liftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem gamma_difference_identity (N s₁ σ : ℕ) (yv zv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    W.γ T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) -
      (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1)) =
      ((PD.p : ℕ) : O) ^ N • gammaDefectOfLiftCorrection W T s₁ σ yv zv ms t c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE (c + 1) : LetA O n) • zv) +
          (W.γ T (μ (c + 1)) - μ (c + 1))) := by
  unfold gammaDefectOfLiftCorrection
  simp only [map_sub, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

theorem frobenius_difference_identity (N s₁ σ : ℕ) (yv : W.DD T) (ms t μ : ZMod n → W.DD T) (c : ZMod n) :
    ((PD.p : ℕ) : O) ^ N • frobeniusShiftDefectOfLiftCorrection W T s₁ σ yv ms t c =
      W.φD T (((PD.p : ℕ) : O) ^ N • liftCorrection W T s₁ σ yv ms t (c - 2) -
          ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c - 1)) -
        ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE c : LetA O n) • yv) +
          W.φD T (μ (c - 1)) - μ c) := by
  unfold frobeniusShiftDefectOfLiftCorrection
  simp only [map_sub, map_add, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
  simp only [add_comm, add_left_comm, add_assoc]
  abel

end Fam

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2A

end
