import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowPartStable

variable {D : D7}

theorem sphericalOperator_commute_levelFiniteGroup (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (P : Pl D.host.E) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) {d : List ℤ} {B : Finset (GA D V)}
    (hS : GlobalTheory.Hk3.SphOp V P d B) (g0 : G0 L.Pg L.r) (Φ : GA D V → ℂ) (hΦ : ∀ k ∈ GlobalTheory.Hk3.hyp V P, ∀ h, Φ (h * k) = Φ h) :
    actG0 V β L g0 (heckeLin V B Φ) = heckeLin V B (actG0 V β L g0 Φ) := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  obtain ⟨hJ', -, hs'⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hP hN hPP
  unfold actG0
  split_ifs with hex
  · have hl := hex.choose_spec
    generalize hex.choose = κ at hl ⊢
    have hκ : κ ∈ levG V β (flagL L) := ⟨hl.1, hl.2.1, Subgroup.mem_top _⟩
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hs' κ hκ
    have e1 : (fun x => (levChi V β (flagL L) (k₁ * k₂))⁻¹ * Φ (x * (k₁ * k₂))) =
      (levChi V β (flagL L) (k₁ * k₂))⁻¹ • fun x => Φ (x * (k₁ * k₂)) := rfl
    rw [e1, LinearMap.map_smul]
    funext h
    rw [GlobalTheory.LevOp.heckeLin_translate hP hJ' hS hΦ hk₁ s₁ s₂]
    rfl
  · rw [LinearMap.map_zero]

theorem mult_lev {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    {U : MMap M} (hU : U ∈ Mult θ M J χ) (v : M.Vec) (k : GA D V) (hk : k ∈ J) (g : GA D V) : U v (g * k) = χ k * U v g := by
  induction hU using Submodule.span_induction with
  | mem U hU => exact hU.lev v k hk g
  | zero => simp
  | add U U' _ _ h h' => simp [h, h', mul_add]
  | smul a U _ h => simp [h, mul_left_comm]

theorem map_gE_le : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, Core R F → ∀ SF, IsSF R SF → ∀ c g, (EEc R SF c).map (R.gE g) ≤ EEc R SF c := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hC SF hSF c g
  rintro _ ⟨x, hx, rfl⟩
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    intro y
    have h : R.HE.e y ∈ R.EEat R.triv := hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y
    exact goodPart_le _ _ _ _ _ h
  have hx' := ((mem_partFull R.θ (R.MY 0) _ _ SF _ _).1 hx).2
  refine (mem_partFull R.θ (R.MY 0) _ _ SF _ _).2 ⟨hmem _, fun P d B hB v => ?_⟩
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hO : OffS D SF P := by
    obtain ⟨e, f, ϖ, α, h, -⟩ := hB
    exact h
  have hG : Good R A.μ0 P := (hoff SF hSF P).1 hO
  obtain ⟨n, hn⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hN : (((D.host.g 0 * D.host.g 1) ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_pow]
    exact fun h => (hgood _ P hG).1 (P.isPrime.mem_of_pow_mem n h)
  have hPP : ∀ PP, PP ∈ (R.dat0 R.triv).Pg ∨ PP ∈ (R.dat0 R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    rcases hPP with hPP | hPP
    · exact hG PP (Or.inl hPP)
    · exact absurd hPP (Finset.notMem_empty _)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.LevOp.level_operators (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP
  have hS := ((h2 SF d B).1 hB).2
  have hfix : ∀ y, ∀ k ∈ GlobalTheory.Hk3.hyp (Yc D 0) P, ∀ h, R.HE.e y v (h * k) = R.HE.e y v h := by
    intro y k hk h
    rw [mult_lev _ _ _ _ (hmem y) v k (h1 k hk).1 h, (h1 k hk).2, one_mul]
  have hact : R.HE.e (R.gE g x) v = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.HE.e x v) := by
    rw [hC.models.gE g x]; rfl
  have hcomm := sphericalOperator_commute_levelFiniteGroup (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hn P hN hPP hS (R.eG g) (R.HE.e x v) (hfix x)
  rw [hx' P d B hB v] at hcomm
  rw [hact]
  exact hcomm.symm.trans ((actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g)).map_smul _ _)

end GlobalTheory.RowPartStable

end
