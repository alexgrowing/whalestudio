import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def combLine {σ : Type} [Fintype σ] (A : σ → HermLine ι) (n : σ → ℤ) : HermLine ι where
  a := fun k => ∑ x, n x * (A x).a k
  h z := ∏ x, (A x).h z ^ n x
  pos z hz := Finset.prod_pos fun x _ => zpow_pos ((A x).pos z hz) _
  smul c z hc := by
    have h0 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have h1 : ∀ k, ‖c k‖ ^ (∑ x, n x * (A x).a k) = ∏ x, (‖c k‖ ^ (A x).a k) ^ n x := by
      intro k
      classical
      induction (Finset.univ : Finset σ) using Finset.induction_on with
      | empty => simp
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add₀ (h0 k), ih, ← zpow_mul, mul_comm (n x)]
    simp only [fun x => (A x).smul c z hc, mul_zpow, Finset.prod_mul_distrib, h1]
    rw [Finset.prod_comm]
    simp only [Finset.prod_zpow]

theorem combLine_eq_top {σ : Type} [Fintype σ] (A : σ → HermLine ι) (n : σ → ℤ) :
    combLine A n = GlobalTheory.CompanionTheory.Ar.Top.combLine A n := by
  unfold combLine GlobalTheory.CompanionTheory.Ar.Top.combLine
  congr 1
  funext k
  simp [Finset.sum_apply]

theorem combLine_a {σ : Type} [Fintype σ] (A : σ → HermLine ι) (n : σ → ℤ) (k : K) :
    (combLine A n).a k = ∑ x, n x * (A x).a k := rfl

theorem combLine_h {σ : Type} [Fintype σ] (A : σ → HermLine ι) (n : σ → ℤ) (z : (Σ k, ι k) → ℂ) :
    (combLine A n).h z = ∏ x, (A x).h z ^ n x := rfl

theorem combLine_div (A B : HermLine ι) :
    (combLine ![A, B] ![1, -1]).a = A.a - B.a ∧ ∀ z, (combLine ![A, B] ![1, -1]).h z = A.h z / B.h z :=
  ⟨funext fun k => by simp [combLine_a, sub_eq_add_neg], fun z => by simp [combLine_h, div_eq_mul_inv]⟩

namespace AnSys

variable {e : ℕ} {σ : Type} (S : AnSys e σ)

def nComp : ℕ := Nat.card (ConnectedComponents S.X)

def degNumDe (w : Fin e → σ) : ℝ := S.degNum w / S.nComp

def degPolyDe [Fintype σ] : MvPolynomial σ ℝ := formPoly e S.degNumDe

theorem finite_components : Finite (ConnectedComponents S.X) := by
  let _ : ChartedSpace (Fin e → ℂ) S.X :=
    { atlas := Set.range S.A.chart
      chartAt := fun x => S.A.chart (S.A.cover x).choose
      mem_chart_source := fun x => (S.A.cover x).choose_spec
      chart_mem_atlas := fun _ => ⟨_, rfl⟩ }
  have := ChartedSpace.locallyConnectedSpace (Fin e → ℂ) S.X
  infer_instance

theorem nComp_pos [Nonempty S.X] : 0 < S.nComp := by
  have := S.finite_components
  exact Nat.card_pos

theorem nComp_eq_one [ConnectedSpace S.X] : S.nComp = 1 :=
  Nat.card_unique

theorem nComp_comap {σ' : Type} (f : σ' → σ) : (S.comap f).nComp = S.nComp := rfl

end AnSys

theorem formPoly_const_mul {σ : Type} [Fintype σ] (n : ℕ) (c : ℝ) (a : (Fin n → σ) → ℝ) :
    formPoly n (fun w => c * a w) = c • formPoly n a := by
  simp only [formPoly, Finset.smul_sum, map_mul, smul_eq_C_mul, mul_assoc]

theorem AnSys.degPoly_eq {e : ℕ} {σ : Type} [Fintype σ] (S : AnSys e σ) [Nonempty S.X] :
    S.degPoly = (S.nComp : ℝ) • S.degPolyDe := by
  have h : (S.nComp : ℝ) ≠ 0 := Nat.cast_ne_zero.2 S.nComp_pos.ne'
  rw [AnSys.degPolyDe, ← formPoly_const_mul, AnSys.degPoly]
  congr 1
  funext w
  rw [AnSys.degNumDe, mul_div_cancel₀ _ h]

structure Realis {D : ℕ} {σ : Type} (S : AnSys D σ) (P : Ideal (MRing ι)) where
  arith : IsArithVar P (D + 1)

  J : Ideal (MRing ι)

  R : AnLogRes P J D

  π : R.X → S.X
  holo : HoloMap R.A S.A π

  deg : ℕ
  deg_pos : 0 < deg

  br : Set S.X
  degree : IsDegreeOff S.A R.A π deg br

  ref : σ → HermLine ι
  ref_smooth : ∀ a, IsSmoothHerm (ref a)
  ref_pot : ∀ a, SamePot R.A Set.univ (potOf R (ref a)) ((S.th a).pullback π holo.1)

  line : σ → ℝ → HermLine ι
  line_deg : ∀ a t, (line a t).a = (ref a).a
  line_smooth : ∀ a t, 0 < t → t ≤ S.t₀ → IsSmoothHerm (line a t)
  line_eq : ∀ a t, 0 < t → t ≤ S.t₀ → ∀ x,
    Real.log ((line a t).h (R.lift x x)) = Real.log ((ref a).h (R.lift x x)) + S.phT a t (π x)

namespace Realis

variable {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (II : IntersectionSystem)

def num (t : ℝ) (w : Fin (D + 1) → σ) : ℝ :=
  II K ι P (D + 1) (fun j => Re.line (w j) t) / Re.deg

def limNum (w : Fin (D + 1) → σ) : ℝ := limUnder (𝓝[>] 0) fun t => Re.num II t w

def FT [Fintype σ] (t : ℝ) : MvPolynomial σ ℝ := formPoly (D + 1) (Re.num II t)

def PB [Fintype σ] : MvPolynomial σ ℝ := formPoly (D + 1) (Re.limNum II)

def de : ℕ := S.nComp * Re.deg

def numDe (t : ℝ) (w : Fin (D + 1) → σ) : ℝ :=
  II K ι P (D + 1) (fun j => Re.line (w j) t) / Re.de

def limNumDe (w : Fin (D + 1) → σ) : ℝ := Re.limNum II w / S.nComp

def FTDe [Fintype σ] (t : ℝ) : MvPolynomial σ ℝ := formPoly (D + 1) (Re.numDe II t)

def PBDe [Fintype σ] : MvPolynomial σ ℝ := formPoly (D + 1) (Re.limNumDe II)

include Re in

theorem nonempty_base : Nonempty S.X := by
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts Re.arith Re.R.nondeg
  obtain ⟨x, -⟩ := Re.R.surj z hz hJ
  exact ⟨Re.π x⟩

include Re in

theorem nComp_pos : 0 < S.nComp :=
  haveI := Re.nonempty_base
  S.nComp_pos

theorem de_pos : 0 < Re.de := Nat.mul_pos Re.nComp_pos Re.deg_pos

theorem numDe_eq (t : ℝ) (w : Fin (D + 1) → σ) : Re.numDe II t w = Re.num II t w / S.nComp := by
  rw [numDe, num, de, Nat.cast_mul, div_div, mul_comm]

theorem num_eq (t : ℝ) (w : Fin (D + 1) → σ) : Re.num II t w = S.nComp * Re.numDe II t w := by
  rw [numDe_eq, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 Re.nComp_pos.ne')]

theorem limNum_eq (w : Fin (D + 1) → σ) : Re.limNum II w = S.nComp * Re.limNumDe II w := by
  rw [limNumDe, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 Re.nComp_pos.ne')]

theorem tendsto_numDe_iff (w : Fin (D + 1) → σ) :
    Tendsto (fun t => Re.numDe II t w) (𝓝[>] 0) (𝓝 (Re.limNumDe II w)) ↔
      Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (Re.limNum II w)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [num_eq, limNum_eq]
    exact h.const_mul _
  · simp only [numDe_eq, limNumDe]
    exact h.div_const _

theorem limNumDe_eq_of_tendsto {w : Fin (D + 1) → σ} {L : ℝ}
    (h : Tendsto (fun t => Re.numDe II t w) (𝓝[>] 0) (𝓝 L)) : Re.limNumDe II w = L := by
  have h1 : Tendsto (fun t => Re.num II t w) (𝓝[>] 0) (𝓝 (S.nComp * L)) := by
    simp only [num_eq]
    exact h.const_mul _
  rw [limNumDe, limNum, h1.limUnder_eq, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 Re.nComp_pos.ne')]

theorem FT_eq [Fintype σ] (t : ℝ) : Re.FT II t = (S.nComp : ℝ) • Re.FTDe II t := by
  rw [FTDe, ← formPoly_const_mul, FT]
  congr 1
  funext w
  exact Re.num_eq II t w

theorem PB_eq [Fintype σ] : Re.PB II = (S.nComp : ℝ) • Re.PBDe II := by
  rw [PBDe, ← formPoly_const_mul, PB]
  congr 1
  funext w
  exact Re.limNum_eq II w

theorem PBDe_of_connected [Fintype σ] [ConnectedSpace S.X] :
    Re.de = Re.deg ∧ Re.PBDe II = Re.PB II ∧ ∀ t, Re.FTDe II t = Re.FT II t := by
  simp [de, PB_eq, FT_eq, S.nComp_eq_one]

def comap {σ' : Type} (f : σ' → σ) : Realis (S.comap f) P where
  arith := Re.arith
  J := Re.J
  R := Re.R
  π := Re.π
  holo := Re.holo
  deg := Re.deg
  deg_pos := Re.deg_pos
  br := Re.br
  degree := Re.degree
  ref a := Re.ref (f a)
  ref_smooth a := Re.ref_smooth (f a)
  ref_pot a := Re.ref_pot (f a)
  line a := Re.line (f a)
  line_deg a := Re.line_deg (f a)
  line_smooth a := Re.line_smooth (f a)
  line_eq a := Re.line_eq (f a)

theorem de_comap {σ' : Type} (f : σ' → σ) : (Re.comap f).de = Re.de := rfl

theorem numDe_comap {σ' : Type} (f : σ' → σ) (t : ℝ) (w : Fin (D + 1) → σ') :
    (Re.comap f).numDe II t w = Re.numDe II t (f ∘ w) := rfl

theorem limNumDe_comap {σ' : Type} (f : σ' → σ) (w : Fin (D + 1) → σ') :
    (Re.comap f).limNumDe II w = Re.limNumDe II (f ∘ w) := rfl

end Realis

section Weights

variable {D N : ℕ} {Ψ : Type} [Fintype Ψ] {S : AnSys D (Option (Ψ × Fin N))} {P : Ideal (MRing ι)}
  (Re : Realis S P) (II : IntersectionSystem)

def Realis.PBs : MvPolynomial (Option (Ψ × Fin N)) ℝ := toWtS (Re.PB II)

def Realis.PBwt : MvPolynomial (Ψ × Fin N) ℝ := toWt ((Re.comap some).PB II)

def scaleS {τ : Type} (k : ℕ) : MvPolynomial (Option τ) ℝ →ₐ[ℝ] MvPolynomial (Option τ) ℝ :=
  aeval fun o : Option τ => o.elim (C (k : ℝ)⁻¹ * X none) fun p => X (some p)

def Realis.PBsDe (k : ℕ) : MvPolynomial (Option (Ψ × Fin N)) ℝ := scaleS k (toWtS (Re.PBDe II))

def Realis.PBwtDe : MvPolynomial (Ψ × Fin N) ℝ := toWt ((Re.comap some).PBDe II)

theorem eval_scaleS {τ : Type} (k : ℕ) (Q : MvPolynomial (Option τ) ℝ) (lam : τ → ℝ) (s : ℝ) :
    eval (fun o : Option τ => o.elim s lam) (scaleS k Q) = eval (fun o : Option τ => o.elim (s / k) lam) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [scaleS]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p o hp =>
    simp only [map_mul, hp, eval_X]
    congr 1
    cases o <;> simp [scaleS, div_eq_inv_mul]

theorem Realis.PBwt_eq : Re.PBwt II = (S.nComp : ℝ) • Re.PBwtDe II := by
  rw [Realis.PBwt, Realis.PB_eq, map_smul]
  rfl

theorem Realis.scaleS_PBs (k : ℕ) : scaleS k (Re.PBs II) = (S.nComp : ℝ) • Re.PBsDe II k := by
  rw [Realis.PBs, Realis.PB_eq, map_smul, map_smul]
  rfl

theorem Realis.eval_PBsDe (k : ℕ) (lam : Ψ × Fin N → ℝ) (s : ℝ) :
    eval (fun o => o.elim s lam) (Re.PBsDe II k) = eval (fun o => o.elim (s / k) lam) (Re.PBs II) / S.nComp := by
  have h : (S.nComp : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.nComp_pos.ne'
  rw [← eval_scaleS, Realis.scaleS_PBs, smul_eval, mul_div_cancel_left₀ _ h]

end Weights

def NefAt (P : Ideal (MRing ι)) (p : ℕ) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W = p →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → 0 ≤ geoNum 1 W fun _ => a

theorem prime_charOf_of_ne_zero {W : Ideal (MRing ι)} (hW : W.IsPrime) (h : charOf W ≠ 0) : (charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have h0 : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ≠ 0 := fun e => h (by simp [charOf, e])
  rw [← Ideal.span_singleton_generator (W.comap (C : ℤ →+* MRing ι)), Ideal.span_singleton_prime h0] at hI
  exact Int.prime_iff_natAbs_prime.1 hI

theorem nefOnFibres_iff_nefAt (P : Ideal (MRing ι)) (a : K → ℤ) :
    NefOnFibres P a ↔ ∀ p : ℕ, p.Prime → NefAt P p a :=
  ⟨fun h p hp W h1 h2 h3 h4 => h W h1 h2 (h3 ▸ hp.ne_zero) h4,
    fun h W h1 h2 h3 h4 => h _ (prime_charOf_of_ne_zero h1.1 h3) W h1 h2 rfl h4⟩

def VertClose (P : Ideal (MRing ι)) (T : Finset ℕ) (α : ℕ → ℝ) (A B : HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (df dg : K → ℕ), IsMultiHomog f df ∧ IsMultiHomog g dg ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (df k : ℤ) - dg k = A.a k - B.a k) ∧
    (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) ∧
    (∀ W, charOf W ∉ T → divCycle P f W = divCycle P g W) ∧
    ∀ W, charOf W ∈ T →
      |(divCycle P f W : ℝ) - divCycle P g W| ≤ α (charOf W) * divCycle P (C (charOf W : ℤ)) W

theorem VertClose.symm {P : Ideal (MRing ι)} {T : Finset ℕ} {α : ℕ → ℝ} {A B : HermLine ι}
    (h : VertClose P T α A B) : VertClose P T α B A := by
  obtain ⟨f, g, df, dg, hf, hg, hfP, hgP, hd, hn, h1, h2⟩ := h
  refine ⟨g, f, dg, df, hg, hf, hgP, hfP, fun k => by linarith [hd k], fun z hz => (hn z hz).symm,
    fun W hW => (h1 W hW).symm, fun W hW => ?_⟩
  rw [abs_sub_comm]
  exact h2 W hW

def Inputs : Prop :=
  (ConvergenceStatement ∧ ConvergenceSignedStatement ∧ ConvergenceRateStatement ∧ UnifIntStatement ∧
    PullbackStatement ∧ RegGlobalStatement) ∧
  (ResExistsStatement ∧ ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement ∧ ArithmeticIntersectionNonneg) ∧
  (ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement) ∧
  (ReciprocityTheory.ChartRestriction.G.AI.I4.PFStatement ∧ ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement ∧
    ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) ∧
  (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg ∧ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement ∧
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.SiuZStatement)

namespace Inputs

theorem convergence (h : Inputs) : ConvergenceStatement := h.1.1

theorem convergenceSigned (h : Inputs) : ConvergenceSignedStatement := h.1.2.1

theorem convergenceRate (h : Inputs) : ConvergenceRateStatement := h.1.2.2.1

theorem unifInt (h : Inputs) : UnifIntStatement := h.1.2.2.2.1

theorem pullback (h : Inputs) : PullbackStatement := h.1.2.2.2.2.1

theorem regGlobal (h : Inputs) : RegGlobalStatement := h.1.2.2.2.2.2

theorem resExists (h : Inputs) : ResExistsStatement := h.2.1.1

theorem degree (h : Inputs) : ReciprocityTheory.ChartRestriction.G.Geo.DegreeStatement := h.2.1.2.1

theorem height (h : Inputs) : ArithmeticIntersectionNonneg := h.2.1.2.2

theorem ratR (h : Inputs) : ReciprocityTheory.ChartRestriction.G.AI.I2.RatRStatement := h.2.2.1.1

theorem metricLocal (h : Inputs) : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement := h.2.2.1.2

theorem projFormula (h : Inputs) : ReciprocityTheory.ChartRestriction.G.AI.I4.PFStatement := h.2.2.2.1.1

theorem lineFibre (h : Inputs) : ReciprocityTheory.ChartRestriction.G.AI.I4.LineFibreStatement := h.2.2.2.1.2.1

theorem fibreDim (h : Inputs) : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement := h.2.2.2.1.2.2

theorem kleimanNef (h : Inputs) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg := h.2.2.2.2.1

theorem kleimanNefF (h : Inputs) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefFStatement := h.2.2.2.2.2.1

theorem siuZ (h : Inputs) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.SiuZStatement := h.2.2.2.2.2.2

end Inputs

end GlobalTheory.CompanionTheory.Ar.PB
