import Mathlib
import Formalism.LocalToGlobal.Columns.ToHLat
import Formalism.GL3MeanSquares.TraceIntegralityResults

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLattices.TraceIntegrality

section Forms

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def formAt {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (P : V →ₗ⋆[K] V →ₗ[K] K)
    (v : InfinitePlace K) (x y : V) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (v.embedding (b.repr x i)) * v.embedding (P (b i) (b j)) * v.embedding (b.repr y j)

theorem GSD.pairAt_eq_formAt (S : GSD K) (v : InfinitePlace K) (x y : S.V) :
    S.pairAt v x y = formAt S.bV S.pair v x y := rfl

@[reducible] def GSD.valH (S : GSD K) (d : S.D) : HLat K := ofFormB S.bV (S.Del d) fun v => S.pairAt v

@[reducible] def GSD.valNabH (S : GSD K) (d : S.D) : HLat K := ofFormB S.bV (S.Nab d) fun v => S.pairAt v

end Forms

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ}

abbrev oneW (lam : DomWeight n) : Unit → DomWeight n := fun _ => lam

abbrev StdV (lam : DomWeight n) : Submodule K (Pol K Unit n) := VV K (oneW lam)

def stdDelL (lam : DomWeight n) : Submodule (𝓞 K) (StdV K lam) :=
  (delStd K (oneW lam)).comap ((StdV K lam).subtype.restrictScalars (𝓞 K))

def stdNabL (lam : DomWeight n) : Submodule (𝓞 K) (StdV K lam) :=
  (nabStd K (oneW lam)).comap ((StdV K lam).subtype.restrictScalars (𝓞 K))

def stdPair (lam : DomWeight n) : StdV K lam →ₗ⋆[K] StdV K lam →ₗ[K] K := pairK (oneW lam) fun _ => 1

@[reducible] def stdDelH (lam : DomWeight n) : HLat K :=
  ofFormB (bVV K (oneW lam)) (stdDelL K lam) (formAt (bVV K (oneW lam)) (stdPair K lam))

@[reducible] def stdNabH (lam : DomWeight n) : HLat K :=
  ofFormB (bVV K (oneW lam)) (stdNabL K lam) (formAt (bVV K (oneW lam)) (stdPair K lam))

end Std

def kap (R : Ranks) : ℕ := R.N 0 - 1

theorem kap_succ (R : Ranks) : kap R + 1 = R.N 0 := by
  have h : R.N 0 = R.k := by simp [Ranks.N]
  have := R.m_add_three_le_k
  unfold kap
  omega

theorem brz_N_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]

theorem kap_succ_k (R : Ranks) : kap R + 1 = R.k := (kap_succ R).trans (brz_N_zero R)

theorem kap_cast (R : Ranks) : (kap R : ℝ) + 1 = (R.k : ℝ) := by
  exact_mod_cast kap_succ_k R

def castW {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : Fin (κ + 1) → ℤ := fun i => lam.w (Fin.cast h i)

theorem castW_anti {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : Antitone (castW h lam) := by
  intro i j hij
  show lam.w (Fin.cast h j) ≤ lam.w (Fin.cast h i)
  exact lam.anti (by rw [Fin.le_iff_val_le_val] at hij ⊢; simpa using hij)

section Nums

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

def lamZ (u : Pr.Word) (τ : X.Tau) : Fin (kap R + 1) → ℤ := castW (kap_succ R) (W.lamTrue u 0 τ)

theorem lamZ_anti (u : Pr.Word) (τ : X.Tau) : Antitone (lamZ W u τ) := castW_anti _ _

theorem lamZ_zero (u : Pr.Word) (τ : X.Tau) : lamZ W u τ 0 = W.aTop u τ := by
  simp only [lamZ, castW, Wts.aTop, Wts.lamTrue, shiftW, Nat.cast_zero, zero_mul, neg_zero, add_zero]
  congr 1 <;> exact Fin.ext (by simp)

theorem lamZ_last (u : Pr.Word) (τ : X.Tau) : lamZ W u τ (Fin.last (kap R)) = -W.bTop u τ := by
  have hN : 0 < R.N 0 := by rw [← kap_succ R]; omega
  simp only [lamZ, castW, Wts.bTop, DomWeight.detShift, dif_pos hN, neg_neg, Wts.lamTrue, shiftW,
    Nat.cast_zero, zero_mul, neg_zero, add_zero]
  congr 1 <;> exact Fin.ext rfl

variable (Pr) in

def logTC (u : Pr.Word) : ℝ := Real.log (Pr.T u)

variable (Pr) in

def loggC : ℝ := Real.log ((Pr.g 0 : ℝ) * (Pr.g 1 : ℝ))

variable (X) in

def vC : ℝ := |(NumberField.discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) / 2

variable (Pr R) in

def NumbersC (u : Pr.Word) (C₀ a b' L eta S : ℝ) : Prop :=
  Numbers C₀ a b' L (vC X) (logTC Pr u) (loggC Pr) eta S R.k R.m R.t (R.N R.m)

variable (Pr R) in

theorem numbersC_of (u : Pr.Word) {C₀ a b' L eta S : ℝ} (hL : 1 ≤ L) (hv : 1 ≤ vC X) (hav : Real.log (a * vC X) ≤ L)
    (hb : 1 ≤ b') (hba : b' ≤ a) (hT : logTC Pr u ≤ C₀ * R.m * L) (hg : loggC Pr ≤ C₀ * L) (he : 0 ≤ eta) (hS : 0 ≤ S)
    (hsm : S + eta + (R.m : ℝ) * R.t ≤ b') (hsq : (R.N R.m : ℝ) ^ 2 * (L + logTC Pr u) ≤ R.N R.m * b')
    (hlin : (R.N R.m : ℝ) * L + logTC Pr u ≤ b') (hpow : (1 + 2 * C₀) * (R.m : ℝ) ^ 3 * R.N R.m ≤ b') :
    NumbersC Pr R u C₀ a b' L eta S where
  one_le_L := hL
  one_le_v := hv
  log_av := hav
  one_le_b' := hb
  b'_le_a := hba
  logT_nonneg := Real.log_natCast_nonneg _
  logT_le := hT
  logg_nonneg := by
    unfold loggC
    rw [← Nat.cast_mul]
    exact Real.log_natCast_nonneg _
  logg_le := hg
  one_le_k := by have := R.m_add_three_le_k; omega
  one_le_m := by have := R.two_le_m; omega
  N_eq := rfl
  eta_nonneg := he
  S_nonneg := hS
  small := hsm
  sq := hsq
  lin := hlin
  pow := hpow

structure WtWin (u : Pr.Word) (C₀ a b' S : ℝ) : Prop where
  top : ∀ τ ∈ W.tops, a ≤ (W.aTop u τ : ℝ) ∧ (W.aTop u τ : ℝ) ≤ 2 * a ∧ b' ≤ (W.bTop u τ : ℝ) ∧ (W.bTop u τ : ℝ) ≤ 2 * b'
  top_wt : ∀ τ ∈ W.tops, (wt (lamZ W u τ) : ℝ) ≤ W.aTop u τ + (R.k : ℝ) * S
  top_plus : ∀ τ ∈ W.tops, (wt (plus (lamZ W u τ)) : ℝ) ≤ W.aTop u τ + (R.k : ℝ) * (W.bTop u τ + S)
  oth_plus : ∀ τ, τ ∉ W.tops → (wt (plus (lamZ W u τ)) : ℝ) ≤ ((R.k : ℝ) + 3) * S
  oth_wt : ∀ τ, τ ∉ W.tops → (wt (lamZ W u τ) : ℝ) ≤ C₀ * (R.k : ℝ) * S
  oth_last : ∀ τ, τ ∉ W.tops → |(W.bTop u τ : ℝ)| ≤ C₀ * S

def ZiiC (u : Pr.Word) (C a b' L S : ℝ) : ℝ :=
  -(∑ τ ∈ W.tops, (W.aTop u τ : ℝ) / (R.k : ℝ) * logTC Pr u) - C * W.tops.card * a * Real.log (R.k : ℝ)
    - C * X.f * (R.k : ℝ) * (b' + S) * Real.log (R.k : ℝ) - C * X.f * S * logTC Pr u - C * X.f * (R.k : ℝ) ^ 2 * L

def ZiiiC (u : Pr.Word) (C a b' L S : ℝ) : ℝ :=
  C * W.tops.card * a * Real.log ((R.k : ℝ) * vC X)
    + C * X.f * (b' + S) * ((R.k : ℝ) * Real.log ((R.k : ℝ) * vC X) + logTC Pr u) + C * X.f * (R.k : ℝ) ^ 2 * L

end Nums

section Named

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def GSD.OrthMean (S : GSD K) (h : S.Ok) : Prop :=
  (S.toH h S.intDel).mu = @mean S.Cl h.fintypeCl fun c => (S.valH (S.outSec.rep c)).mu

def GSD.OrthMax (S : GSD K) (h : S.Ok) : Prop :=
  ∃ c : S.Cl, (S.toH h S.intDel).muMax ≤ (S.valH (S.outSec.rep c)).muMax

variable (K) {n : ℕ}

def DualSlope (lam : DomWeight n) : Prop := (stdDelH K lam).mu = -(stdNabH K lam).mu

def SlopeLeMax (lam : DomWeight n) : Prop := (stdNabH K lam).mu ≤ (stdNabH K lam).muMax

def MaxSlopeNablaBound {κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : Prop := (stdNabH K lam).muMax ≤ MeanSquareWeightBound (castW h lam)

end Named

def MaxSlopeNablaSharpBound (K : Type) [Field K] [NumberField K] [StarRing K] {n κ : ℕ} (h : κ + 1 = n) (lam : DomWeight n) : Prop :=
  (stdNabH K lam).muMax ≤ (wt (plus (castW h lam)) : ℝ) * Real.log ((κ : ℝ) + 1)
    + ((κ : ℝ) + 1) * (κ : ℝ) / 2 * Real.log ((plus (castW h lam) 0 : ℝ) + (κ : ℝ) + 1)

theorem brz_plus_nonneg {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (hl : Antitone lam) (i : Fin (κ + 1)) : 0 ≤ plus lam i := by
  unfold plus
  exact sub_nonneg.2 (hl (Fin.le_last i))

def StdWeylSlopes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n κ : ℕ) (h : κ + 1 = n) (lam : DomWeight n),
    DualSlope K lam ∧ MaxSlopeNablaSharpBound K h lam

section NamedCol

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def SummandSlopeAtDecoratedLattice (u : Pr.Word) : Prop :=
  ∀ d : (colGSD W Ch u 0).D, ((colGSD W Ch u 0).valH d).mu =
    -(∑ τ, (wt (lamZ W u τ) : ℝ) / (R.k : ℝ) * logTC Pr u) + ∑ τ, (stdDelH X.K (W.lamTrue u 0 τ)).mu

def MaxSlopeSummandWithConstant (u : Pr.Word) (C₅ : ℝ) : Prop :=
  ∀ d : (colGSD W Ch u 0).D, ((colGSD W Ch u 0).valH d).muMax ≤
    ∑ τ, ((wt (plus (lamZ W u τ)) : ℝ) * (C₅ * Real.log ((R.k : ℝ) * vC X))
      + (R.k : ℝ) ^ 2 * Real.log ((plus (lamZ W u τ) 0 : ℝ) + (R.k : ℝ)) + |(W.bTop u τ : ℝ)| * logTC Pr u)

def MaxSlopeSummandExplicitForm (u : Pr.Word) : Prop :=
  ∀ d : (colGSD W Ch u 0).D, ((colGSD W Ch u 0).valH d).muMax ≤
    ∑ τ, ((wt (plus (lamZ W u τ)) : ℝ) * Real.log (4 * (R.k : ℝ) ^ 4 * vC X ^ 2)
      + (R.k : ℝ) * ((R.k : ℝ) - 1) / 2 * Real.log ((plus (lamZ W u τ) 0 : ℝ) + (R.k : ℝ))
      - (lamZ W u τ (Fin.last (kap R)) : ℝ) * logTC Pr u)

end NamedCol

def SummandSlopeAllData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok →
    2 * X.f * R.k < Pr.g 0 - 1 → ∀ u, SummandSlopeAtDecoratedLattice W Ch u

def MaxSlopeSummandAllData : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m), X.Ok → Pr.Ok →
    2 * X.f * R.k < Pr.g 0 - 1 → 2 ≤ vC X → ∀ u, MaxSlopeSummandExplicitForm W Ch u

section Main

theorem colCl_nonempty {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (u : Pr.Word) :
    Nonempty (colGSD W Ch u 0).Cl :=
  haveI : NeZero (R.N 0) := ⟨(R.N_pos 0).ne'⟩
  ⟨(colGSD W Ch u 0).cls (DecoSet.base X.E (R.N 0) (Pr.vT u) Pr.vGs)⟩

theorem propZ_ii_col : ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (hX : X.Ok) (u : Pr.Word) (a b' L eta S : ℝ),
    NumbersC Pr R u C₀ a b' L eta S → WtWin W u C₀ a b' S →
    (colGSD W Ch u 0).OrthMean (colOk W Ch hX u 0) → SummandSlopeAtDecoratedLattice W Ch u →
    (∀ τ, DualSlope X.K (W.lamTrue u 0 τ)) → (∀ τ, SlopeLeMax X.K (W.lamTrue u 0 τ)) →
    (∀ τ, MaxSlopeNablaBound X.K (kap_succ R) (W.lamTrue u 0 τ)) →
    ZiiC W u C a b' L S ≤ (Mu0H W Ch hX u).mu := by
  intro C₀ h0
  obtain ⟨C, hC⟩ := zeta_proposition_second C₀ h0
  refine ⟨C, fun {X Pr R} W Ch hX u a b' L eta S hN hW hM h5 hD hS h4 => ?_⟩
  let _ : Fintype (colGSD W Ch u 0).Cl := (colOk W Ch hX u 0).fintypeCl
  have := colCl_nonempty W Ch u
  have hN' : Numbers C₀ a b' L (vC X) (logTC Pr u) (loggC Pr) eta S (kap R + 1) R.m R.t (R.N R.m) := by
    rw [kap_succ_k]; exact hN
  have key := hC X.Tau (colGSD W Ch u 0).Cl W.tops (kap R) R.m R.t (R.N R.m) (lamZ W u)
    (fun τ => (W.aTop u τ : ℝ)) (fun τ => (W.bTop u τ : ℝ)) a b' L (vC X) (logTC Pr u) (loggC Pr) eta S
    (Mu0H W Ch hX u).mu (fun c => ((colGSD W Ch u 0).valH ((colGSD W Ch u 0).outSec.rep c)).mu)
    (fun τ => (stdDelH X.K (W.lamTrue u 0 τ)).mu) (fun τ => (stdNabH X.K (W.lamTrue u 0 τ)).mu)
    (fun τ => (stdNabH X.K (W.lamTrue u 0 τ)).muMax) hN' (lamZ_anti W u) hW.top
    (by simpa only [kap_cast] using hW.top_wt) (by simpa only [kap_cast] using hW.top_plus)
    (by simpa only [kap_cast] using hW.oth_plus) (by simpa only [kap_cast] using hW.oth_wt)
    hM (fun c => by simpa only [kap_cast] using h5 _) hD hS h4
  simpa only [kap_cast, ZiiC, Fields.f] using key

theorem propZ_iii_col : ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (hX : X.Ok) (u : Pr.Word) (a b' L eta S : ℝ),
    NumbersC Pr R u C₀ a b' L eta S → WtWin W u C₀ a b' S →
    (colGSD W Ch u 0).OrthMax (colOk W Ch hX u 0) → MaxSlopeSummandWithConstant W Ch u C₀ →
    (Mu0H W Ch hX u).muMax ≤ ZiiiC W u C a b' L S := by
  intro C₀ h0
  obtain ⟨C, hC⟩ := zeta_proposition_third C₀ h0
  refine ⟨C, fun {X Pr R} W Ch hX u a b' L eta S hN hW hM h5 => ?_⟩
  let _ : Fintype (colGSD W Ch u 0).Cl := (colOk W Ch hX u 0).fintypeCl
  have := colCl_nonempty W Ch u
  have hN' : Numbers C₀ a b' L (vC X) (logTC Pr u) (loggC Pr) eta S (kap R + 1) R.m R.t (R.N R.m) := by
    rw [kap_succ_k]; exact hN
  have e : ∀ p : ℝ, p + (kap R : ℝ) + 1 = p + (R.k : ℝ) := fun p => by rw [add_assoc, kap_cast]
  have hl : ∀ τ, |((lamZ W u τ (Fin.last (kap R)) : ℤ) : ℝ)| = |(W.bTop u τ : ℝ)| := fun τ => by
    rw [lamZ_last]; push_cast; exact abs_neg _
  have key := hC X.Tau (colGSD W Ch u 0).Cl W.tops (kap R) R.m R.t (R.N R.m) (lamZ W u)
    (fun τ => (W.aTop u τ : ℝ)) (fun τ => (W.bTop u τ : ℝ)) a b' L (vC X) (logTC Pr u) (loggC Pr) eta S
    (Mu0H W Ch hX u).muMax (fun c => ((colGSD W Ch u 0).valH ((colGSD W Ch u 0).outSec.rep c)).muMax)
    hN' (lamZ_anti W u) hW.top (by simpa only [kap_cast] using hW.top_plus)
    (fun τ hτ => by
      rw [hl, abs_of_nonneg]
      have h1 := (hW.top τ hτ).2.2.1
      have h2 := hN.one_le_b'
      linarith)
    (by simpa only [kap_cast] using hW.oth_plus) (fun τ hτ => by rw [hl]; exact hW.oth_last τ hτ)
    hM (fun c => by simpa only [kap_cast, e, hl] using h5 _)
  simpa only [kap_cast, ZiiiC, Fields.f] using key

theorem propZ_col : ∀ C₀ : ℝ, 0 ≤ C₀ → ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
    (Ch : Chars X Pr R.m) (hX : X.Ok) (u : Pr.Word) (a b' L eta S : ℝ),
    NumbersC Pr R u C₀ a b' L eta S → WtWin W u C₀ a b' S →
    (colGSD W Ch u 0).OrthMean (colOk W Ch hX u 0) → (colGSD W Ch u 0).OrthMax (colOk W Ch hX u 0) →
    SummandSlopeAtDecoratedLattice W Ch u → MaxSlopeSummandWithConstant W Ch u C₀ →
    (∀ τ, DualSlope X.K (W.lamTrue u 0 τ)) → (∀ τ, SlopeLeMax X.K (W.lamTrue u 0 τ)) →
    (∀ τ, MaxSlopeNablaBound X.K (kap_succ R) (W.lamTrue u 0 τ)) →
    ZiiC W u C a b' L S ≤ (Mu0H W Ch hX u).mu ∧ (Mu0H W Ch hX u).muMax ≤ ZiiiC W u C a b' L S := by
  intro C₀ h0
  obtain ⟨C2, h2⟩ := propZ_ii_col C₀ h0
  obtain ⟨C3, h3⟩ := propZ_iii_col C₀ h0
  refine ⟨max (max C2 C3) 0, le_max_right _ _, fun {X Pr R} W Ch hX u a b' L eta S hN hW hM hM' h5 h5' hD hS h4 => ?_⟩
  have l2 : C2 ≤ max (max C2 C3) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have l3 : C3 ≤ max (max C2 C3) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  generalize max (max C2 C3) 0 = C at l2 l3
  have hb : (0 : ℝ) ≤ b' := le_trans zero_le_one hN.one_le_b'
  have ha : (0 : ℝ) ≤ a := le_trans hb hN.b'_le_a
  have hSn := hN.S_nonneg
  have hL : (0 : ℝ) ≤ L := le_trans zero_le_one hN.one_le_L
  have hT := hN.logT_nonneg
  have hk1 : (1 : ℝ) ≤ (R.k : ℝ) := by exact_mod_cast hN.one_le_k
  have hk : (0 : ℝ) ≤ (R.k : ℝ) := le_trans zero_le_one hk1
  have hlk : 0 ≤ Real.log (R.k : ℝ) := Real.log_nonneg hk1
  have hlkv : 0 ≤ Real.log ((R.k : ℝ) * vC X) := Real.log_nonneg (by nlinarith [hN.one_le_v])
  have hf : (0 : ℝ) ≤ (X.f : ℝ) := Nat.cast_nonneg _
  have hc : (0 : ℝ) ≤ (W.tops.card : ℝ) := Nat.cast_nonneg _
  constructor
  · refine le_trans ?_ (h2 W Ch hX u a b' L eta S hN hW hM h5 hD hS h4)
    unfold ZiiC
    have e1 : C2 * W.tops.card * a * Real.log (R.k : ℝ) ≤ C * W.tops.card * a * Real.log (R.k : ℝ) := by
      have : 0 ≤ (W.tops.card : ℝ) * a * Real.log (R.k : ℝ) := by positivity
      nlinarith
    have e2 : C2 * X.f * (R.k : ℝ) * (b' + S) * Real.log (R.k : ℝ) ≤ C * X.f * (R.k : ℝ) * (b' + S) * Real.log (R.k : ℝ) := by
      have : 0 ≤ (X.f : ℝ) * (R.k : ℝ) * (b' + S) * Real.log (R.k : ℝ) := by positivity
      nlinarith
    have e3 : C2 * X.f * S * logTC Pr u ≤ C * X.f * S * logTC Pr u := by
      have : 0 ≤ (X.f : ℝ) * S * logTC Pr u := by positivity
      nlinarith
    have e4 : C2 * X.f * (R.k : ℝ) ^ 2 * L ≤ C * X.f * (R.k : ℝ) ^ 2 * L := by
      have : 0 ≤ (X.f : ℝ) * (R.k : ℝ) ^ 2 * L := by positivity
      nlinarith
    linarith
  · refine le_trans (h3 W Ch hX u a b' L eta S hN hW hM' h5') ?_
    unfold ZiiiC
    have e1 : C3 * W.tops.card * a * Real.log ((R.k : ℝ) * vC X) ≤ C * W.tops.card * a * Real.log ((R.k : ℝ) * vC X) := by
      have : 0 ≤ (W.tops.card : ℝ) * a * Real.log ((R.k : ℝ) * vC X) := by positivity
      nlinarith
    have e2 : C3 * X.f * (b' + S) * ((R.k : ℝ) * Real.log ((R.k : ℝ) * vC X) + logTC Pr u) ≤
        C * X.f * (b' + S) * ((R.k : ℝ) * Real.log ((R.k : ℝ) * vC X) + logTC Pr u) := by
      have : 0 ≤ (X.f : ℝ) * (b' + S) * ((R.k : ℝ) * Real.log ((R.k : ℝ) * vC X) + logTC Pr u) := by positivity
      nlinarith
    have e4 : C3 * X.f * (R.k : ℝ) ^ 2 * L ≤ C * X.f * (R.k : ℝ) ^ 2 * L := by
      have : 0 ≤ (X.f : ℝ) * (R.k : ℝ) ^ 2 * L := by positivity
      nlinarith
    linarith

end Main

section PartI

def logOp {K : Type} [Field K] [NumberField K] [StarRing K] (A B : HLat K) (φ : A.V →ₗ[K] B.V) (v : InfinitePlace K) : ℝ :=
  Real.log (Formalism.HN.opNormAt A.b A.X B.b B.X v φ ^ 2)

theorem brz_N_succ (R : Ranks) (j : ℕ) : R.N j - 1 + 1 = R.N j := by
  have h1 : R.k ≤ R.N j := Nat.le_add_right _ _
  have := R.m_add_three_le_k
  omega

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

abbrev StepArg (u : Pr.Word) : Type := ∀ j : ℕ, ColV W Ch u j →ₗ[X.K] ColV W Ch u (j + 1)

variable {W Ch} in

def chainArg {u : Pr.Word} (kk : StepArg W Ch u) : ∀ j : ℕ, ColV W Ch u 0 →ₗ[X.K] ColV W Ch u j
  | 0 => LinearMap.id
  | j + 1 => kk j ∘ₗ chainArg kk j

def nuZ (u : Pr.Word) (j : ℕ) (τ : X.Tau) : Fin (R.N j - 1 + 1) → ℕ :=
  fun i => (castW (brz_N_succ R j) (W.nuW u (j + 1) τ) i).toNat

def wZ (u : Pr.Word) (j : ℕ) (τ : X.Tau) : ℕ := ⌊wG R ((RowPar.of (W.hc u τ)).eAt j) (j + 1)⌋.toNat

def lamMZ (u : Pr.Word) (τ : X.Tau) : Fin (R.N R.m - 1 + 1) → ℤ := castW (brz_N_succ R R.m) (W.lamTrue u R.m τ)

def sgZ (τ : X.Tau) : Fin (R.N R.m - 1) → ℤ := (W.sgTrue τ).w

structure WtWinI (u : Pr.Word) (T2 : Finset X.Tau) (C₀ a b' L eta S : ℝ) : Prop where
  disj : Disjoint W.tops T2
  nu_anti : ∀ (j : Fin R.m) τ, Antitone (nuZ W u j τ)
  top : ∀ τ ∈ W.tops, a ≤ ((W.aTop u τ).toNat : ℝ) ∧ ((W.aTop u τ).toNat : ℝ) ≤ 2 * a ∧ (W.bTop u τ : ℝ) ≤ 2 * b'
  nu_top : ∀ j : Fin R.m, ∀ τ ∈ W.tops, nuZ W u j τ 0 = (W.aTop u τ).toNat + wZ W u j τ ∧ (wZ W u j τ : ℝ) ≤ 2 * b' ∧
    ∀ i, i ≠ 0 → (nuZ W u j τ i : ℝ) ≤ (2 + C₀) * b'
  nu_thin : ∀ (j : Fin R.m) τ, τ ∉ W.tops → τ ∉ T2 → ∀ i, (nuZ W u j τ i : ℝ) ≤ (2 + C₀) * b'
  inter : ∀ τ, Formalism.LogVandermondeBounds.flipTwoThree.Interlace (lamMZ W u τ) (sgZ W τ)
  logW : ∀ τ, Real.log (Wnum (lamMZ W u τ) : ℝ) ≤ C₀ * L
  topWeightBound : ∀ τ ∈ W.tops, (Formalism.LogVandermondeBounds.flipTwoThree.B0 (lamMZ W u τ) (sgZ W τ) : ℝ) ≤ W.bTop u τ + eta + S
  otherWeightBound : ∀ τ, τ ∉ W.tops → (Formalism.LogVandermondeBounds.flipTwoThree.B0 (lamMZ W u τ) (sgZ W τ) : ℝ) ≤ eta + S
  slots : ∀ τ, ∃ Y : Finset (Fin (R.N R.m - 1)), Y.card ≤ 3 ∧ ((∑ i ∈ Yᶜ, Formalism.LogVandermondeBounds.flipTwoThree.len (lamMZ W u τ) i : ℤ) : ℝ) ≤ eta + S
  deg_top : ∀ τ ∈ W.tops, ((W.aTop u τ).toNat : ℝ) - W.bTop u τ - C₀ * (S + eta + (R.m : ℝ) * R.t) ≤ (W.degTrue u τ : ℝ)
  deg_oth : ∀ τ, τ ∉ W.tops → -(S + eta) - C₀ * ((R.m : ℝ) * R.t) ≤ (W.degTrue u τ : ℝ)

variable (hX : X.Ok)

structure SizeIn (u : Pr.Word) (kk : StepArg W Ch u) (B : HLat X.K) (Pt : ColV W Ch u R.m →ₗ[X.K] B.V)
    (C₀ L logOm : ℝ) (logOms : X.Tau → InfinitePlace X.K → ℝ) (logTh : Fin R.m → InfinitePlace X.K → ℝ) : Prop where
  per : ∀ τ, mean (logOms τ) = logOm
  per_le : |logOm| ≤ C₀ * L
  th : ∀ j, mean (logTh j) ≤ C₀ * Fintype.card X.Tau * (((R.N R.m - 1 : ℕ) : ℝ) + 1) ^ 2 * L
  z1 : ∀ (j : Fin R.m) v, logOp (latH W Ch hX u j) (latH W Ch hX u (j + 1)) (kk j) v ≤
    ∑ τ, placeTerm (nuZ W u j τ) (logOms τ v) + logTh j v
      + C₀ * Fintype.card X.Tau * (R.m : ℝ) ^ 2 * (((R.N R.m - 1 : ℕ) : ℝ) + 1) ^ 2 * (L + logTC Pr u + loggC Pr)
  z3 : ∀ v, logOp (latH W Ch hX u R.m) B Pt v ≤ ∑ τ, MeanSquareTwistBound (lamMZ W u τ) (sgZ W τ) (logTC Pr u)
  submul : Pt ∘ₗ chainArg kk R.m ≠ 0 → ∀ v, logOp (Mu0H W Ch hX u) B (Pt ∘ₗ chainArg kk R.m) v ≤
    logOp (latH W Ch hX u R.m) B Pt v + ∑ j : Fin R.m, logOp (latH W Ch hX u j) (latH W Ch hX u (j + 1)) (kk j) v

end PartI

end Formalism.L2.Col
