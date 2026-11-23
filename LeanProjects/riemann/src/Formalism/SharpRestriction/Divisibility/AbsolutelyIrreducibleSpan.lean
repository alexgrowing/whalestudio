import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HermitianLattices.StatementMaj
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace Formalism.MainNotions.AbsolutelyIrreducibleSpan

open Formalism.BasicNotions

section LLStr

variable {LL : Type} [Field LL] (φ : LL →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W]

def llSpan (S : Set W) : Set W :=
  {x | ∃ (s : Finset W) (c : W → LL), (↑s : Set W) ⊆ S ∧ x = ∑ v ∈ s, φ (c v) • v}

def llIndep (s : Finset W) : Prop :=
  ∀ c : W → LL, ∑ v ∈ s, φ (c v) • v = 0 → ∀ v ∈ s, c v = 0

def IsLLForm (F : Set W) : Prop :=
  llSpan φ F = F ∧ Submodule.span ℂ F = ⊤ ∧
    ∀ s : Finset W, (↑s : Set W) ⊆ F → llIndep φ s → LinearIndependent ℂ (fun x : s => (x : W))

def IsRational (F : Set W) (U : Submodule ℂ W) : Prop :=
  Submodule.span ℂ ((U : Set W) ∩ F) = U

end LLStr

structure Lev (D : D7) where
  EE : Type
  [nEE : NormedAddCommGroup EE]
  [iEE : InnerProductSpace ℂ EE]
  [fEE : FiniteDimensional ℂ EE]
  S : RowSide D EE
  n : ℕ
  onb : OrthonormalBasis (Fin n) ℂ EE
  ft : Fin n → D.what₂.FT

attribute [instance] Lev.nEE Lev.iEE Lev.fEE

def Lev.of {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) : Lev D :=
  { EE := EE, S := S, n := n, onb := b, ft := ty }

def Lev.sharp (D : D7) : Lev D := Lev.of (RowSide.sharp D) D.what₂.onb D.what₂.ft

def Lev.p0 {D : D7} (P : BaseLevelRowSide D) : Lev D := Lev.of P.s D.what₂.onb0 D.what₂.ft0

def Lev.kap {D : D7} (V : Lev D) : ℝ := V.S.kapOf V.ft

theorem Lev.kap_pos {D : D7} (V : Lev D) : 0 < V.kap := by
  unfold Lev.kap RowSide.kapOf
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

theorem sharp_kap (D : D7) : (Lev.sharp D).kap = kapSharp D := rfl

theorem chain_constant_at_small_level {D : D7} (P : BaseLevelRowSide D) : (Lev.p0 P).kap = P.kap0 := rfl

theorem sharp_downTo (D : D7) (μ : D.what₂.Tup) :
    ∀ j, (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j
  | 0 => rfl
  | j + 1 => by
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [sharp_downTo D μ j]; rfl

theorem sharp_iota (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  first
  | (unfold RowSide.iota Rows.Data.iota; rw [sharp_downTo D μ D.R.m]; try rfl; done)
  | (simp only [RowSide.iota, Rows.Data.iota, sharp_downTo]; try rfl; done)
  | rfl

theorem sharp_Usp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Usp μ = D.what₂.Usp μ := by
  first
  | (unfold RowSide.Usp Rows.Data.Usp; rw [sharp_iota]; try rfl; done)
  | (simp only [RowSide.Usp, Rows.Data.Usp, sharp_iota]; try rfl; done)
  | rfl

theorem sharp_Qsp (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).Qsp μ = D.what₂.Qsp μ := by
  first
  | (unfold RowSide.Qsp Rows.Data.Qsp; rw [sharp_Usp]; try rfl; done)
  | (simp only [RowSide.Qsp, Rows.Data.Qsp, sharp_Usp]; try rfl; done)
  | rfl

theorem sharp_LamSet (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).LamSet μ = D.what₂.LamSet μ := by
  first
  | (unfold RowSide.LamSet Rows.Data.LamSet; rw [sharp_Qsp]; try rfl; done)
  | (simp only [RowSide.LamSet, Rows.Data.LamSet, sharp_Qsp]; try rfl; done)
  | rfl

theorem sharp_RRset (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).RRset μ = D.what₂.RRset μ := by
  first
  | (unfold RowSide.RRset Rows.Data.RRset; rw [sharp_iota, sharp_LamSet]; try rfl; done)
  | (simp only [RowSide.RRset, Rows.Data.RRset, sharp_iota, sharp_LamSet]; try rfl; done)
  | rfl

theorem sharp_RRDef (D : D7) : (RowSide.sharp D).RRDef ↔ DV.RRDef D := by
  first
  | (unfold RowSide.RRDef DV.RRDef; simp only [sharp_RRset]; try exact Iff.rfl; done)
  | exact Iff.rfl

theorem sharp_AIntegral (D : D7) : (RowSide.sharp D).AIntegral ↔ Rows.AIntegral D.what₂ := by
  first
  | exact Iff.rfl
  | (unfold RowSide.AIntegral Rows.AIntegral; exact Iff.rfl)

section Derived

variable (D : D7)

abbrev Used (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

variable {D} in

theorem Used.dv {μ : D.what₂.Tup} (h : Used D μ) : DV.Used D μ := by
  unfold DV.Used
  rcases h with h | ⟨w, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr ⟨w, h⟩))

def v0 : InfinitePlace D.what₂.LL := InfinitePlace.mk D.what₂.embLL

def DataTup (V : Lev D) (μ : D.what₂.Tup) (c : ℝ) : Prop :=
  Function.Bijective (V.S.iotaQ μ) ∧
  ∀ σ, (V.S.iotaQ μ ∘ₗ LinearMap.adjoint (V.S.iotaQ μ)) (V.onb σ) =
    ((c * ∏ j ∈ SizeData₂.lifts D, D.what₂.lamP μ j (V.ft σ) : ℝ) : ℂ) • V.onb σ

def LamLow (b : ℝ) : Prop :=
  ∀ j ∈ SizeData₂.lifts D, ∀ σ, Real.exp (-b) ≤ D.what₂.lamP D.what₂.mu0 j σ

def DataAt (V : Lev D) (b κ : ℝ) : Prop :=
  (∃ ρ : D.what₂.Tup → ℝ, ρ D.what₂.mu0 = 1 ∧ (∀ μ, 0 < ρ μ) ∧ ∀ μ, Used D μ → DataTup D V μ (κ * ρ μ)) ∧
    LamLow D b

def lamC : ℝ :=
  ⨆ τ : D.what₂.Tau, (((D.hc τ).v ⟨0, by have := D.R.m_add_three_le_k; omega⟩ -
    (D.hc τ).v ⟨D.R.k - 2, by have := D.R.m_add_three_le_k; omega⟩ : ℚ) : ℝ)

def rPr : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0 : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

theorem condE_pos : 0 < LevelStarExponents.condE D := by
  unfold LevelStarExponents.condE
  exact Nat.mul_pos (Nat.mul_pos D.host.QS_pos (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.1))
    (lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2)

theorem absNorm_ccK_pos : 0 < Ideal.absNorm D.host.ccK := by
  first
  | exact Nat.pos_of_ne_zero (fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  | (rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot)

theorem rPr_mem : (rPr D).Prime ∧
    ¬ rPr D ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
  have hN : 0 < LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK := by
    have h1 := D.host.pde_prime.two_le
    have h2 := D.host.pde'_prime.two_le
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (condE_pos D) (by omega)) (by omega)) (absNorm_ccK_pos D)
  obtain ⟨p, hp1, hp2⟩ :=
    Nat.exists_infinite_primes (LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK + 1)
  have hne : {p : ℕ | p.Prime ∧
      ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp2, fun hd => absurd (Nat.le_of_dvd hN hd) (Nat.not_le.mpr (Nat.lt_of_succ_le hp1))⟩
  exact Nat.sInf_mem hne

theorem auxiliary_prime_mem : (q0 D).Prime ∧ q0 D % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ q0 D ∣ Ideal.absNorm D.host.ccK := by
  have hr := (rPr_mem D).1
  have hc := condE_pos D
  have hk : 1 < rPr D * LevelStarExponents.condE D :=
    lt_of_lt_of_le hr.one_lt (le_mul_of_one_le_right (Nat.zero_le _) hc)
  obtain ⟨p, hp, hlt, hmod⟩ :=
    Nat.exists_prime_gt_modEq_one (Ideal.absNorm D.host.ccK) (Nat.pos_iff_ne_zero.mp (lt_trans Nat.zero_lt_one hk))
  have hne : {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}.Nonempty :=
    ⟨p, hp, (show p % _ = 1 % _ from hmod).trans (Nat.mod_eq_of_lt hk),
      fun hd => absurd (Nat.le_of_dvd (absNorm_ccK_pos D) hd) (Nat.not_le.mpr hlt)⟩
  exact Nat.sInf_mem hne

theorem auxiliary_prime_eq_least (h : Ideal.absNorm D.host.ccK < LevelStarExponents.condE D) :
    q0 D = sInf {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1} := by
  unfold q0
  congr 1
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp, h1, -⟩
    exact ⟨hp, h1⟩
  · rintro ⟨hp, h1⟩
    refine ⟨hp, h1, fun hd => ?_⟩
    have hkp : rPr D * LevelStarExponents.condE D < p := by
      by_contra hle
      push_neg at hle
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · rw [heq, Nat.mod_self] at h1
        exact absurd h1 (by norm_num)
      · rw [Nat.mod_eq_of_lt hlt] at h1
        exact absurd h1 hp.one_lt.ne'
    have hck : LevelStarExponents.condE D ≤ rPr D * LevelStarExponents.condE D :=
      le_mul_of_one_le_left (Nat.zero_le _) (rPr_mem D).1.one_lt.le
    exact absurd (Nat.le_of_dvd (absNorm_ccK_pos D) hd)
      (Nat.not_le.mpr (lt_trans h (lt_of_le_of_lt hck hkp)))

def S0pr : Finset ℕ := {D.host.g 0, D.host.g 1, D.host.pde, D.host.pde', q0 D}

def chiCond (p : ℕ) : ℕ :=
  if p = D.host.g 0 ∨ p = D.host.g 1 ∨ p = D.host.pde ∨ p = D.host.pde' then 2 else if p = q0 D then 1 else 0

def nAt (l : ℕ) : ℕ := if l = q0 D then 1 else D.R.f

def PPn (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + 1) ^ 6 *
    Real.log (L.sc.b * ((D.R.r : ℝ) + 1) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
      (D.host.pde' : ℝ) * |(NumberField.discr D.host.E : ℝ)|)

def eV0 (L : SizeData₂ D) (C : ℝ) : ℕ := ⌊PPn D L C / Real.log (q0 D : ℝ)⌋₊ + 1

end Derived

def IsPath (m : ℕ) (h : ℕ → ℕ) : Prop :=
  (∀ i, h i ≤ m) ∧ (∀ i, h (i + 1) ≤ h i) ∧ ∀ i, m ≤ i → h i = 0

def hBot : ℕ → ℕ := fun _ => 0

def hTop (m : ℕ) : ℕ → ℕ := fun i => if i < m then m else 0

def flipP (h : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := Function.update h i (h i + 1)

def Flippable (m : ℕ) (h : ℕ → ℕ) (i : ℕ) : Prop :=
  i < m ∧ h i < m ∧ (i = 0 ∨ h i < h (i - 1))

open Formalism.BasicNotions.TH (Ix Mat ProvA)

def shiftIx {p q : ℕ} : Ix p q → Ix (p + 1) q
  | Sum.inl i => Sum.inl i.succ
  | Sum.inr j => Sum.inr j

def embMat {p q : ℕ} (g : Mat p q) : Mat (p + 1) q :=
  Matrix.of fun a b =>
    (if a = Sum.inl 0 ∧ b = Sum.inl 0 then (1 : ℂ) else 0) +
      ∑ a', ∑ b', if shiftIx a' = a ∧ shiftIx b' = b then g a' b' else 0

structure ThetaTh where
  Sp : Type
  rk : Sp → ℕ
  witt : Sp → ℕ
  AF : Sp → Type
  [aAF : ∀ V, AddCommGroup (AF V)]
  [mAF : ∀ V, Module ℂ (AF V)]
  cusp : ∀ V, Submodule ℂ (AF V)
  pet : ∀ V, AF V → AF V → ℂ
  Dat : Sp → Sp → Type
  lift : ∀ W V, Dat W V → AF W →ₗ[ℂ] AF V
  Tst : Sp → ℕ → Bool → Type
  per : ∀ V c b, Tst V c b → AF V →ₗ[ℂ] ℂ
  tcusp : ∀ V c b, Tst V c b → Prop
  tpure : ∀ V c b, Tst V c b → Prop
  taniso : ∀ V c b, Tst V c b → Prop
  tmatch : ∀ W V c b, Dat W V → Tst V c b → Prop
  Hq : ∀ (_W V : Sp) (c : ℕ) (b : Bool), Tst V (c + 1) b → Type
  itInt : ∀ W V c b (ph : Tst V (c + 1) b), (Hq W V c b ph → ℂ) → ℂ
  tlift : ∀ W V c b, Dat W V → ∀ ph : Tst V (c + 1) b, Hq W V c b ph → Tst W c (!b)
  tl0 : ∀ W V b, Dat W V → Tst V 0 b → AF W
  tl0cusp : ∀ W V b, Dat W V → Tst V 0 b → Prop
  PlS : Type
  fac : ∀ W V, PlS → Dat W V → Dat W V → AF W → AF W → Prop
  lowerZero : ∀ W V, Dat W V → AF W → Prop
  LS : ∀ W V, PlS → Dat W V → AF W → ℝ → ℂ
  dS : ∀ W V, PlS → Dat W V → ℂ
  Zloc : ∀ W V, PlS → Dat W V → Dat W V → AF W → AF W → ℂ
  cR : Sp → Sp → ℂ
  embC : ∀ W, AF W → AF W → ℂ

attribute [instance] ThetaTh.aAF ThetaTh.mAF

structure LocV (D : D7) (V : Lev D) (A : AmbForm D V.S) where
  kapV : InfinitePlace D.what₂.LL → ℝ
  kapV_pos : ∀ v, 0 < kapV v
  kapV_base : kapV (v0 D) = V.kap
  plS : Finset D.what₂.places.Pl
  plS_mu : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ plS
  s : ℕ
  s_odd : Odd s
  s_lo : D.R.r + 5 < s
  s_hi : s ≤ D.R.r + 7
  cInf : ℕ → D.what₂.Tau → ℚ
  chi_above : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ (j : Fin D.R.m) τ,
    2 * ((D.R.k + D.R.m * (D.R.t + s + 1) : ℕ) : ℚ) ^ 3 < 2 * ((D.hc τ).e j + cInf i τ)
  ev0 : ℕ
  nb : Fin D.R.m → ℚ
  ar : ProvA
  th : ThetaTh
  vx : ℕ → ℕ → th.Sp
  vx_rk : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → th.rk (vx i j) = D.R.r + j * D.R.t + i * s
  vx_witt : ∀ i j, i ≤ D.R.m → j ≤ D.R.m → th.witt (vx i j) ≤ (D.R.m - j) / 2
  Pp : ℕ → th.Sp
  Pp_rk : ∀ i, i ≤ D.R.m → th.rk (Pp i) = D.R.r + 1 + i * (s - 1)
  Pp_witt : ∀ i, i ≤ D.R.m → th.witt (Pp i) ≤ (D.R.m - i + 1) / 2
  real : V.EE →ₗ[ℂ] th.AF (vx 0 0)
  real_inj : Function.Injective real
  real_cusp : ∀ u, real u ∈ th.cusp (vx 0 0)
  MM : HLat D.what₂.LL
  MM_good : MM.Good
  DatX : Type
  [finDat : Fintype DatX]
  I0 : Type
  mmIx : MM.ι ≃ DatX × I0
  tst : I0 → th.Tst (vx D.R.m 0) (D.R.m - 1) true
  datRow : DatX → ∀ i, th.Dat (vx i 0) (vx (i + 1) 0)
  PD : D.what₂.Tup → (ℕ → ℕ) → Type
  [aPD : ∀ μ h, AddCommGroup (PD μ h)]
  [mPD : ∀ μ h, Module ℂ (PD μ h)]
  ev : ∀ μ h, PD μ h →ₗ[ℂ] V.S.Amb μ →ₗ[ℂ] th.AF (vx D.R.m 0)
  T0 : ∀ μ, DatX → PD μ hBot
  Good : ∀ μ h, Set (PD μ h)
  IntAt : ∀ μ h, D.what₂.places.Pl → ℝ → Set (PD μ h)
  SzAt : ∀ μ h, InfinitePlace D.what₂.LL → ℝ → Set (PD μ h)
  Rep : D.what₂.Tup → (ℕ → ℕ) → ℕ → Type
  pA : ∀ μ h i, PD μ (flipP h i) → Rep μ h i
  pB : ∀ μ h i, PD μ h → Rep μ h i
  csq : D.what₂.Tup → ℕ → ℕ → ℂ
  vT : ∀ μ, PD μ (hTop D.R.m) → I0 → Module.Dual D.what₂.LL (A.MtH μ).V
  App : ℂ
  KI : Type
  kS : KI → HLat D.what₂.LL
  kT : KI → HLat D.what₂.LL
  kmap : ∀ k, (kS k).V →ₗ[D.what₂.LL] (kT k).V
  kTup : KI → D.what₂.Tup
  kdeg : KI → ℕ
  kdepth : KI → ℕ → ℕ
  U1 : Submodule ℂ (th.AF (vx 0 0))
  MS : ℕ → Type
  [aMS : ∀ i, AddCommGroup (MS i)]
  [mMS : ∀ i, Module ℂ (MS i)]
  DatP : ℕ → Type
  Dn : ∀ i, DatP i → MS (i + 1) →ₗ[ℂ] MS i
  Up : ∀ i, DatP i → MS i →ₗ[ℂ] MS (i + 1)
  phi0 : ∀ i, DatP i
  DatS : Type
  cmb : DatS → DatX → ℂ
  datPof : DatS → ∀ i, DatP i
  Phi0 : DatS
  phi_data_at_base : datPof Phi0 = phi0
  psiMS : I0 → MS D.R.m
  psi_span : Submodule.span ℂ (Set.range psiMS) = ⊤
  lamPer : MS 0 →ₗ[ℂ] th.AF (vx 0 0) →ₗ[ℂ] ℂ
  Irr : Set (MS 0)
  Ap : ℂ
  volS : ℝ
  volS_pos : 0 < volS
  cRal : ℕ → ℂ
  LSpi : MS 0 → ℕ → ℂ
  Lchi : ℕ → ℕ → ℕ → ℂ
  dSv : ℕ → ℂ
  ZS : ℕ → ℝ

attribute [instance] LocV.finDat LocV.aPD LocV.mPD LocV.aMS LocV.mMS

abbrev Loc (D : D7) (A : AmbForm D (RowSide.sharp D)) := LocV D (Lev.sharp D) A

namespace LocV

variable {D : D7} {V : Lev D} {A : AmbForm D V.S} (X : LocV D V A)

def Nst : ℕ := D.R.k + D.R.m * (D.R.t + X.s + 1)

def eAt (l : ℕ) : ℕ := if l = q0 D then X.ev0 else 2

def weightedLogLevelSum : ℝ :=
  2 * (D.R.f : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) * (D.host.pde' : ℝ)) +
    (X.ev0 : ℝ) * Real.log (q0 D : ℝ)

def ltPts (_X : LocV D V A) (μ : D.what₂.Tup) : Set (V.S.Amb μ) := Set.range (A.jAmb μ)

noncomputable def rowUp (Φ : X.DatX) : (i : ℕ) → X.th.AF (X.vx 0 0) →ₗ[ℂ] X.th.AF (X.vx i 0)
  | 0 => LinearMap.id
  | i + 1 => (X.th.lift (X.vx i 0) (X.vx (i + 1) 0) (X.datRow Φ i)).comp (rowUp Φ i)

def fPer (Φ : X.DatX) (a : X.I0) : X.th.AF (X.vx 0 0) →ₗ[ℂ] ℂ :=
  (X.th.per (X.vx D.R.m 0) (D.R.m - 1) true (X.tst a)).comp (X.rowUp Φ D.R.m)

def cTot (μ : D.what₂.Tup) : ℂ :=
  ∏ i ∈ Finset.range D.R.m, ∏ j ∈ Finset.range D.R.m, X.csq μ i j

def PSI : V.EE →ₗ[ℂ] (X.MM.ι → ℂ) :=
  LinearMap.pi fun i =>
    (X.cTot D.what₂.mu0 * X.App⁻¹) • ((X.fPer (X.mmIx i).1 (X.mmIx i).2).comp X.real)

def EELL : Set V.EE := {u | ∀ i, X.PSI u i ∈ Set.range D.what₂.embLL}

def vMap (μ : D.what₂.Tup) (Tf : X.DatX → X.PD μ (hTop D.R.m)) :
    (A.MtH μ).V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL X.MM.V :=
  ∑ i, (X.vT μ (Tf (X.mmIx i).1) (X.mmIx i).2).smulRight (X.MM.b.coord i)

noncomputable def dnAll (φ : ∀ i, X.DatP i) : (i : ℕ) → X.MS i →ₗ[ℂ] X.MS 0
  | 0 => LinearMap.id
  | i + 1 => (dnAll φ i).comp (X.Dn i (φ i))

noncomputable def upChain (ξ : X.MS 0) : (i : ℕ) → X.MS i
  | 0 => ξ
  | i + 1 => X.Up i (X.phi0 i) (upChain ξ i)

def ralVal (ξ : X.MS 0) (i : ℕ) : ℂ :=
  X.cRal i * (X.LSpi ξ (D.R.m - i) *
      ∏ c' ∈ Finset.Ioc (D.R.m - i) D.R.m, ∏ n' ∈ Finset.Icc 1 (X.s - 1), X.Lchi n' c' (D.R.m - i)) /
    X.dSv i * (X.ZS i : ℂ)

end LocV

def unitMetricFrames {D : D7} {V : Lev D} {A : AmbForm D V.S} (X : LocV D V A) : InfinitePlace D.what₂.LL → Matrix V.S.RR.ι V.S.RR.ι ℂ :=
  fun v => ((Real.sqrt (X.kapV v) : ℝ) : ℂ) • V.S.RR.X v

def KapLevels {D : D7} {V : Lev D} {A : AmbForm D V.S} (XD : DivX D) (X : LocV D V A) : Prop :=
  ∀ v : InfinitePlace D.what₂.LL, X.kapV v = XD.kapR v.embedding

def KapNear {D : D7} {V : Lev D} {A : AmbForm D V.S} (XD : DivX D) (X : LocV D V A) (c : ℝ) : Prop :=
  ∀ v : InfinitePlace D.what₂.LL, |Real.log (X.kapV v) - Real.log (XD.kapR v.embedding)| ≤ c

theorem kapNear_of_levels {D : D7} {V : Lev D} {A : AmbForm D V.S} {XD : DivX D} {X : LocV D V A} (h : KapLevels XD X) :
    KapNear XD X 0 := by
  unfold KapNear
  unfold KapLevels at h
  intro v
  rw [h v]
  simp

theorem unit_metric_frames_of_levels {D : D7} {V : Lev D} {A : AmbForm D V.S} {XD : DivX D} {X : LocV D V A} (h : KapLevels XD X) :
    unitMetricFrames X = fun v => ((Real.sqrt (XD.kapR v.embedding) : ℝ) : ℂ) • V.S.RR.X v := by
  unfold KapLevels at h
  funext v
  first
  | (simp only [unitMetricFrames, h v]; done)
  | (unfold unitMetricFrames; rw [h v])

section admitted

variable (D : D7) {V : Lev D} {A : AmbForm D V.S}

def adm1 (X : LocV D V A) : Prop :=
  (∀ (W V : X.th.Sp) (Φ : X.th.Dat W V) (c : ℕ) (b : Bool) (G : X.th.AF W) (ph : X.th.Tst V (c + 1) b),
    G ∈ X.th.cusp W → X.th.tcusp V (c + 1) b ph →
    (b = false → (X.th.tpure V (c + 1) b ph ∨ X.th.taniso V (c + 1) b ph) ∧ X.th.tmatch W V (c + 1) b Φ ph) →
    (∀ h, X.th.tcusp W c (!b) (X.th.tlift W V c b Φ ph h)) →
      X.th.per V (c + 1) b ph (X.th.lift W V Φ G) =
        X.th.itInt W V c b ph (fun h => X.th.per W c (!b) (X.th.tlift W V c b Φ ph h) G)) ∧
  (∀ (W V : X.th.Sp) (Φ : X.th.Dat W V) (b : Bool) (G : X.th.AF W) (ph : X.th.Tst V 0 b),
    G ∈ X.th.cusp W → X.th.tcusp V 0 b ph →
    (b = false → X.th.tpure V 0 b ph ∨ X.th.taniso V 0 b ph) → X.th.tl0cusp W V b Φ ph →
      X.th.per V 0 b ph (X.th.lift W V Φ G) = X.th.pet W G (X.th.tl0 W V b Φ ph))

def adm2 (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (C : ℝ) : Prop :=
  DataAt D V L.sc.b V.kap ∧
  (∀ (s : D.what₂.LL →+* ℂ), ∀ j ∈ SizeData₂.lifts D, ∀ σ : Fin V.n, -L.sc.b ≤ XD.logLam j (V.ft σ) s) ∧
  (∀ μ, Used D μ → ∀ Φ, X.T0 μ Φ ∈ X.Good μ hBot ∧
    ∀ F ∈ V.S.V0 μ, X.ev μ hBot (X.T0 μ Φ) F = X.rowUp Φ D.R.m (X.real (V.S.iota μ F))) ∧
  (∀ w Φ, X.T0 (D.what₂.muAt w) Φ ∈ X.IntAt (D.what₂.muAt w) hBot w 0) ∧
  (∀ v Φ, X.T0 D.what₂.mu0 Φ ∈ X.SzAt D.what₂.mu0 hBot v (C * (D.R.m : ℝ) * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum))

def lossINT (XD : DivX D) (X : LocV D V A) (C : ℝ) (G : ℕ) (k : X.KI) (w : D.what₂.places.Pl) : ℝ :=
  (vAdd (D.plEq w) ((G : ℕ) : D.what₂.LL) : ℝ) +
  (if D.what₂.places.resChar w ∣ D.host.condN then
      C * ((⨆ τ, XD.vdd (D.what₂.places.resChar w) τ) + 1) * (X.kdeg k : ℝ) * (D.what₂.places.ramIdx w : ℝ)
    else 0) +
  (X.kdepth k (D.what₂.places.resChar w) : ℝ) * (X.kdeg k : ℝ) * (D.what₂.places.ramIdx w : ℝ) +
  (X.kdepth k (D.what₂.places.resChar w) : ℝ) * (nAt D (D.what₂.places.resChar w) : ℝ) * (2 * (X.Nst : ℝ)) ^ 2 *
    (D.what₂.places.ramIdx w : ℝ)

def GamFun (X : LocV D V A) (C : ℝ) (G : X.KI → ℕ) : Prop :=
  ∀ k, 0 < G k ∧ Real.log (G k : ℝ) ≤ C * (D.R.f : ℝ) * (X.Nst : ℝ) * Real.log ((D.R.f : ℝ) * (X.Nst : ℝ))

def adm3 (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (C : ℝ) : Prop :=
  (∃ G : X.KI → ℕ, GamFun D X C G ∧ ∀ k w, (X.kTup k = D.what₂.mu0 ∨ X.kTup k = D.what₂.muAt w) →
    ¬ D.what₂.places.resChar w ∣ Ideal.absNorm D.host.ccK → ∀ x ∈ (X.kS k).L, ∀ φ ∈ (X.kT k).dualL,
      -(lossINT D XD X C (G k) k w) ≤ (vAdd (D.plEq w) (φ (X.kmap k x)) : ℝ)) ∧
  (∀ k, X.kTup k = D.what₂.mu0 →
    Formalism.HN.htMap (X.kS k).b (X.kS k).X (X.kT k).b (X.kT k).X (X.kmap k) ≤
      C * (D.R.f : ℝ) * (X.Nst : ℝ) ^ 2 * (L.sc.L + X.weightedLogLevelSum) * L.sc.b)

def ArchimedeanSignatureMatching (X : LocV D V A) : Prop :=
  (∀ (W V : X.th.Sp) (t' : ℕ) (S : X.th.PlS) (Φ1 Φ2 : X.th.Dat W V) (f1 f2 : X.th.AF W),
    X.th.rk V = X.th.rk W + t' → 2 ≤ t' → X.th.witt V < t' → X.th.fac W V S Φ1 Φ2 f1 f2 →
    f1 ∈ X.th.cusp W → f2 ∈ X.th.cusp W → X.th.lowerZero W V Φ1 f1 → X.th.lowerZero W V Φ2 f2 →
      X.th.pet V (X.th.lift W V Φ1 f1) (X.th.lift W V Φ2 f2) =
        X.th.cR W V * X.th.embC W f1 f2 * (X.th.LS W V S Φ1 f1 ((1 + (t' : ℝ)) / 2) / X.th.dS W V S Φ1) *
          X.th.Zloc W V S Φ1 Φ2 f1 f2) ∧
  (∀ (W V : X.th.Sp) (Φ : X.th.Dat W V) (f : X.th.AF W),
    f ∈ X.th.cusp W → X.th.lowerZero W V Φ f → X.th.lift W V Φ f ∈ X.th.cusp V)

def adm8 (X : LocV D V A) : Prop := Formalism.MainNotions.SchurIrreducible.DiscreteSeriesPositivity X.ar

end admitted

def adm9 (D : D7) (L : SizeData₂ D) : Prop := Real.log (q0 D : ℝ) ≤ L.sc.L

theorem auxiliary_prime_odd (D : D7) : q0 D % 2 = 1 := by
  have h2 : 2 ∣ D.host.QS := by
    have ht := D.host.tower_dvd
    exact dvd_trans (dvd_pow_self 2 (by omega)) ht
  have h2c : 2 ∣ LevelStarExponents.condE D := by
    unfold LevelStarExponents.condE
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2 _) _
  have h2k : 2 ∣ rPr D * LevelStarExponents.condE D := dvd_mul_of_dvd_right h2c _
  rw [← Nat.mod_mod_of_dvd (q0 D) h2k, (auxiliary_prime_mem D).2.1]
  all_goals norm_num

theorem auxiliary_prime_admissible_of_prime (D : D7) (L : SizeData₂ D) (p : ℕ) (hp : p.Prime) (h1 : p % (rPr D * LevelStarExponents.condE D) = 1)
    (h2 : ¬ p ∣ Ideal.absNorm D.host.ccK) (h3 : Real.log (p : ℝ) ≤ L.sc.L) : adm9 D L := by
  unfold adm9
  have hle : q0 D ≤ p := Nat.sInf_le ⟨hp, h1, h2⟩
  have hq : 0 < q0 D := (auxiliary_prime_mem D).1.pos
  calc Real.log (q0 D : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hle)
    _ ≤ L.sc.L := h3

def covR {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup (Set.range fun x : EuclideanSpace ℝ (Fin n) => Metric.infDist x (Λ : Set (EuclideanSpace ℝ (Fin n))))

def dualSet {n : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ Λ, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

def lam1 {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf {r : ℝ | ∃ y ∈ S, y ≠ 0 ∧ r = ‖y‖}

def adm10 (C : ℝ) : Prop :=
  ∀ (n : ℕ) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
    covR Λ * lam1 (dualSet Λ) ≤ C * (n : ℝ)

def adm11 : Prop := Formalism.HN.SlopeIneqMean

section Adm2

variable (D : D7) {V : Lev D} {A : AmbForm D V.S}

def adm13 (X : LocV D V A) : Prop :=
  Formalism.MainNotions.SchurIrreducible.DiscreteSeriesBlattner X.ar ∧
  Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X.ar ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X.ar ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X.ar ∧ Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X.ar ∧
    Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X.ar

def adm14 (X : LocV D V A) : Prop :=
  ∀ μ, Used D μ → ∀ h i, IsPath D.R.m h → Flippable D.R.m h i →
    4 * D.R.m + 2 < D.R.t + X.s → 2 * D.R.m + 1 < D.R.r + h i * D.R.t + i * X.s →
    (∀ τ (hj : h i < D.R.m), ((2 * (D.R.r + h i * D.R.t + i * X.s) + D.R.t + X.s : ℕ) : ℚ) <
      2 * ((D.hc τ).e ⟨h i, hj⟩ + X.cInf (D.R.m - i) τ)) →
    ∀ (T : X.PD μ h) (T' : X.PD μ (flipP h i)), X.pA μ h i T' = X.pB μ h i T →
      ∀ F ∈ V.S.V0 μ, X.ev μ (flipP h i) T' F = X.csq μ i (h i) • X.ev μ h T F

def gLoss (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) (w : D.what₂.places.Pl) : ℝ :=
  if D.what₂.places.resChar w ∈ S0pr D then
    C * (X.eAt (D.what₂.places.resChar w) : ℝ) * (nAt D (D.what₂.places.resChar w) : ℝ) * (X.Nst : ℝ) *
      (L.sc.b + (X.Nst : ℝ)) * (D.what₂.places.ramIdx w : ℝ)
  else 0

def adm15 (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (C : ℝ) : Prop :=
  ∀ μ, Used D μ → ∀ h i, IsPath D.R.m h → Flippable D.R.m h i → ∀ T ∈ X.Good μ h,
    ∃ T' ∈ X.Good μ (flipP h i), X.pA μ h i T' = X.pB μ h i T ∧
      (∀ w a, D.what₂.places.resChar w ∉ XD.Qp μ → T ∈ X.IntAt μ h w a →
        T' ∈ X.IntAt μ (flipP h i) w (a + gLoss D L X C w)) ∧
      (∀ v a, T ∈ X.SzAt μ h v a → T' ∈ X.SzAt μ (flipP h i) v (a + C * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum))

def adm16 (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) : Prop :=
  ∃ rL : D.what₂.Tup → D.what₂.LL,
    (∀ μ, Used D μ → D.what₂.embLL (rL μ) = X.cTot μ / X.cTot D.what₂.mu0) ∧ rL D.what₂.mu0 = 1 ∧
    ∑ w ∈ X.plS, lw D.what₂.LL (D.plEq w) * (vAdd (D.plEq w) (rL (D.what₂.muAt w)) : ℝ) ≤
      L.sc.x ^ C * (D.R.f : ℝ) * L.sc.b * L.sc.L

def adm17 (V : Lev D) : Prop := V.S.AIntegral

def adm18 (X : LocV D V A) : Prop :=
  ∀ μ, Used D μ → ∀ i j, i < D.R.m → j < D.R.m → X.csq μ i j ≠ 0

def adm19 (X : LocV D V A) : Prop :=
  ∀ μ, Used D μ → ∀ T ∈ X.Good μ (hTop D.R.m), ∀ (a : X.I0) (q : (A.MtH μ).V),
    A.jAmb μ q ∈ V.S.V0 μ →
      X.th.per (X.vx D.R.m 0) (D.R.m - 1) true (X.tst a) (X.ev μ (hTop D.R.m) T (A.jAmb μ q)) =
        X.App * D.what₂.embLL (X.vT μ T a q)

def HHfp (L : SizeData₂ D) (X : LocV D V A) (C C' : ℝ) : ℝ :=
  C * (D.R.f : ℝ) * L.sc.b * (X.Nst : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * L.sc.L + (D.R.m : ℝ) * X.weightedLogLevelSum) +
    C' * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (X.Nst : ℝ) ^ 2 * (L.sc.L + X.weightedLogLevelSum) * L.sc.b

def HHn (L : SizeData₂ D) (X : LocV D V A) (C C' : ℝ) : ℝ :=
  HHfp D L X C C + L.sc.x ^ C' * (D.R.f : ℝ) * L.sc.b * L.sc.L

def adm20 (L : SizeData₂ D) (X : LocV D V A) (C C' : ℝ) : Prop :=
  ∃ (S : Finset D.what₂.places.Pl) (del : D.what₂.places.Pl → ℝ), (∀ w, 0 ≤ del w) ∧ (∀ w, w ∉ S → del w = 0) ∧
    (∀ w, ∀ (Tf : X.DatX → X.PD (D.what₂.muAt w) (hTop D.R.m)) (a : ℝ), 0 ≤ a →
      (∀ Φ, Tf Φ ∈ X.Good (D.what₂.muAt w) (hTop D.R.m) ∧ Tf Φ ∈ X.IntAt (D.what₂.muAt w) (hTop D.R.m) w a) →
      ∀ q ∈ (A.MtH (D.what₂.muAt w)).L, A.jAmb (D.what₂.muAt w) q ∈ V.S.V0 (D.what₂.muAt w) → ∀ ψ ∈ X.MM.L,
        -(a + del w) ≤ (vAdd (D.plEq w) (X.vMap (D.what₂.muAt w) Tf q ψ) : ℝ)) ∧
    2 * ∑ w ∈ S, lw D.what₂.LL (D.plEq w) * del w ≤ HHfp D L X C C'

def adm21 (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) : Prop :=
  ∀ (Tf : X.DatX → X.PD D.what₂.mu0 (hTop D.R.m)) (a : ℝ), 0 ≤ a →
    (∀ Φ, Tf Φ ∈ X.Good D.what₂.mu0 (hTop D.R.m) ∧ ∀ v, Tf Φ ∈ X.SzAt D.what₂.mu0 (hTop D.R.m) v a) →
    Formalism.HN.htMap (A.MtH D.what₂.mu0).b (A.MtH D.what₂.mu0).X X.MM.dualB X.MM.dualX
              (X.vMap D.what₂.mu0 Tf) ≤
      C * (D.R.f : ℝ) * (D.R.m : ℝ) * (X.Nst : ℝ) * L.sc.b * L.sc.L +
        C * (D.R.m : ℝ) ^ 2 * (X.Nst : ℝ) ^ 2 * X.weightedLogLevelSum + 4 * a

def adm22 (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) : Prop :=
  X.MM.muMaxDual ≤ (1 + lamC D) * L.sc.x ^ C

def adm23 (X : LocV D V A) : Prop :=
  ∀ u : V.EE, u ≠ 0 → ∃ u1 ∈ X.U1, u1 ≠ 0 ∧
    ((∀ Φ a, X.fPer Φ a (X.real u) = 0) → ∀ Φ a, X.fPer Φ a u1 = 0)

def FrobeniusExpansionCongruence (X : LocV D V A) : Prop :=
  ∀ u1 ∈ X.U1, u1 ≠ 0 → ∃ ξ ∈ X.Irr, X.lamPer ξ u1 ≠ 0

def HerrExtensionClause (X : LocV D V A) : Prop :=
  ∀ (Φ' : X.DatS) (a : X.I0), ∀ u1 ∈ X.U1,
    ∑ Φ, X.cmb Φ' Φ * X.fPer Φ a u1 =
      X.Ap * (X.volS : ℂ) * X.lamPer (X.dnAll (X.datPof Φ') D.R.m (X.psiMS a)) u1

def adm26 (X : LocV D V A) : Prop :=
  ∀ ξ ∈ X.Irr, ∀ i, i < D.R.m → X.Dn i (X.phi0 i) (X.upChain ξ (i + 1)) = X.ralVal ξ i • X.upChain ξ i

def HerrCocycleExtensionClass (X : LocV D V A) : Prop :=
  (∀ ξ ∈ X.Irr, ∀ c, 1 ≤ c → c ≤ D.R.m → X.LSpi ξ c ≠ 0) ∧
  (∀ n' c' c, 1 ≤ n' → n' ≤ X.s - 1 → 1 ≤ c → c < c' → c' ≤ D.R.m → X.Lchi n' c' c ≠ 0) ∧
  (∀ i, i < D.R.m → X.dSv i ≠ 0 ∧ 0 < X.ZS i ∧ X.cRal i ≠ 0)

def FontaineFormalProperties (X : LocV D V A) : Prop := X.Ap ≠ 0

def qnAt (A : AmbForm D V.S) (v : InfinitePlace D.what₂.LL) (q : (A.MtH D.what₂.mu0).V) : ℝ :=
  ⨅ q' : {q' : (A.MtH D.what₂.mu0).V // A.jAmb D.what₂.mu0 q' ∈ V.S.Usp D.what₂.mu0},
    Formalism.HermitianLatticesTheory.normAt (A.MtH D.what₂.mu0).b (A.MtH D.what₂.mu0).X v (q + q'.1)

def AmbientMetricLowerBound (XD : DivX D) (X : LocV D V A) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : V.S.RR.V) (q : (A.MtH D.what₂.mu0).V), A.jAmb D.what₂.mu0 q ∈ V.S.V0 D.what₂.mu0 →
    V.S.jEE x = V.S.iota D.what₂.mu0 (A.jAmb D.what₂.mu0 q) →
    X.kapV (InfinitePlace.mk s) * Real.exp (⨅ σ : Fin V.n, ∑ j ∈ SizeData₂.lifts D, XD.logLam j (V.ft σ) s) *
        qnAt D A (InfinitePlace.mk s) q ^ 2 ≤
      Formalism.HermitianLatticesTheory.normAt V.S.RR.b V.S.RR.X (InfinitePlace.mk s) x ^ 2 ∧
    Formalism.HermitianLatticesTheory.normAt V.S.RR.b V.S.RR.X (InfinitePlace.mk s) x ^ 2 ≤
      X.kapV (InfinitePlace.mk s) * Real.exp (⨆ σ : Fin V.n, ∑ j ∈ SizeData₂.lifts D, XD.logLam j (V.ft σ) s) *
        qnAt D A (InfinitePlace.mk s) q ^ 2

end Adm2

structure Consts where
  Cf : ℝ
  Cp : ℝ
  CPP : ℝ
  Cint : ℝ
  Clin : ℝ
  Ctr : ℝ
  Cten : ℝ
  Cgr : ℝ
  Cval : ℝ
  Cfp : ℝ
  Cfp' : ℝ
  Cip : ℝ
  Cmm : ℝ

section Stmt

variable (D : D7) {V : Lev D} {A : AmbForm D V.S}

def HypGap (X : LocV D V A) : Prop :=
  ∀ τ (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * (X.Nst : ℚ) ^ 3 < (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

def FunDataAt (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) : Prop :=
  Real.log (q0 D : ℝ) ≤ C * L.sc.L ∧
    ∀ i, 0 < X.nb i ∧ |Real.log ((X.nb i : ℚ) : ℝ)| ≤ C * (D.R.m : ℝ) * (D.R.f : ℝ) * L.sc.L

def HypSz (L : SizeData₂ D) (X : LocV D V A) (K : Consts) : Prop :=
  (D.R.f : ℝ) ≤ K.Cf * ((D.R.r : ℝ) + 1) ^ 2 ∧ (lamC D ≤ L.sc.b ∧ (X.Nst : ℝ) ≤ L.sc.b) ∧
  (D.R.k : ℝ) ≤ L.sc.x ^ K.Cp ∧ (D.R.t : ℝ) ≤ L.sc.x ^ K.Cp ∧
  (∀ i, Real.log (D.host.g i : ℝ) ≤ K.Cp * L.sc.L) ∧
  Real.log (D.host.pde : ℝ) ≤ K.Cp * L.sc.L ∧ Real.log (D.host.pde' : ℝ) ≤ K.Cp * L.sc.L ∧
  Real.log (LevelStarExponents.condE D : ℝ) ≤ L.sc.L ∧
  Real.log |(NumberField.discr D.host.E : ℝ)| ≤ K.Cp * (D.R.f : ℝ) * L.sc.L ∧
  (Real.log (Ideal.absNorm D.host.ccK : ℝ) ≤ L.sc.L ∧ (Ideal.absNorm D.host.ccK : ℝ) ≤ K.Cp * (D.host.d : ℝ)) ∧
  X.ev0 = eV0 D L K.CPP ∧
  0 < V.n ∧ 0 ≤ K.Cgr ∧ FunDataAt D L X K.Cp

theorem auxiliary_prime_eq_least_of_size {L : SizeData₂ D} {X : LocV D V A} {K : Consts} (h : HypSz D L X K)
    (hC : K.Cp < (D.host.QS : ℝ) * (D.host.q : ℝ)) :
    q0 D = sInf {p : ℕ | p.Prime ∧ p % (rPr D * LevelStarExponents.condE D) = 1} := by
  unfold HypSz at h
  obtain ⟨-, -, -, -, -, -, -, -, -, ⟨-, hN⟩, -⟩ := h
  apply auxiliary_prime_eq_least D
  have hd : (0 : ℝ) < (D.host.d : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hlt : (Ideal.absNorm D.host.ccK : ℝ) < (LevelStarExponents.condE D : ℝ) := by
    unfold LevelStarExponents.condE
    push_cast
    calc (Ideal.absNorm D.host.ccK : ℝ) ≤ K.Cp * (D.host.d : ℝ) := hN
      _ < (D.host.QS : ℝ) * (D.host.q : ℝ) * (D.host.d : ℝ) := mul_lt_mul_of_pos_right hC hd
  exact_mod_cast hlt

def Hyp (L : SizeData₂ D) (X : LocV D V A) (K : Consts) : Prop :=
  HypGap D X ∧ HypSz D L X K

def RRDef (_X : LocV D V A) : Prop :=
  Set.range V.S.jEE = llSpan D.what₂.embLL (V.S.RRset D.what₂.mu0) ∧ V.S.RRDef

def Conclusion1 (X : LocV D V A) : Prop :=
  (∀ μ, Used D μ → IsRational (X.ltPts μ) (V.S.Usp μ)) ∧
  IsLLForm D.what₂.embLL (llSpan D.what₂.embLL (V.S.RRset D.what₂.mu0)) ∧
  (∀ μ, Used D μ → V.S.RRset μ ⊆ llSpan D.what₂.embLL (V.S.RRset D.what₂.mu0)) ∧
  (∀ μ, Used D μ → X.EELL = llSpan D.what₂.embLL (V.S.RRset μ))

def JEEDef (X : LocV D V A) : Prop := Set.range V.S.jEE = X.EELL

theorem rrset_sub_EELL {X : LocV D V A} (h : Conclusion1 D X) : V.S.RRset D.what₂.mu0 ⊆ X.EELL := by
  unfold Conclusion1 at h
  intro x hx
  rw [h.2.2.2 D.what₂.mu0 (Or.inl rfl)]
  simp only [llSpan, Set.mem_setOf_eq]
  exact ⟨{x}, fun _ => 1, by simpa using hx, by simp⟩

theorem rrDef_of_jEEDef {X : LocV D V A} (h : Conclusion1 D X) (hJ : JEEDef D X) (hR : V.S.RRDef) : RRDef D X := by
  unfold Conclusion1 at h
  unfold RRDef
  unfold JEEDef at hJ
  exact ⟨hJ.trans (h.2.2.2 D.what₂.mu0 (Or.inl rfl)), hR⟩

def Conclusion2 (L : SizeData₂ D) (X : LocV D V A) (C : ℝ) : Prop :=
  RRDef D X → Formalism.HN.muMaxDef V.S.RR.b (unitMetricFrames X) V.S.RR.L ≤ L.sc.x ^ C * L.sc.b

def PointsLemma (L : SizeData₂ D) (X : LocV D V A) (C C' : ℝ) : Prop :=
  RRDef D X → ∃ P : V.S.RR.V →ₗ[D.what₂.LL] Module.Dual D.what₂.LL X.MM.V, Function.Injective P ∧
    (∀ x i, D.what₂.embLL (P x (X.MM.b i)) = X.PSI (V.S.jEE x) i) ∧
    ∃ (S : Finset D.what₂.places.Pl) (a : D.what₂.places.Pl → ℝ), (∀ w, w ∉ S → a w = 0) ∧
      (∀ w, ∀ x ∈ V.S.RR.L, ∀ ψ ∈ X.MM.L, P x ψ ≠ 0 → -(a w) ≤ (vAdd (D.plEq w) (P x ψ) : ℝ)) ∧
      Formalism.HN.htMap V.S.RR.b (unitMetricFrames X) X.MM.dualB X.MM.dualX P +
        2 * ∑ w ∈ S, lw D.what₂.LL (D.plEq w) * a w ≤ HHn D L X C C'

def AdmTools (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (K : Consts) : Prop :=
  adm1 D X ∧ adm3 D L XD X K.Cint ∧ ArchimedeanSignatureMatching D X ∧ adm8 D X ∧ adm10 K.Ctr ∧
    adm13 D X

def AdmCore (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (K : Consts) : Prop :=
  adm2 D L XD X K.Cgr ∧ adm9 D L ∧ adm11 ∧ adm14 D X ∧ adm15 D L XD X K.Cgr ∧ adm16 D L X K.Cval ∧ adm17 D V ∧
    adm18 D X ∧ adm19 D X ∧ adm20 D L X K.Cfp K.Cfp' ∧ adm21 D L X K.Cip ∧ adm22 D L X K.Cmm ∧ adm23 D X ∧
    FrobeniusExpansionCongruence D X ∧ HerrExtensionClause D X ∧ adm26 D X ∧ HerrCocycleExtensionClass D X ∧ FontaineFormalProperties D X ∧ AmbientMetricLowerBound D XD X

def admitted (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (K : Consts) : Prop :=
  AdmTools D L XD X K ∧ AdmCore D L XD X K

def aux₃ (L : SizeData₂ D) (X : LocV D V A) (C Ch Ch' : ℝ) : Prop :=
  Conclusion1 D X ∧ Conclusion2 D L X C ∧ PointsLemma D L X Ch Ch'

def BoundsOfCoreAdmissibleData (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (K : Consts) (C Ch Ch' : ℝ) : Prop :=
  Hyp D L X K → AdmCore D L XD X K → aux₃ D L X C Ch Ch'

def Stmt (L : SizeData₂ D) (XD : DivX D) (X : LocV D V A) (K : Consts) (C Ch Ch' : ℝ) : Prop :=
  Hyp D L X K → admitted D L XD X K → aux₃ D L X C Ch Ch'

end Stmt

abbrev ObjClass : Type 1 :=
  ∀ {D : D7} (_ : SizeData₂ D) (_ : DivX D) {V : Lev D} {A : AmbForm D V.S}, LocV D V A → Prop

def RealisationStatementAll (𝒪 : ObjClass) : Prop :=
  ∀ K : Consts, ∃ C Ch Ch' : ℝ, ∀ (D : D7) (L : SizeData₂ D) (XD : DivX D) (V : Lev D) (A : AmbForm D V.S) (X : LocV D V A),
    𝒪 L XD X → Stmt D L XD X K C Ch Ch'

def Conclusion1Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i) (XF x hx i)

def Conclusion2Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (XF x hx i) C

def Conclusion3Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) (C C' : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, PointsLemma (Fm.D x i) (Fm.L x i) (XF x hx i) C C'

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) (K : Consts) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    HypSz (Fm.D x i) (Fm.L x i) (XF x hx i) K ∧ admitted (Fm.D x i) (Fm.L x i) (Fm.X x i) (XF x hx i) K

def InClass (𝒪 : ObjClass) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), 𝒪 (Fm.L x i) (Fm.X x i) (XF x hx i)

def ErrorExponentStatement (K : Consts) (C Ch Ch' : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i)}
    {AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S}
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)) : Prop :=
  AdmF Fm XF K → Conclusion1Family Fm XF ∧ Conclusion2Family Fm XF C ∧ Conclusion3Family Fm XF Ch Ch'

def KudlaFamilyStatement (𝒪 : ObjClass) (K : Consts) (C Ch Ch' : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ (VF : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Lev (Fm.D x i))
    (AF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), AmbForm (Fm.D x i) (VF x hx i).S)
    (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LocV (Fm.D x i) (VF x hx i) (AF x hx i)),
    InClass 𝒪 Fm XF → ErrorExponentStatement K C Ch Ch' Fm XF

def FamilyErrorExponentBound (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ K : Consts, ∃ C Ch Ch' : ℝ, ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CH : ℝ), 𝒞 Fm → KudlaFamilyStatement 𝒪 K C Ch Ch' Fm CH

def cpOf (l : List ℝ) : ℝ := max (l.getD 0 0 + 1) (max (l.getD 6 0 + 1) (max (l.getD 7 0) (max (l.getD 8 0) 5)))

theorem cpOf_cOut {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) :
    cpOf Fm.cOut = max (Fm.Ct + 1) (max (Fm.CYL + 1) (max Fm.Cpde (max Fm.CccK 5))) := rfl

def Consts.atFam (K : Consts) (l : List ℝ) : Consts :=
  { K with
    Cp := max K.Cp (cpOf l)
    Cval := K.Cval * max K.Cp (cpOf l)
    Cfp' := K.Cfp' * max K.Cp (cpOf l)
    Cmm := K.Cmm * max K.Cp (cpOf l) }

def ClosedAbsoluteShare (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ K : List ℝ → Consts, ∃ C Ch Ch' : List ℝ → ℝ,
    Formalism.MainNotions.Closed 𝒞 (fun Fm CH => KudlaFamilyStatement 𝒪 (K Fm.cOut) (C Fm.cOut) (Ch Fm.cOut) (Ch' Fm.cOut) Fm CH)

theorem LocV.s_eq {D : D7} {V : Lev D} {A : AmbForm D V.S} (X : LocV D V A) : X.s = D.R.r + 6 := by
  have h1 := X.s_odd
  have h2 := X.s_lo
  have h3 := X.s_hi
  have hk := D.R.k_even
  have hm := D.R.m_even
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := hk
  obtain ⟨c, hc⟩ := hm
  omega

theorem hypGap_fam {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) {V : Lev (Fm.D x i)}
    {A : AmbForm (Fm.D x i) V.S} (X : LocV (Fm.D x i) V A) : HypGap (Fm.D x i) X := by
  intro τ j h
  have h1 := ((Fm.params x hx i).nodes_gap τ j.1 h).1
  have h2 := (Fm.params x hx i).heightBound_ge_rank_cubic
  have h3 := h2.trans h1
  have hN : ((X.Nst : ℕ) : ℝ) = ((Fm.D x i).R.k : ℝ) + (Fm.D x i).R.m * ((Fm.D x i).R.t + ((Fm.D x i).R.r + 6) + 1) := by
    unfold LocV.Nst
    rw [X.s_eq]
    push_cast
    ring
  rw [← hN] at h3
  have h4 : (((Fm.D x i).R.t : ℝ) + 2 * ((X.Nst : ℕ) : ℝ) ^ 3) <
      ((((Fm.D x i).hc τ).b ⟨j.1 + 1, h⟩ - ((Fm.D x i).hc τ).b ⟨j.1, by omega⟩ : ℚ) : ℝ) := by linarith
  have h5 : ((((Fm.D x i).R.t : ℚ) + 2 * ((X.Nst : ℕ) : ℚ) ^ 3 : ℚ) : ℝ) <
      ((((Fm.D x i).hc τ).b ⟨j.1 + 1, h⟩ - ((Fm.D x i).hc τ).b ⟨j.1, by omega⟩ : ℚ) : ℝ) := by
    push_cast
    push_cast at h4
    exact h4
  exact (Rat.cast_lt (K := ℝ)).1 h5

theorem stmtFam_of_all (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) (h : RealisationStatementAll 𝒪) : FamilyErrorExponentBound 𝒪 𝒞 := by
  intro K
  obtain ⟨C, Ch, Ch', hK⟩ := h K
  refine ⟨C, Ch, Ch', ?_⟩
  intro eps Fm CH _ VF AF XF hIn hAdm
  obtain ⟨x0, hx0⟩ := hAdm
  have key : ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      aux₃ (Fm.D x i) (Fm.L x i) (XF x hx i) C Ch Ch' := by
    intro x hx hle i
    obtain ⟨hS, hA⟩ := hx0 x hx hle i
    exact hK (Fm.D x i) (Fm.L x i) (Fm.X x i) (VF x hx i) (AF x hx i) (XF x hx i) (hIn x hx i)
      ⟨hypGap_fam Fm x hx i (XF x hx i), hS⟩ hA
  exact ⟨⟨x0, fun x hx hle i => (key x hx hle i).1⟩, ⟨x0, fun x hx hle i => (key x hx hle i).2.1⟩,
    ⟨x0, fun x hx hle i => (key x hx hle i).2.2⟩⟩

theorem stmtClosed_of_fam (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) (h : FamilyErrorExponentBound 𝒪 𝒞) : ClosedAbsoluteShare 𝒪 𝒞 := by
  intro K
  refine ⟨fun l => Classical.choose (h (K l)),
    fun l => Classical.choose (Classical.choose_spec (h (K l))),
    fun l => Classical.choose (Classical.choose_spec (Classical.choose_spec (h (K l)))), ?_⟩
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hC _ => ?_⟩⟩
  exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (h (K Fm.cOut)))) Fm CH hC

end Formalism.MainNotions.AbsolutelyIrreducibleSpan
