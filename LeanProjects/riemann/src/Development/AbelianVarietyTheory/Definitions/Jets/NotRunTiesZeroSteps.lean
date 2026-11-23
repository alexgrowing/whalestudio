import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7} {L : SizeData₂ D} {Pm : ParameterChoice' D L}

section General

variable (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def retie (O : OnObj S P oc) (ι : Bs.J → ℕ) : OnObj S P oc :=
  { O with
    E := fun v j => EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
    σ := fun _ j => sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    nnK := fun j => nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
    T := Tp.TO
    g1 := D.host.g 0
    g2 := D.host.g 1
    q1 := D.host.q
    dd := D.host.d
    sm := D.host.small
    k := D.R.k
    m := D.R.m
    f := D.R.f
    x := L.sc.x
    eps := L.sc.eps
    Sc := L.Sc
    eta := L.etaSz
    bp := L.sc.b'
    X2 := L.sc.X'' D.R.n
    vd := vd2 D
    wt := fun _ => 2 * (D.R.f : ℝ) * L.sc.b
    th := fun l => Formalism.UnitaryBoundIntegral.thl D.R.k l
    ad := fun _ => 0
    DF := ((Finset.univ.sup fun j : Bs.J => WeightAlgebra.DF (lR Tp hK (ι j)) : ℕ) : ℝ) }

theorem runTie_retie (O : OnObj S P oc) (ι : Bs.J → ℕ) (hι : ∀ j, InR D (ι j))
    (hs : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a)
    (hc : ∀ a : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) K a) = algebraMap (𝓞 D.host.E) K (T.Q.H.bar a)) :
    RunTie T EX Tp hK (retie T EX Tp hK O ι) ι where
  inR := hι
  star_eq := hs
  conj := hc
  E_eq _ _ := rfl
  σ_eq _ _ := rfl
  nn_eq _ := rfl
  T_eq := rfl
  jets_eq_fact := rfl
  g2_eq := rfl
  cmQuadraticForm_eq_alternatingForm := rfl
  dd_eq := rfl
  sm_eq := rfl
  k_eq := rfl
  m_eq := rfl
  f_eq := rfl
  x_eq := rfl
  eps_eq := rfl
  Sc_eq := rfl
  eta_eq := rfl
  bp_eq := rfl
  depthNumbers_threshold_eq := rfl
  vd_eq := rfl
  wt_eq _ := rfl
  th_eq _ := rfl
  ad_eq _ := rfl
  DF_ge j := by
    show _ ≤ ((Finset.univ.sup fun j : Bs.J => WeightAlgebra.DF (lR Tp hK (ι j)) : ℕ) : ℝ)
    exact_mod_cast Finset.le_sup (f := fun j : Bs.J => WeightAlgebra.DF (lR Tp hK (ι j))) (Finset.mem_univ j)

variable {T EX Tp hK} {O : OnObj S P oc} {ι : Bs.J → ℕ}

theorem tiePrimes (h : RunTie T EX Tp hK O ι) : DepthCond.TiePrimes O (numOf D L) :=
  ⟨h.jets_eq_fact, h.g2_eq, h.cmQuadraticForm_eq_alternatingForm, h.dd_eq, h.sm_eq⟩

theorem tieFK (h : RunTie T EX Tp hK O ι) : DepthCond.TieFK O (numOf D L) := by
  refine ⟨?_, h.k_eq⟩
  rw [h.f_eq]
  show ((2 * D.R.n : ℕ) : ℝ) = 2 * ((D.R.n : ℕ) : ℝ)
  push_cast
  ring

theorem tieT (h : RunTie T EX Tp hK O ι) : O.T = (((depOf T EX Tp hK).Q.T : ℕ) : ℝ) := h.T_eq

theorem b_eq (h : RunTie T EX Tp hK O ι) : O.b = L.sc.b := by
  unfold OnObj.b OnObj.xe Scale.b Scale.L
  rw [h.x_eq, h.eps_eq]

theorem wt_eq' (h : RunTie T EX Tp hK O ι) (j : Bs.J) : O.wt j = 2 * O.f * O.b := by
  rw [h.wt_eq, h.f_eq, b_eq h]

theorem th_zero (h : RunTie T EX Tp hK O ι) : O.th 0 = 0 ∧ O.th 1 = 0 := by
  have hk : (1 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h1 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ ((3 : ℝ) / 2) := Real.one_le_rpow hk (by norm_num)
  constructor
  · rw [h.th_eq, Formalism.UnitaryBoundIntegral.thl]
    convert Real.sSup_empty
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -, h3, hlt, -⟩
    rw [Nat.cast_zero, zero_pow (by omega)] at hlt
    linarith
  · rw [h.th_eq, Formalism.UnitaryBoundIntegral.thl]
    convert Real.sSup_empty
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -, -, hlt, -⟩
    rw [Nat.cast_one, one_pow] at hlt
    linarith

theorem not_runTies_zeroSteps (h : RunTie T EX Tp hK O ι) :
    ¬ RunTie T EX Tp hK ({ O with T := 0 } : OnObj S P oc) ι := by
  intro h'
  have h0 : (0 : ℝ) = (Tp.TO : ℝ) := h'.T_eq
  have := TO_pos Tp
  have : (0 : ℝ) < (Tp.TO : ℝ) := by exact_mod_cast this
  linarith

end General

theorem numOf_w (L : SizeData₂ D) {j : ℕ} (hj : InR D j) (z : RPl D.R) : (numOf D L).w j z = wj D j (plOf D z) := by
  have h1 : j - 1 < D.R.m := by have := hj.1; have := hj.2; omega
  unfold NumDatum.w NumDatum.eQ wj
  rw [dif_pos (show 1 ≤ j ∧ j ≤ (numOf D L).R.m from hj), dif_pos h1]
  rfl

theorem numOf_aPlus (L : SizeData₂ D) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (numOf D L).aPlus j z i = DV.aPlusQ D j (plOf D z) i := rfl

theorem numOf_aMinus (L : SizeData₂ D) (j : ℕ) (z : RPl D.R) (i : ℕ) :
    (numOf D L).aMinus j z i = DV.aMinusQ D j (plOf D z) i := rfl

theorem eTau_plOf_false (t : D.R.A) :
    (D.eTau (plOf D (false, t)) : D.R.GG) = D.R.tau1 t := by
  simp [plOf]

theorem eTau_plOf_true (t : D.R.A) :
    (D.eTau (plOf D (true, t)) : D.R.GG) = D.R.tau2 t := by
  simp [plOf]

theorem localExponent_small_prime (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (w : WeightFamilies.Wt D j)
    {p : ℕ} (hp : p ∈ D.host.small) :
    (depOf T EX Tp hK).Q.cP (WeightAlgebra.DF w) p = padicValNat p D.host.QS * c2 D w := by
  unfold DepPage.cP
  rw [if_pos (show (depOf T EX Tp hK).Q.IsRam p from Or.inl hp)]
  show ⌈vdOf D p * _⌉.toNat = _
  unfold vdOf c2
  rw [if_pos hp, Int.ceil_toNat, ← Nat.cast_mul, Nat.ceil_natCast]

theorem localExponent_two (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (w : WeightFamilies.Wt D j) :
    (depOf T EX Tp hK).Q.cP (WeightAlgebra.DF w) 2 = padicValNat 2 D.host.QS * c2 D w :=
  localExponent_small_prime T EX Tp hK w (Nat.mem_primeFactors.2
    ⟨Nat.prime_two, (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd, D.host.QS_pos.ne'⟩)

def intMap (T : Core D) : 𝓞 T.Q.c.F →+* 𝓞 D.what₂.LL :=
  (D.what₂.OtoLL.comp T.Q.eO.toRingHom).codRestrict (integralClosure ℤ D.what₂.LL) fun x =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) x).map (D.what₂.OtoLL.comp T.Q.eO.toRingHom).toIntAlgHom

def hostMap (D : D7) : 𝓞 D.host.E →+* D.what₂.LL := D.embE.comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem hostMap_conj (T : Core D) (a : 𝓞 D.host.E) : star (hostMap D a) = hostMap D (T.Q.H.bar a) := by
  apply D.what₂.embLL.injective
  rw [D.starLL_cx]
  have e : ∀ b : 𝓞 D.host.E, D.what₂.embLL (hostMap D b) = D.host.φ₀ (b : D.host.E) := fun b =>
    DFunLike.congr_fun D.embE_φ₀ (b : D.host.E)
  rw [e, e, T.Q.H.bar_eq, IsCMField.complexEmbedding_complexConj]

theorem intMap_integral (T : Core D) :
    letI := (intMap T).toAlgebra
    Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 D.what₂.LL) := by
  letI := (intMap T).toAlgebra
  exact Algebra.IsIntegral.tower_top (R := ℤ)

theorem exists_runTie (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (ι : Bs.J → ℕ) (hι : ∀ j, InR D (ι j)) :
    letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar T.Q.H
    letI := (intMap T).toAlgebra
    haveI := intMap_integral T
    letI := (hostMap D).toAlgebra
    RunTie T EX Tp hK (retie T EX Tp hK O ι) ι := by
  letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar T.Q.H
  letI := (intMap T).toAlgebra
  haveI := intMap_integral T
  letI := (hostMap D).toAlgebra
  exact runTie_retie T EX Tp hK O ι hι (fun _ => rfl) (hostMap_conj T)

theorem exists_runTie_toy (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    (v0 : InfinitePlace D.what₂.LL) (Tw0 : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (j : ℕ) (hj : InR D j) :
    letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar T.Q.H
    letI := (intMap T).toAlgebra
    haveI := intMap_integral T
    letI := (hostMap D).toAlgebra
    ∃ O : OnObj (exampleIndefiniteData D.what₂.LL v0 Tw0 0) Unit exampleC, RunTie T EX Tp hK O fun _ => j :=
  ⟨_, exists_runTie T EX Tp hK (exampleObject D.what₂.LL v0 Tw0) (fun _ => j) fun _ => hj⟩

theorem inR_one (D : D7) : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩

end GlobalTheory.RunDepth.Model
