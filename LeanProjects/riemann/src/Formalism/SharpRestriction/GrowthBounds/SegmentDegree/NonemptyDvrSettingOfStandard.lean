import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

structure Dat (n' r : ℕ) where
  F : Frames n' r
  deg : Fin n' → ℕ
  L₁ : ℕ
  N₁ : ℕ
  Ns : ℕ
  E₀ : ℕ
  mStar : ℕ
  E' : Fin n' → ℕ
  a : ℝ
  Y : ℝ
  Q : ℝ
  CLa : ℝ
  Ck : ℝ

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

structure Hyp : Prop where
  prime : p.Prime
  even : Even n'
  p13 : 13 ≤ p
  r2 : 2 ≤ r
  valid : X.F.Valid X.L₁ X.N₁
  degs : ∀ t ∈ X.F.TT, X.a ≤ (X.deg t : ℝ) ∧ (X.deg t : ℝ) ≤ 2 * X.a
  card : ∀ j : ℤ, (X.F.letters j).card ≤ X.Ns
  NsN₁ : X.Ns ≤ X.N₁
  NsN : X.Ns ≤ 2 * X.F.TT.card
  NsK : X.Ns + r ≤ K
  twist : ∀ j : ℤ, ∀ x ∈ X.F.letters j, (p : ℝ) ^ X.F.dist j x ≤ X.Q
  Y1 : 1 ≤ X.Y
  P1 : X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a ≤ ((r + K : ℕ) : ℝ)
  P2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ ((X.L₁ : ℤ) - 1)
  E'le : ∀ t ∈ X.F.TT, X.E' t ≤ X.E₀
  P3 : 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a

def k : ℝ := ((r + K : ℕ) : ℝ)

def La : ℝ := X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a

def Bo (j x : ℤ) : ℝ :=
  (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (p : ℝ) ^ X.F.dist j (X.F.oldest j x)

def sg (j x : ℤ) : ℕ := ⌊X.Bo p j x / (k (r := r) K ^ 2 * X.Y)⌋₊

def mg (j x : ℤ) : ℤ := (X.mStar : ℤ) + (X.sg p K j x : ℤ)

def th (j x : ℤ) : ℝ := X.Bo p j x / 2

def o (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ X.F.dist j x) +
    (if Even x then (10 : ℝ) else 1) * X.a * (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ)))

def d : Fin n' → ℕ := fun t => if t ∈ X.F.TT then X.deg t - X.E' t else 0

variable [NeZero r] [NeZero K]

def XXs (O : Type) [CommRing O] (j : ℤ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (X.mg p K j) (X.th p j) (X.o p K j)

def gen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) := Gen O p K X.F (X.XXs p K O) X.d

def NN (O : Type) [CommRing O] : Submodule O (RRing O n' (r + K)) := Submodule.span O (X.gen p K O)

omit [NeZero n'] [NeZero r] [NeZero K] in

def bound (Crk : ℝ) : ℝ := (1 - Crk * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * k (r := r) K / X.Y) *
    ∏ t ∈ X.F.TT, ((Nat.choose (X.deg t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

def NNbar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.gen p K O)

end Dat

def RestDeg : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → 0 ≤ X.CLa →
    ∀ P ∈ X.NN p K O, ∀ mm ∈ P.support,
      (vsDeg mm : ℝ) ≤ 10 * (X.F.TT.card : ℝ) *
        (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + X.a * (p : ℝ) ^ (-(X.L₁ : ℤ)) + Dat.k (r := r) K * X.Q)

def RestSel : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ : Type) (s : Set (σ →₀ ℕ)), s.Finite →
    ∀ G : Set (MvPolynomial σ O), (∀ g ∈ G, g ∈ restrictSupport O s) →
    ∃ Sg : Submodule O (MvPolynomial σ O), Sg ≤ Submodule.span O G ∧
      (∃ T : Submodule O (MvPolynomial σ O), IsCompl Sg T) ∧
      (∃ (ιb : Type) (b : Module.Basis ιb O Sg), ∀ i, (b i : MvPolynomial σ O) ∈ G) ∧
      Module.finrank O Sg =
        Module.finrank (FF O) (Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G))

def RestRank (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.NNbar p K O) : ℝ)

theorem degSet_finite (n' k : ℕ) (d : Fin n' → ℕ) :
    {m : Fin n' × Fin k →₀ ℕ | ∀ t, ∑ c : Fin k, m (t, c) = d t}.Finite := by
  have hpi : (Set.pi Set.univ fun v : Fin n' × Fin k => Set.Iic (d v.1)).Finite :=
    Set.Finite.pi fun v => Set.finite_Iic _
  have hpre := Set.Finite.preimage (f := (Finsupp.equivFunOnFinite : (Fin n' × Fin k →₀ ℕ) → (Fin n' × Fin k → ℕ)))
    (fun a _ b _ hab => Finsupp.equivFunOnFinite.injective hab) hpi
  refine hpre.subset ?_
  intro m hm
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Finsupp.equivFunOnFinite_apply]
  intro v
  calc m v = m (v.1, v.2) := rfl
    _ ≤ ∑ c : Fin k, m (v.1, c) :=
        Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
    _ = d v.1 := hm v.1

theorem nonempty_dvr_setting_of_standard {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jW w) :
    Nonempty (UniformizedDVR p O) := by
  obtain ⟨hS, hw, -, -⟩ := h
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hw.not_isUnit
  refine ⟨⟨w, hw, ?_, ?_, hS.complete_O⟩⟩
  · rw [← hS.w_sq]; exact Ideal.pow_mem_of_mem _ hwm 2 (by norm_num)
  · rw [← hS.w_sq]; exact pow_ne_zero 2 hw0

theorem second_estimate_of_rank_bound (D : Formalism.BasicNotions.D7) (C₀ Crk : ℝ) (hC₀ : 0 < C₀) (hCrk : 0 < Crk)
    (hDeg : RestDeg) (hSel : RestSel) (hRank : AdmB D → RestRank C₀ Crk) : SecondPartClosed D := by
  intro hAdm
  refine ⟨C₀, hC₀, fun CLa Ck hCLa hCk => ⟨Crk, 10, hCrk, by norm_num, ?_⟩⟩
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jW w hSet hp13 r K _ _ hr2 F deg L₁ N₁ Ns E₀ mStar E' a Y Q
    hV hdeg hcard hNsN₁ hNsN hNsK htw hY hP1 hP2 hE' hP3
  obtain ⟨S⟩ := nonempty_dvr_setting_of_standard hSet
  let X : Dat n' r := ⟨F, deg, L₁, N₁, Ns, E₀, mStar, E', a, Y, Q, CLa, Ck⟩
  have hX : X.Hyp p K :=
    ⟨hSet.1.prime, hSet.1.even, hp13, hr2, hV, hdeg, hcard, hNsN₁, hNsN, hNsK, htw, hY, hP1, hP2, hE', hP3⟩
  have hrk := hRank hAdm p n' r K X O S hX hCLa hCk
  have hdg := hDeg p n' r K X O hX (hC₀.le.trans hCLa)
  obtain ⟨Sg, hle, hT, hb, hfr⟩ := hSel O (Fin n' × Fin (r + K)) _ (degSet_finite n' (r + K) X.d) (X.gen p K O)
    (fun g hg => by obtain ⟨x, -, l, -, -, h⟩ := hg; exact h)
  have hrk' : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank O Sg : ℝ) := by
    rw [hfr]; exact hrk
  refine ⟨⟨Sg, hle, hT, hb, hrk', ?_⟩, hdg⟩
  intro FFq _ _ hcardF
  have h6 : Fintype.card FFq ^ (r * (r + K - r)) ≤ nPl FFq (r + K) r :=
    hAdm.2.2.2.2.2.1 FFq (r + K) r (Nat.le_add_right r K)
  rw [hcardF, Nat.add_sub_cancel_left] at h6
  have hq : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by
    have : (0 : ℝ) < p := by exact_mod_cast hSet.1.prime.pos
    positivity
  have h6' : ((p : ℝ) ^ n') ^ (r * K) ≤ (nPl FFq (r + K) r : ℝ) := by exact_mod_cast h6
  have hn : (0 : ℝ) < (nPl FFq (r + K) r : ℝ) := lt_of_lt_of_le hq h6'
  rcases le_or_gt (X.bound K Crk) 0 with hb0 | hb0
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hb0 hn.le) (Nat.cast_nonneg _)
  · refine le_trans ?_ hrk'
    rw [zpow_neg, zpow_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hq h6') hb0.le

end Formalism.MainNotions.SelectionLemmas.Pf
