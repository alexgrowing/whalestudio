import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum

def ratG (D : D7) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {g | ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ}

def intG (D : D7) (N : ℕ) : Subgroup (GA D N) :=
  Subgroup.closure {k | IntG D (k : GL (Fin N) (AE D))}

abbrev Cls (D : D7) (N : ℕ) (J : Subgroup (GA D N)) : Type :=
  DoubleCoset.Quotient (ratG D N : Set (GA D N)) (J : Set (GA D N))

def gam (D : D7) {N : ℕ} (J : Subgroup (GA D N)) (g : GA D N) : ℕ :=
  Nat.card {γ : GA D N // γ ∈ ratG D N ∧ g⁻¹ * γ * g ∈ J}

theorem inc_inj (D : D7) : Function.Injective (inc D) := by
  haveI : Nontrivial (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 ℚ)
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
      ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField ℚ)⟩
    refine ⟨0, 1, fun h => ?_⟩
    have h2 : (0 : v.adicCompletion ℚ) = 1 := congrArg (fun x : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ => x v) h
    exact zero_ne_one h2
  haveI : Nontrivial (AE D) :=
    (Algebra.TensorProduct.includeRight_injective (algebraMap ℚ D.host.E).injective :
      Function.Injective (Algebra.TensorProduct.includeRight :
        IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AE D)).nontrivial
  exact (inc D).injective

theorem ratG_eq_ratPts (D : D7) (N : ℕ) :
    ratG D N = (Formalism.UG.ratPts (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)).subgroupOf (GA D N) := by
  apply le_antisymm
  · rw [ratG, Subgroup.closure_le]
    rintro g ⟨γ, hγ⟩
    have h1 : (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    have hg : ((g.1 : Matrix (Fin N) (Fin N) (AE D)).map (sgA D)).transpose *
        (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) * (g.1 : Matrix (Fin N) (Fin N) (AE D)) =
        (1 : Matrix (Fin N) (Fin N) D.host.E).map (inc D) := g.2
    have hc : ((γ.map D.host.conj).transpose).map (inc D) = ((γ.map (inc D)).map (sgA D)).transpose := by
      ext i j
      simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]
    have hu : (γ.map D.host.conj).transpose * γ = 1 := by
      apply Matrix.map_injective (inc_inj D)
      unfold IsRat at hγ
      rw [hγ, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
      exact hg.trans h1.symm
    refine ⟨⟨γ, _, mul_eq_one_comm.1 hu, hu⟩, ?_, Units.ext hγ.symm⟩
    change (γ.map D.host.conj).transpose * 1 * γ = 1
    rw [Matrix.mul_one, hu]
  · rintro g ⟨u, -, hu⟩
    exact Subgroup.subset_closure ⟨(u : Matrix (Fin N) (Fin N) D.host.E), (congrArg Units.val hu).symm⟩

theorem mem_ratG {D : D7} {N : ℕ} (g : GA D N) : g ∈ ratG D N ↔ ∃ γ, IsRat D (g : GL (Fin N) (AE D)) γ := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  rw [ratG_eq_ratPts] at h
  obtain ⟨u, -, hu⟩ := h
  exact ⟨(u : Matrix (Fin N) (Fin N) D.host.E), (congrArg Units.val hu).symm⟩

theorem mem_intG {D : D7} {N : ℕ} (k : GA D N) : k ∈ intG D N ↔ IntG D (k : GL (Fin N) (AE D)) := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    intro i j
    have : ((1 : Matrix (Fin N) (Fin N) (AE D)) i j) ∈ OhE D := by
      rw [Matrix.one_apply]; split_ifs
      · exact one_mem _
      · exact zero_mem _
    simpa using this
  | mul x y _ _ hx hy =>
    intro i j
    constructor
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hx i l).1 (hy l j).1
    · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact sum_mem fun l _ => mul_mem (hy i l).2 (hx l j).2
  | inv x _ hx =>
    intro i j
    refine ⟨?_, ?_⟩
    · exact (hx i j).2
    · rw [Subgroup.coe_inv, inv_inv]; exact (hx i j).1

theorem cls_eq_classSet (D : D7) (N : ℕ) (J : Subgroup (GA D N)) : Cls D N J = Formalism.UG.ClassSet (ratG D N) J := rfl

theorem gam_eq_card_stabAt (D : D7) {N : ℕ} (J : Subgroup (GA D N)) (g : GA D N) :
    gam D J g = Nat.card (Formalism.UG.stabAt (ratG D N) J g) :=
  Nat.card_congr
    { toFun := fun γ => ⟨⟨γ.1, γ.2.1⟩, γ.2.2⟩
      invFun := fun γ => ⟨γ.1.1, γ.1.2, γ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem gam_ne_zero_iff (D : D7) {N : ℕ} (J : Subgroup (GA D N)) (g : GA D N) :
    gam D J g ≠ 0 ↔ Finite (Formalism.UG.stabAt (ratG D N) J g) := by
  rw [gam_eq_card_stabAt, Nat.card_ne_zero]
  exact ⟨fun h => h.2, fun h => ⟨⟨⟨1, by simp [Formalism.UG.stabAt]⟩⟩, h⟩⟩

abbrev Tup (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) : Type :=
  ∀ τ, Fin (n τ) → {s : Fin a → Fin d // StrictMono s}

def minorPol (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : MvPolynomial (GL3Theta.Idx D a d) ℂ :=
  ∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
    (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det

def SplitIn (D : D7) (p : ℕ) : Prop := p = 2 ∨ jacobiSym (-(D.host.d : ℤ)) p = 1

def Pres (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (Q : ℕ) {a d : ℕ} (e0 F : VC D a d → ℂ) : Prop :=
  ∃ (k : ℕ) (r : Fin k → Qbar) (z : Fin k → Matrix (Fin d) (Fin a) D.host.E),
    (∀ i, Q • pt D (tor0 D cc δ) δ (z i) ∈ La0 D (tor0 D cc δ) a d) ∧
    (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (a * d) * r i)) ∧
    (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (a * d)) ∧
    F = fun y => ∑ i, (r i : ℂ) * Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 y

structure Pair (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (Q : ℕ) where

  crv : Crv D cc δ

  pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0

  a : ℕ

  d : ℕ
  a_le : a ≤ d
  d_even : Even d

  e0 : VC D a d → ℂ
  vac : oddE0 D cc δ t0 a d e0

  W : WeilO D cc δ a d e0

  n : D.what₂.Tau → ℕ
  wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)

  F : VC D a d → ℂ
  pres : Pres D cc δ Q e0 F
  fix : ∀ k ∈ intG D a, W.Om k 1 F = F

  J : Subgroup (GA D d)
  J_le : J ≤ intG D d
  idx_ne : J.relIndex (intG D d) ≠ 0
  idx_le : J.relIndex (intG D d) ≤ Q ^ (d ^ 2 + 4)
  eig : ∀ j ∈ J, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j F = c • F

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

def Pair.term (P : Pair D cc δ t0 Q) (x : GA D P.a) (h : GA D P.d) (T : Tup D P.a P.d P.n) : ℂ :=
  GL3Theta.applyAt0 D (minorPol D T) (P.W.Om x h P.F)

def Pair.coord (P : Pair D cc δ t0 Q) (h : GA D P.d) (T : Tup D P.a P.d P.n) : ℂ :=
  ∑ᶠ x : Cls D P.a (intG D P.a), ((gam D (intG D P.a) x.out : ℂ))⁻¹ * P.term x.out h T

def Pair.sq (P : Pair D cc δ t0 Q) (h : GA D P.d) : ℝ := ∑ T, ‖P.coord h T‖ ^ 2

def Pair.norm (P : Pair D cc δ t0 Q) : ℝ :=
  ∑ᶠ h : Cls D P.d P.J, ((gam D P.J h.out : ℝ))⁻¹ * P.sq h.out

def Pair.Small (P : Pair D cc δ t0 Q) (N : ℕ) (B : ℝ) : Prop := P.d ≤ 2 * N ∧ ∀ τ, (P.n τ : ℝ) ≤ 2 * B

def GoodLevel (D : D7) (Q : ℕ) : Prop := 0 < Q ∧ ∀ p : ℕ, p.Prime → p ∣ Q → SplitIn D p

def Letters (D : D7) (S : Finset ℕ) (dl : ℕ → ℝ) : Prop :=
  (∀ l ∈ S, l.Prime) ∧ (∀ l, 0 ≤ dl l) ∧ (∀ l, l ∉ S → dl l = 0) ∧ ∑ l ∈ S, dl l * Real.log l ≤ Real.log D.host.rdE ∧
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a d : ℕ) (k : GL3Theta.Idx D a d),
      ∃ (m : ℕ) (c : Fin m → Qbar) (y : Fin m → Matrix (Fin d) (Fin a) D.host.E),
        (∀ i, y i ∈ YYl D (stdL D a) (stdL D d)) ∧ (∀ i, ‖lam (c i)‖ ≤ (p : ℝ) ^ dl p) ∧
        coordV D k = ∑ i, (c i : ℂ) • (fun τ s t => embT D τ (y i s t) : VC D a d)

structure Inp (D : D7) : Prop where
  g1 : admG1 D
  perm : EmbeddingPermutesTypes D
  uni : IntertwinerUnitary D
  mu : GaussSumTripleConstant D
  curve : galCurve D
  gal : gal D
  galEx : galEx D
  t0Ex : t0Ex D
  use1 : use1 D
  alg : useAlg D
  conj : useConj D
  nrm : useNorm D
  bar : useBar D
  odd3 : odd3 D
  odd4 : odd4 D
  rep : oddRep D
  model : GL3Theta.modelEx D
  transl : GL3Theta.transl D
  two : GL3Theta.atTwo D
  jets : GL3Theta.jetsPh D
  split : GL3Theta.splitZero D

  eqv : ∀ (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (N N' : ℕ) (e0 : VC D N N' → ℂ), Crv D cc δ →
    GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (N * N') → oddE0 D cc δ t0 N N' e0 → oddEq D cc δ N N' e0

theorem Inp.of_conditions (hA : AdmD D) (hP : aux₃ D) (hM : GL3Theta.modelEx D)
    (hE : ∀ cc δ t0 N N' e0, StatementOddExactness D cc δ t0 N N' e0) : Inp D := by
  obtain ⟨⟨-, hg1, hperm, huni, hmu, hC, hPo⟩, htr, htwo, hjets, -, hsplit⟩ := hA
  obtain ⟨⟨hcurve, -, -, -, -, -, -, hgal, hgalEx, ht0, huse1, halg, hconj, hnrm, -, -, -, hbar⟩, -, h3, h4, hrep, -⟩ := hP
  exact ⟨hg1, hperm, huni, hmu, hcurve, hgal, hgalEx, ht0, huse1, halg, hconj, hnrm, hbar, h3, h4, hrep, hM, htr, htwo,
    hjets, hsplit, fun cc δ t0 N N' e0 h1 h2 he hv => hE cc δ t0 N N' e0 h1 h2 he hv hPo hg1 huni hmu hC h3 h4⟩

theorem Pair.even_mul (P : Pair D cc δ t0 Q) : Even (P.a * P.d) := P.d_even.mul_left P.a

theorem Pair.eqv (P : Pair D cc δ t0 Q) (h : Inp D) : oddEq D cc δ P.a P.d P.e0 :=
  h.eqv cc δ t0 P.a P.d P.e0 P.crv P.pt0 P.even_mul P.vac

theorem Pair.level_pos (P : Pair D cc δ t0 Q) : 0 < Q := by
  rcases Nat.eq_zero_or_pos Q with rfl | h
  · have h := P.idx_le
    rw [zero_pow (by omega)] at h
    exact absurd (Nat.le_zero.mp h) P.idx_ne
  · exact h

theorem Pair.sq_nonneg (P : Pair D cc δ t0 Q) (h : GA D P.d) : 0 ≤ P.sq h :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem Pair.norm_nonneg (P : Pair D cc δ t0 Q) : 0 ≤ P.norm :=
  finsum_nonneg fun _ => mul_nonneg (by positivity) (P.sq_nonneg _)

theorem Pair.term_mul_intG (P : Pair D cc δ t0 Q) (hF : P.F ∈ TT D (tor0 D cc δ) P.a P.d) (x : GA D P.a) {k : GA D P.a}
    (hk : k ∈ intG D P.a) (h : GA D P.d) (T : Tup D P.a P.d P.n) : P.term (x * k) h T = P.term x h T := by
  have := P.W.mul x k h 1 P.F hF
  rw [mul_one, P.fix k hk] at this
  rw [Pair.term, Pair.term, this]

theorem wd_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pres_self (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) :
    Pres D cc δ 1 e0 e0 := by
  have h0 : pt D (tor0 D cc δ) δ (0 : Matrix (Fin d) (Fin a) D.host.E) = 0 := by
    funext τ i j
    simp [pt, embV, tor0]
  refine ⟨1, fun _ => 1, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i; rw [h0]; simp
  · intro i; simpa using isIntegral_one
  · intro ρ; simp
  · funext y; simp [h0, wd_zero]

def Pair.ofVacuum (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d) (hd : Even d)
    {e0 : VC D a d → ℂ} (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0)
    (n : D.what₂.Tau → ℕ) (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ))
    (hfix : ∀ k ∈ intG D a, W.Om k 1 e0 = e0)
    (heig : ∀ j ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 j e0 = c • e0) : Pair D cc δ t0 1 where
  crv := crv
  pt0 := pt0
  a := a
  d := d
  a_le := had
  d_even := hd
  e0 := e0
  vac := vac
  W := W
  n := n
  wt := wt
  F := e0
  pres := pres_self D cc δ e0
  fix := hfix
  J := intG D d
  J_le := le_rfl
  idx_ne := by simp
  idx_le := by simp
  eig := heig

theorem Pair.ofVacuum_F_ne_zero (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {a d : ℕ} (had : a ≤ d)
    (hd : Even d) {e0 : VC D a d → ℂ} (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt) (hfix) (heig) : (Pair.ofVacuum crv pt0 had hd vac W n wt hfix heig).F ≠ 0 := W.nz

theorem exists_crv_top (D : D7) : ∃ δ : ℂ, Crv D ⊤ δ := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr (lamOf D ⊤ 1)) (n := 12) (by norm_num)
  exact ⟨δ, ⟨top_ne_bot, by simp⟩, hδ⟩

namespace RankZero

instance spaceUnique (D : D7) : Unique (VC D 0 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩

instance groupSubsingleton (D : D7) : Subsingleton (GA D 0) :=
  ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩

theorem hf0 (D : D7) (T : Tor D) (z w : VC D 0 0) : Hf D T z w = 0 := by simp [Hf]

theorem iop0 (D : D7) (T : Tor D) (A B : AddSubgroup (VC D 0 0)) (G : VC D 0 0 → ℂ) : Iop D T A B G = G := by
  funext z
  have hi : (A.addSubgroupOf B).index = 1 := by
    rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
  haveI : Subsingleton (B ⧸ A.addSubgroupOf B) := by
    refine ⟨fun x y => ?_⟩
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    congr 1
    exact Subsingleton.elim _ _
  haveI : Unique (B ⧸ A.addSubgroupOf B) := ⟨⟨((0 : B) : B ⧸ A.addSubgroupOf B)⟩, fun _ => Subsingleton.elim _ _⟩
  unfold Iop
  rw [hi, finsum_unique]
  simp only [al, U, hf0]
  simp
  congr 1
  exact Subsingleton.elim _ _

def triv (D : D7) : HeckeU D 0 where
  f := 1
  n := 0
  unitary := by simp
  cont := ⟨1, one_pos, by simp⟩
  aut := by simp
  norm := by simp
  par := by simp
  unr := by simp

def weil0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) : WeilO D cc δ 0 0 (fun _ => 1) where
  nz := fun h => by simpa using congrFun h 0
  chV := triv D
  chV' := triv D
  ep := 1
  ep' := 1
  ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩
  Om := fun _ _ F => F
  maps := fun _ _ _ h => h
  add := fun _ _ _ _ _ _ => rfl
  smul := fun _ _ _ _ _ => rfl
  one := fun _ _ => rfl
  mul := fun _ _ _ _ _ _ => rfl
  lift := fun _ _ z _ _ => ⟨1, one_pos, fun z' _ => by rw [Subsingleton.elim z z']⟩
  inert := fun _ _ _ _ _ _ => rfl
  split := by
    intros
    rw [iop0]; simp [triv]

theorem taylor0 (D : D7) (α : Mono D 0 0) (c : ℂ) : taylor D (fun _ => c) α = c := by
  have : α = 0 := by ext k; exact k.2.1.elim0
  subst this
  have h : ∀ (k : ℕ) (v : Fin k → VC D 0 0), k = 0 → iteratedFDeriv ℂ k (fun _ : VC D 0 0 => c) 0 v = c := by
    intro k v hk; subst hk; simp
  unfold taylor
  rw [h _ _ (by simp)]
  simp

theorem normSq0 (D : D7) (T : Tor D) (A : AddSubgroup (VC D 0 0)) : normSq D T A (fun _ => 1) = 1 := by
  have hex : ∃ Fd : Set (VC D 0 0), MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume := by
    refine ⟨Set.univ, MeasureTheory.IsAddFundamentalDomain.mk' (by simp) fun x => ⟨0, by simp, fun y _ => Subsingleton.elim _ _⟩⟩
  have hs := Classical.epsilon_spec hex
  unfold normSq
  simp only [hf0]
  set Fd := Classical.epsilon (fun Fd : Set (VC D 0 0) => MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume)
  have hv : (MeasureTheory.volume : MeasureTheory.Measure (VC D 0 0)) Set.univ = 1 := by
    simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
  have hF : Fd = Set.univ := by
    have hc := hs.ae_covers
    by_contra hne
    have he : Fd = ∅ := by
      rcases Set.eq_empty_or_nonempty Fd with h | ⟨x, hx⟩
      · exact h
      · exact absurd (Set.eq_univ_of_forall fun y => by rw [Subsingleton.elim y x]; exact hx) hne
    rw [he] at hc
    simp only [Set.mem_empty_iff_false, exists_false, Filter.eventually_false_iff_eq_bot,
      MeasureTheory.ae_eq_bot] at hc
    rw [hc] at hv; simp at hv
  rw [hF]
  simp [MeasureTheory.average_eq, MeasureTheory.Measure.real, hv]

theorem vac0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) : oddE0 D cc δ t0 0 0 (fun _ => 1) := by
  haveI : IsEmpty (Fin (fF D * 0 * 0)) := by simp only [mul_zero]; infer_instance
  have hon : OnB D (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E)) :=
    ⟨fun i => isEmptyElim i, Subsingleton.elim _ _⟩
  refine ⟨⟨differentiable_const _, fun x _ z => ?_⟩, fun α => ?_, ?_, ⟨fun _ => 0, 1, hon, ⟨one_mem _, fun σ => ?_⟩, ?_⟩, ?_⟩
  · simp [al, U, hf0]
  · rw [taylor0]; exact one_mem _
  · rw [La0, normSq0]; simp
  · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
    rw [this]; simp
  · rw [iop0]; funext z; simp [pullB]
  · intro p _ lam _
    refine ⟨fun _ => 0, 1, hon, ⟨linearIndependent_empty_type, fun i => isEmptyElim i,
      fun y _ => ⟨1, by simp, fun i => isEmptyElim i, Subsingleton.elim _ _⟩⟩, one_mem _, ?_, ?_, ?_⟩
    · have : (⟨1, one_mem _⟩ : Qbar) = 1 := rfl
      simp [lamC, this]
    · have hi : ((LaB D (tor0 D cc δ) (fun _ : Fin (fF D * 0 * 0) => (0 : Matrix (Fin 0) (Fin 0) D.host.E))).addSubgroupOf
          (La0 D (tor0 D cc δ) 0 0)).index = 1 := by
        rw [AddSubgroup.index_eq_one]; exact Subsingleton.elim _ _
      rw [hi]; simp
    · rw [iop0]; funext z; simp [pullB]

def pair0 (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) : Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 le_rfl (by simp) (vac0 D cc δ t0) (weil0 D cc δ) 0
    (by simp [weil0, triv]) (fun _ _ => rfl) (fun _ _ => ⟨1, by simp, by simp [weil0]⟩)

theorem gam0 (D : D7) (J : Subgroup (GA D 0)) (g : GA D 0) : gam D J g = 1 := by
  unfold gam
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨⟨1, one_mem _, by rw [Subsingleton.elim (_ * _ * _) 1]; exact one_mem _⟩⟩⟩

instance classUnique (D : D7) (J : Subgroup (GA D 0)) : Unique (Cls D 0 J) :=
  ⟨⟨Quotient.mk'' 1⟩, fun x => by
    induction x using Quotient.inductionOn'
    congr 1
    exact Subsingleton.elim _ _⟩

theorem normSumPairRankZeroOfCurve_coord_norm (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) :
    (∀ h T, (pair0 crv pt0).coord h T = 1) ∧ (pair0 crv pt0).norm = 1 := by
  have ht : ∀ x h T, (pair0 crv pt0).term x h T = 1 := by
    intro x h T
    have hm : minorPol D T = 1 := by
      unfold minorPol
      refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun j _ => j.elim0
    show GL3Theta.applyAt0 D (minorPol D T) (fun _ => 1) = 1
    rw [hm]
    have := taylor0 D 0 1
    simp [GL3Theta.applyAt0, MvPolynomial.support_one]
    exact this
  have hc : ∀ h T, (pair0 crv pt0).coord h T = 1 := by
    intro h T
    unfold Pair.coord
    simp only [ht]
    show ∑ᶠ x : Cls D 0 (intG D 0), ((gam D (intG D 0) x.out : ℂ))⁻¹ * 1 = 1
    rw [finsum_unique, gam0]; simp
  have hq : ∀ h, (pair0 crv pt0).sq h = 1 := by
    intro h
    unfold Pair.sq
    simp only [hc]
    haveI : Unique (Tup D (pair0 crv pt0).a (pair0 crv pt0).d (pair0 crv pt0).n) :=
      ⟨⟨fun τ j => j.elim0⟩, fun T => funext fun τ => funext fun j => j.elim0⟩
    simp
  refine ⟨hc, ?_⟩
  unfold Pair.norm
  simp only [hq]
  show ∑ᶠ h : Cls D 0 (intG D 0), ((gam D (intG D 0) h.out : ℝ))⁻¹ * 1 = 1
  rw [finsum_unique, gam0]; simp

end RankZero

example (h : t0Ex D) : ∃ (δ t0 : ℂ) (P : Pair D ⊤ δ t0 1), P.norm = 1 ∧ GoodLevel D 1 := by
  obtain ⟨δ, hδ⟩ := exists_crv_top D
  obtain ⟨t0, ht⟩ := (h ⊤ δ hδ).1
  exact ⟨δ, t0, RankZero.pair0 hδ ht, (RankZero.normSumPairRankZeroOfCurve_coord_norm hδ ht).2, one_pos,
    fun p hp h1 => absurd (Nat.dvd_one.mp h1) hp.one_lt.ne'⟩

example (P : Pair D ⊥ δ t0 Q) : False := P.crv.1.1 rfl

example {d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D 1 d n) :
    minorPol D T = ∏ τ, ∏ j, MvPolynomial.X (τ, (T τ j).1 0, 0) := by
  simp [minorPol]

end GlobalTheory.NormSum
