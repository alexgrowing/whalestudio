import Mathlib

open scoped BigOperators

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

abbrev Letter {ι : Type} (dim : ι → ℕ) (n : ℕ) : Type := Fin n × (Σ s : ι, Fin (dim s))

structure Block {ι : Type} (dim : ι → ℕ) (n : ℕ) where
  emb : ι
  size : ℕ
  expo : ℕ
  one_le_size : 1 ≤ size
  size_le : size ≤ dim emb
  one_le_expo : 1 ≤ expo
  col : Fin size ↪ Fin n
  vec : Fin size → EuclideanSpace ℂ (Fin (dim emb))
  orthonormal_vec : Orthonormal ℂ vec

variable {ι : Type} {dim : ι → ℕ} {n : ℕ}

def Block.entry (B : Block dim n) (a b : Fin B.size) : MvPolynomial (Letter dim n) ℂ :=
  ∑ k : Fin (dim B.emb),
    MvPolynomial.C (B.vec a k) * MvPolynomial.X (B.col b, ⟨B.emb, k⟩)

def Block.poly (B : Block dim n) : MvPolynomial (Letter dim n) ℂ :=
  (Matrix.of fun a b => B.entry a b).det ^ B.expo

structure BlockSystem {ι : Type} (dim : ι → ℕ) (n : ℕ) where
  card : ℕ
  block : Fin card → Block dim n
  disjoint : Pairwise fun j j' =>
    Disjoint (Set.range (block j).col) (Set.range (block j').col)

def BlockSystem.poly (S : BlockSystem dim n) : MvPolynomial (Letter dim n) ℂ :=
  ∏ j, (S.block j).poly

def BlockSystem.degree (S : BlockSystem dim n) : ℕ :=
  ∑ j, (S.block j).size * (S.block j).expo

def IsBlockPolynomial (P : MvPolynomial (Letter dim n) ℂ) (D : ℕ) : Prop :=
  ∃ S : BlockSystem dim n, S.poly = P ∧ S.degree = D

theorem Block.isHomogeneous_entry (B : Block dim n) (a b : Fin B.size) :
    (B.entry a b).IsHomogeneous 1 := by
  unfold Block.entry
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C _ (B.vec a k)).mul
    (MvPolynomial.isHomogeneous_X ℂ ((B.col b, ⟨B.emb, k⟩) : Letter dim n))

theorem Block.isHomogeneous_poly (B : Block dim n) :
    B.poly.IsHomogeneous (B.size * B.expo) := by
  unfold Block.poly
  refine MvPolynomial.IsHomogeneous.pow ?_ _
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i, (Matrix.of fun a b => B.entry a b) (σ i) i).IsHomogeneous
      (∑ _i : Fin B.size, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => B.isHomogeneous_entry _ _
  have h2 : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Letter dim n) ℂ)).IsHomogeneous 0 := by
    have := MvPolynomial.isHomogeneous_C (Letter dim n) (((Equiv.Perm.sign σ : ℤ) : ℂ))
    simpa using this
  simpa using h2.mul h1

theorem BlockSystem.isHomogeneous_poly (S : BlockSystem dim n) :
    S.poly.IsHomogeneous S.degree :=
  MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => (S.block j).isHomogeneous_poly

def exampleBlock : Block (fun _ : Fin 2 => 2) 3 where
  emb := 0
  size := 2
  expo := 3
  one_le_size := by norm_num
  size_le := le_rfl
  one_le_expo := by norm_num
  col := Fin.castLEEmb (by norm_num)
  vec := EuclideanSpace.basisFun (Fin 2) ℂ
  orthonormal_vec := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal

def exampleSystem : BlockSystem (fun _ : Fin 2 => 2) 3 where
  card := 1
  block := fun _ => exampleBlock
  disjoint := Subsingleton.pairwise

example : exampleSystem.degree = 6 := by
  decide

section Operator

variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

def wordDeriv (dir : Λ → W) (l : List Λ) (F : W → ℂ) (p : W) : ℂ :=
  iteratedFDeriv ℂ l.length F p fun j => dir (l.get j)

def applyAt (dir : Λ → W) (P : MvPolynomial Λ ℂ) (F : W → ℂ) (p : W) : ℂ :=
  ∑ μ ∈ P.support, P.coeff μ * wordDeriv dir (Finsupp.toMultiset μ).toList F p

theorem iteratedFDeriv_directions_comp_perm_of_analyticAt (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {k : ℕ} (u v : Fin k → Λ) (σ : Equiv.Perm (Fin k)) (h : u = v ∘ σ) :
    iteratedFDeriv ℂ k F p (fun j => dir (u j)) = iteratedFDeriv ℂ k F p (fun j => dir (v j)) := by
  subst h
  exact (hF.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (fun j => dir (v j)) σ

theorem wordDeriv_perm (dir : Λ → W) {F : W → ℂ} {p : W} (hF : AnalyticAt ℂ F p)
    {l l' : List Λ} (h : l.Perm l') : wordDeriv dir l F p = wordDeriv dir l' F p := by
  have key : ∀ {l l' : List Λ}, l.Perm l' →
      ∃ e : Fin l.length ≃ Fin l'.length, ∀ j, l.get j = l'.get (e j) := by
    intro l l' h
    induction h with
    | nil => exact ⟨Equiv.refl _, fun _ => rfl⟩
    | cons x _ ih =>
      obtain ⟨e, he⟩ := ih
      refine ⟨(finSuccEquiv _).trans ((Equiv.optionCongr e).trans (finSuccEquiv _).symm), ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simpa using he j
    | swap x y l =>
      refine ⟨Equiv.swap (0 : Fin (l.length + 2)) 1, ?_⟩
      intro j
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
      · simp
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _)]
        simp
    | trans _ _ ih₁ ih₂ =>
      obtain ⟨e₁, h₁⟩ := ih₁
      obtain ⟨e₂, h₂⟩ := ih₂
      exact ⟨e₁.trans e₂, fun j => by rw [h₁, h₂]; rfl⟩
  obtain ⟨e, he⟩ := key h
  have hl := h.length_eq
  unfold wordDeriv
  have gen : ∀ (a b : ℕ) (_ : a = b) (u : Fin a → Λ) (v : Fin b → Λ) (e : Fin a ≃ Fin b),
      (∀ j, u j = v (e j)) → iteratedFDeriv ℂ a F p (fun j => dir (u j)) =
        iteratedFDeriv ℂ b F p (fun j => dir (v j)) := by
    intro a b hab u v e he
    subst hab
    exact iteratedFDeriv_directions_comp_perm_of_analyticAt dir hF u v e (funext he)
  exact gen _ _ hl _ _ e he

example (dir : Λ → W) (F : W → ℂ) (p : W) : applyAt dir 1 F p = F p := by
  classical
  have h : (Finsupp.toMultiset (0 : Λ →₀ ℕ)).toList = [] := by simp
  simp only [applyAt, MvPolynomial.support_one, Finset.sum_singleton, h]
  simp [wordDeriv]

end Operator

section Columns

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def letterDir (e : (s : ι) → Fin (dim s) → V) (x : Letter dim n) : Fin n → V :=
  Pi.single x.1 (e x.2.1 x.2.2)

def opAt (e : (s : ι) → Fin (dim s) → V) (P : MvPolynomial (Letter dim n) ℂ)
    (F : (Fin n → V) → ℂ) (p : Fin n → V) : ℂ :=
  applyAt (letterDir e) P F p

end Columns

def gDim (f r : ℕ) : ℕ := f * r

def bigR (rd : ℝ) : ℝ := rd ^ 7

def dStar (f m : ℕ) : ℕ := 2 * f * m

def omStar (f : ℕ) (rd : ℝ) : ℝ := 2 * (f : ℝ) ^ ((3 : ℝ) / 2) * rd

def thSq (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := f * R₀ ^ 2 * bigR rd ^ 3 / q

def th (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := Real.sqrt (thSq f rd q R₀)

def bZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q / (R₀ ^ 2 * bigR rd ^ 4)

def tZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q * bZero rd q R₀

def mOne (f m : ℕ) (rd : ℝ) : ℝ := 90 * (m : ℝ) ^ 2 * (dStar f m : ℝ) ^ 2 * rd

def cChi (f m : ℕ) (rd : ℝ) : ℝ := 8100 * (m : ℝ) ^ 4 * (dStar f m : ℝ) ^ 4 * bigR rd

def ph (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) (la : Set.Ioi (0 : ℝ)) : ℝ :=
  if (la : ℝ) < th f rd q R₀ then 2 * f / (rd ^ 2 * (la : ℝ) ^ 2) else 0

theorem ph_nonneg (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) (la : Set.Ioi (0 : ℝ)) :
    0 ≤ ph f rd q R₀ la := by
  unfold ph
  split_ifs
  · positivity
  · exact le_rfl

structure Params {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ) where
  q : ℕ
  R₀ : ℝ
  m : ℕ
  one_le_m : 1 ≤ m
  min_dim_le : ∃ s, dim s ≤ m
  m_pow_le : m ^ 4 ≤ f
  f_sq_le : (f : ℝ) ^ 2 ≤ rd
  sixteen_le : 16 ≤ rd
  two_le_fr : 2 ≤ f * r
  three_le_q : 3 ≤ q
  one_le_D : 1 ≤ D
  one_le_n : 1 ≤ n
  R₀_pos : 0 < R₀
  R₀_sq : max (270 : ℝ) (90 * ((gDim f r : ℝ) + D)) ≤ R₀ ^ 2
  threshold_lt : (dStar f m : ℝ) ^ 2 * omStar f rd * thSq f rd q R₀ < 1
  one_le_bZero : 1 ≤ bZero rd q R₀
  mOne_le : mOne f m rd ≤ (q : ℝ) / 2
  D_le_q : D ≤ q
  tZero_ge_log : 4 * (D : ℝ) * (7 + Real.log ((q : ℝ) * D)) + (dStar f m : ℝ) + 1 ≤ tZero rd q R₀
  tZero_ge_rank : (gDim f r : ℝ) * Real.log 2 + 2 * (dStar f m : ℝ) + 3 +
    ((D : ℝ) + 1) * ((r : ℝ) * Real.log r + 3 * r + 3) ≤ tZero rd q R₀

structure ParamsWithLevel {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ)
    extends Params dim f r rd D n where
  r₁ : ℕ
  two_le_r₁ : 2 ≤ r₁

def exampleParams : ParamsWithLevel (fun _ : Fin 2 => 1) 1 2 16 1 1 where
  q := 2 ^ 130
  R₀ := 17
  m := 1
  r₁ := 2
  two_le_r₁ := le_rfl
  one_le_m := le_rfl
  min_dim_le := ⟨0, le_rfl⟩
  m_pow_le := by norm_num
  f_sq_le := by norm_num
  sixteen_le := le_rfl
  two_le_fr := by norm_num
  three_le_q := by norm_num
  one_le_D := le_rfl
  one_le_n := le_rfl
  R₀_pos := by norm_num
  R₀_sq := by norm_num [gDim]
  threshold_lt := by norm_num [dStar, omStar, thSq, bigR]
  one_le_bZero := by norm_num [bZero, bigR]
  mOne_le := by norm_num [mOne, dStar]
  D_le_q := by norm_num
  tZero_ge_log := by
    have h : Real.log (((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) ≤ ((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) :=
      Real.log_le_self (by positivity)
    have h2 : 4 * ((1 : ℕ) : ℝ) * (7 + ((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) + (dStar 1 1 : ℝ) + 1
        ≤ tZero 16 (2 ^ 130) 17 := by
      norm_num [dStar, tZero, bZero, bigR]
    refine le_trans ?_ h2
    gcongr
  tZero_ge_rank := by
    have h : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
    have h2 : (100 : ℝ) ≤ tZero 16 (2 ^ 130) 17 := by
      norm_num [tZero, bZero, bigR]
    refine le_trans ?_ h2
    simp only [gDim, dStar]
    push_cast
    linarith

def kaZero (f m : ℕ) (rd : ℝ) : ℝ := 4 * bigR rd * (dStar f m : ℝ) ^ 2

def pOne (f r q : ℕ) : ℝ :=
  1 + (gDim f r : ℝ) * Real.log (1 + 6 * Real.sqrt ((gDim f r : ℝ) * q))

def pTwo (f m : ℕ) : ℝ := Real.log (2 * (3 * (dStar f m : ℝ)) ^ dStar f m)

def pThree (f r q m : ℕ) : ℝ := r * (pOne f r q + pTwo f m + (dStar f m : ℝ))

def pFour (f r r₁ : ℕ) (Nc : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log Nc + 2 * f * (r : ℝ) ^ 2 * Real.log r₁

def bigA (f r m r₁ : ℕ) : ℝ := (r₁ : ℝ) ^ 4 * r * (dStar f m : ℝ) / 2

def bigA' (f r m : ℕ) : ℝ := max 1 (r * (dStar f m : ℝ) / 4)

def pSixteen (f r : ℕ) (rd : ℝ) (q m r₁ : ℕ) (Nc : Set.Ici (1 : ℝ)) : ℝ :=
  2 * (r₁ : ℝ) ^ 4 * (pThree f r q m + pFour f r r₁ Nc) +
    bigA f r m r₁ * Real.log (bigA f r m r₁ * kaZero f m rd)

def pFourteen (f r n q m : ℕ) : ℝ :=
  1 / 2 * ((f : ℝ) * r * n * Real.log q +
    n * (Real.log 24 + (f : ℝ) * m * Real.log (4 * f * m)) + ((r : ℝ) + 2) * Real.log 2)

def pThirteenMin (f n m : ℕ) : ℝ := 16200 * Real.pi * n * (m : ℝ) ^ 4 * (dStar f m : ℝ) ^ 4

def cCoeff (rd PP : ℝ) (D q : ℕ) : ℝ := bigR rd * PP * (D : ℝ) ^ 2 / q

theorem exp_pTwo (f m : ℕ) : Real.exp (pTwo f m) = 2 * (3 * (dStar f m : ℝ)) ^ dStar f m := by
  unfold pTwo
  refine Real.exp_log ?_
  rcases Nat.eq_zero_or_pos (dStar f m) with h | h
  · simp [h]
  · have : (0 : ℝ) < dStar f m := by exact_mod_cast h
    positivity

def jetBound (f r : ℕ) (rd : ℝ) (D n q : ℕ) (R₀ : ℝ) (m : ℕ) (la : Set.Ioi (0 : ℝ)) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ * ((6 * (2 * (dStar f m : ℝ)) ^ ((dStar f m : ℝ) / 2)) ^ n)⁻¹ *
    ((2 : ℝ) ^ ((r + 2) * D))⁻¹ *
    Real.exp (-(2 * Real.pi * n * cChi f m rd * ph f rd q R₀ la / q))

namespace Params

variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)

def ph (la : Set.Ioi (0 : ℝ)) : ℝ := WordBlockPolynomials.ph f rd P.q P.R₀ la

def jetBound (la : Set.Ioi (0 : ℝ)) : ℝ := WordBlockPolynomials.jetBound f r rd D n P.q P.R₀ P.m la

def kaZero : ℝ := WordBlockPolynomials.kaZero f P.m rd

def pOne : ℝ := WordBlockPolynomials.pOne f r P.q

def pTwo : ℝ := WordBlockPolynomials.pTwo f P.m

def pThree : ℝ := WordBlockPolynomials.pThree f r P.q P.m

theorem jetBound_pos (la : Set.Ioi (0 : ℝ)) : 0 < P.jetBound la := by
  have hf : 1 ≤ f := le_trans (Nat.one_le_pow _ _ P.one_le_m) P.m_pow_le
  have hd : (0 : ℝ) < dStar f P.m := by
    have := P.one_le_m
    exact_mod_cast (show 0 < 2 * f * P.m by positivity)
  unfold Params.jetBound WordBlockPolynomials.jetBound
  positivity

end Params

end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
