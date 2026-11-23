import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete

set_option autoImplicit false

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange

namespace GlobalTheory.WachPlace

abbrev Mx (R : Type) (a b : ℕ) : Type := Matrix (Fin a) (Fin b) R

section Series

def LatAt {n : ℕ} {O L : Type} [CommRing O] [Field L] (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O]
    (P D : Mx O⟦X⟧ n n) (Th : Mx O n n) (h : ℕ) (u : ℤ_[l]ˣ) (U : Fin n → ℤ) (em : O →+* L)
    (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∃ Q : Mx O⟦X⟧ n n, P.map (inc l O) * Q = (q l O ^ h) • (1 : Mx O⟦X⟧ n n)) ∧
  (∀ a b, (X - C (l : O)) ∣ D a b - C (Th a b)) ∧
  (∀ b ∈ Finset.Ioo 0 l, ∃ G H : (Mx L⟦X⟧ n n)ˣ,
    P.map (fun y => jj b (inc l O y)) =
      (G : Mx L⟦X⟧ n n) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U a).toNat) * (H : Mx L⟦X⟧ n n) ∧
    ((1 + (X : O⟦X⟧) • D).map (fun y => jj b (inc l O y))) *
        ((G : Mx L⟦X⟧ n n) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U a).toNat)).map
          (rescale (em (algebraMap ℤ_[l] O (u : ℤ_[l])))) =
      (G : Mx L⟦X⟧ n n) * Matrix.diagonal (fun a => (X : L⟦X⟧) ^ (U a).toNat))

theorem latN_iff {ι : Type} {n : ℕ} {O L : Type} [CommRing O] [Field L] (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (N : Lat ι n O) (h : ℕ) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ) (em : O →+* L)
    (jj : ℕ → O⟦X⟧ →+* L⟦X⟧) :
    LatN l N h u U' em jj ↔ ∀ i, LatAt l (N.P i) (N.D i) (N.Th i) h u (U' i) em jj := by
  unfold LatN LatAt
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    exact ⟨h1 i, h2 i, h3 i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2.1, fun i => (h i).2.2⟩

private lemma powerSeries_zero_subst {R : Type} [CommRing R] (p : R⟦X⟧) : (0 : R⟦X⟧).subst p = 0 := by
  rw [show (0 : R⟦X⟧) = C (0 : R) by simp, subst_C]
  simp

private lemma subst_one_lemma_2 {R : Type} [CommRing R] (p : R⟦X⟧) : (1 : R⟦X⟧).subst p = 1 := by
  rw [show (1 : R⟦X⟧) = C (1 : R) by simp, subst_C]
  simp

def IsExpAt {O L : Type} [CommRing O] [Field L] [Algebra ℚ L] (em : O →+* L) (ζ : O) (jj : O⟦X⟧ →+* L⟦X⟧) : Prop :=
  (∀ a, jj (C a) = C (em a)) ∧ jj X = C (em ζ) * PowerSeries.exp L - 1

variable {F : Type} [Field F]

def lrank {a b : ℕ} (A : Mx F⟦X⟧ a b) : ℕ := (A.map (algebraMap F⟦X⟧ (LaurentSeries F))).rank

def RedHom (l : ℕ) (un : F⟦X⟧) {a b : ℕ} (P D : Mx F⟦X⟧ b b) (P' D' : Mx F⟦X⟧ a a) (A A' : Mx F⟦X⟧ a b) : Prop :=
  P' * A'.map (frob0 l) = A * P ∧
    (1 + (X : F⟦X⟧) • D') * A.map (gam0 0 un) = A * (1 + (X : F⟦X⟧) • D)

theorem redHom_one {l : ℕ} (hl : 0 < l) (un : F⟦X⟧) {a : ℕ} (P D : Mx F⟦X⟧ a a) : RedHom l un P D P D 1 1 := by
  unfold RedHom
  have hf : (1 : Mx F⟦X⟧ a a).map (frob0 l) = 1 :=
    Matrix.map_one _ (powerSeries_zero_subst _) (subst_one_lemma_2 _)
  have hg : (1 : Mx F⟦X⟧ a a).map (gam0 0 un) = 1 :=
    Matrix.map_one _ (powerSeries_zero_subst _) (subst_one_lemma_2 _)
  rw [hf, hg, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  exact ⟨rfl, rfl⟩

end Series

section Chains

def Tw {Γ O : Type} [Group Γ] [CommRing O] {a b : ℕ} (r : Γ →* GL (Fin b) O) (r' : Γ →* GL (Fin a) O)
    (A : Mx O a b) : Prop :=
  ∀ g, A * (r g : Mx O b b) = (r' g : Mx O a a) * A

structure GalMats (Γ O : Type) [Group Γ] [CommRing O] (n t R : ℕ) where

  rk : Fin (R + 1) → Γ →* GL (Fin n) O

  a : Fin (R + 1) → Mx O n n

  bb : Fin R → Mx O n n

  r2 : Fin t → Γ →* GL (Fin (n + 1)) O

  B : Fin t → Mx O n (n + 1)

  B' : Fin t → Mx O n (n + 1)

  C : Fin t → Mx O 1 (n + 1)

  E : Fin t → Mx O (n + 1) n

def GalMats.Chain {Γ O F : Type} [Group Γ] [CommRing O] [Field F] {n t R : ℕ} (x : GalMats Γ O n t R) (red : O →+* F)
    (r : Γ →* GL (Fin n) O) (ψ : Fin t → Γ →* GL (Fin 1) O) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ) : Prop :=
  (∀ k, Tw (x.rk k) r (x.a k) ∧ (x.a k).det ≠ 0 ∧ ((x.a k).map red).rank = dim k) ∧
  (∀ k : Fin R, Tw (x.rk k.castSucc) (x.rk k.succ) (x.bb k) ∧ x.a k.castSucc = x.a k.succ * x.bb k) ∧
  ∀ s, Tw (x.r2 s) r (x.B s) ∧ Tw (x.r2 s) (x.rk (rs s).succ) (x.B' s) ∧ Tw (x.r2 s) (ψ s) (x.C s) ∧
    Tw (x.rk (rs s).castSucc) (x.r2 s) (x.E s) ∧
    x.B s * x.E s = x.a (rs s).castSucc ∧ x.C s * x.E s = 0 ∧ x.B s = x.a (rs s).succ * x.B' s ∧
    ((x.E s).map red).rank = n ∧ ((x.C s).map red).rank = 1 ∧ ((x.B' s).map red).rank = n ∧
    ∀ v, (x.B s).mulVec v = 0 → (x.C s).mulVec v = 0 → v = 0

def GalMats.res {Γ Γ' O : Type} [Group Γ] [Group Γ'] [CommRing O] {n t R : ℕ} (x : GalMats Γ O n t R) (ι : Γ' →* Γ) :
    GalMats Γ' O n t R :=
  { x with rk := fun k => (x.rk k).comp ι, r2 := fun s => (x.r2 s).comp ι }

theorem GalMats.Chain.res {Γ Γ' O F : Type} [Group Γ] [Group Γ'] [CommRing O] [Field F] {n t R : ℕ}
    {x : GalMats Γ O n t R} {red : O →+* F} {r : Γ →* GL (Fin n) O} {ψ : Fin t → Γ →* GL (Fin 1) O}
    {rs : Fin t → Fin R} {dim : Fin (R + 1) → ℕ} (h : x.Chain red r ψ rs dim) (ι : Γ' →* Γ) :
    (x.res ι).Chain red (r.comp ι) (fun s => (ψ s).comp ι) rs dim := by
  unfold GalMats.Chain Tw at *
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun k => ⟨fun g => (h1 k).1 (ι g), (h1 k).2⟩, fun k => ⟨fun g => (h2 k).1 (ι g), (h2 k).2⟩, fun s => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := h3 s
  exact ⟨fun g => e1 (ι g), fun g => e2 (ι g), fun g => e3 (ι g), fun g => e4 (ι g), e5⟩

structure Slot (F : Type) [Field F] (n t R : ℕ) where

  Pk : Fin (R + 1) → Mx F⟦X⟧ n n

  Dk : Fin (R + 1) → Mx F⟦X⟧ n n

  A : Fin (R + 1) → Mx F⟦X⟧ n n

  Bb : Fin R → Mx F⟦X⟧ n n

  P2 : Fin t → Mx F⟦X⟧ (n + 1) (n + 1)

  D2 : Fin t → Mx F⟦X⟧ (n + 1) (n + 1)

  B : Fin t → Mx F⟦X⟧ n (n + 1)

  B' : Fin t → Mx F⟦X⟧ n (n + 1)

  C : Fin t → Mx F⟦X⟧ 1 (n + 1)

  E : Fin t → Mx F⟦X⟧ (n + 1) n

def Slot.Chain {F : Type} [Field F] {n t R : ℕ} (x x' : Slot F n t R) (l : ℕ) (un : F⟦X⟧) (P D : Mx F⟦X⟧ n n)
    (Pψ Dψ : Fin t → Mx F⟦X⟧ 1 1) (rs : Fin t → Fin R) (dim : Fin (R + 1) → ℕ) : Prop :=
  (∀ k, RedHom l un (x.Pk k) (x.Dk k) P D (x.A k) (x'.A k) ∧ lrank (x.A k) = dim k) ∧
  (∀ k : Fin R, x.A k.castSucc = x.A k.succ * x.Bb k) ∧
  ∀ s, RedHom l un (x.P2 s) (x.D2 s) P D (x.B s) (x'.B s) ∧
    RedHom l un (x.P2 s) (x.D2 s) (Pψ s) (Dψ s) (x.C s) (x'.C s) ∧
    x.B s * x.E s = x.A (rs s).castSucc ∧ x.C s * x.E s = 0 ∧ x.B s = x.A (rs s).succ * x.B' s ∧
    lrank (x.E s) = n ∧ lrank (x.C s) = 1 ∧ lrank (x.B' s) = n

theorem rank_of_mul_eq_one {k : Type} [Field k] {a b : ℕ} (A : Mx k a b) (B : Mx k b a) (h : A * B = 1) :
    A.rank = a ∧ B.rank = a := by
  have h1 : (A * B).rank = a := by rw [h, Matrix.rank_one, Fintype.card_fin]
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
  · simpa using A.rank_le_card_height
  · calc a = (A * B).rank := h1.symm
      _ ≤ A.rank := Matrix.rank_mul_le_left A B
  · simpa using B.rank_le_card_width
  · calc a = (A * B).rank := h1.symm
      _ ≤ B.rank := Matrix.rank_mul_le_right A B

def charMats {Γ O : Type} [Group Γ] [CommRing O] (χ : Γ →* Oˣ) (ϖ : O) : GalMats Γ O 1 1 1 where
  rk := fun _ => GlobalTheory.TripleGal.rk1 χ
  a := ![!![ϖ], 1]
  bb := fun _ => !![ϖ]
  r2 := fun _ => (Units.map (Matrix.scalar (Fin 2) : O →+* Mx O 2 2).toMonoidHom).comp χ
  B := fun _ => !![1, ϖ]
  B' := fun _ => !![1, ϖ]
  C := fun _ => !![1, 0]
  E := fun _ => !![0; 1]

theorem charMats_chain {Γ O F : Type} [Group Γ] [CommRing O] [IsDomain O] [Field F] (χ : Γ →* Oˣ) (ϖ : O) (hϖ : ϖ ≠ 0)
    (red : O →+* F) (h0 : red ϖ = 0) :
    (charMats χ ϖ).Chain red (GlobalTheory.TripleGal.rk1 χ) (fun _ => GlobalTheory.TripleGal.rk1 χ) (fun _ => 0) ![0, 1] := by
  have key : ∀ g, ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) O) : Mx O 1 1) = !![(χ g : O)] := by
    intro g
    ext i j
    fin_cases i
    fin_cases j
    simp [GlobalTheory.TripleGal.rk1]
  have key2 : ∀ g, (((Units.map (Matrix.scalar (Fin 2) : O →+* Mx O 2 2).toMonoidHom).comp χ g : GL (Fin 2) O) :
      Mx O 2 2) = !![(χ g : O), 0; 0, (χ g : O)] := by
    intro g
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have tw11 : ∀ A : Mx O 1 1, Tw (GlobalTheory.TripleGal.rk1 χ) (GlobalTheory.TripleGal.rk1 χ) A := by
    intro A g
    rw [key]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  have hm0 : (!![ϖ] : Mx O 1 1).map red = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    simp [h0]
  unfold GalMats.Chain
  refine ⟨fun k => ?_, fun k => ⟨tw11 _, ?_⟩, fun s => ?_⟩
  · fin_cases k
    · refine ⟨tw11 _, ?_, ?_⟩
      · simpa [charMats] using hϖ
      · simp only [charMats]
        simp [hm0]
    · refine ⟨tw11 _, ?_, ?_⟩
      · simp [charMats]
      · simp [charMats]
  · fin_cases k
    simp [charMats]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g
      simp only [charMats, key, key2]
      ext i j
      fin_cases i
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · intro g
      simp only [charMats, key, key2]
      ext i j
      fin_cases i
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · intro g
      simp only [charMats, key, key2]
      ext i j
      fin_cases i
      fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · intro g
      simp only [charMats, key, key2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    · simp only [charMats]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [charMats]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [charMats]
    · refine (rank_of_mul_eq_one (!![0, 1] : Mx F 1 2) _ ?_).2
      simp only [charMats]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · refine (rank_of_mul_eq_one _ (!![1; 0] : Mx F 2 1) ?_).1
      simp only [charMats]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · refine (rank_of_mul_eq_one _ (!![1; 0] : Mx F 2 1) ?_).1
      simp only [charMats]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · intro v h1 h2
      have e1 := congrFun h1 0
      have e2 := congrFun h2 0
      simp [charMats, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e1 e2
      rw [e2, zero_add] at e1
      have e3 : v 1 = 0 := (mul_eq_zero.mp e1).resolve_left hϖ
      funext i
      fin_cases i
      · simpa using e2
      · simpa using e3

private lemma frob0_zero {R : Type} [CommRing R] (l : ℕ) : frob0 l (0 : R⟦X⟧) = 0 := powerSeries_zero_subst _

private lemma frob0_one {R : Type} [CommRing R] (l : ℕ) : frob0 l (1 : R⟦X⟧) = 1 := subst_one_lemma_2 _

private lemma gam0_zero {R : Type} [CommRing R] (lam : R) (un : R⟦X⟧) : gam0 lam un (0 : R⟦X⟧) = 0 :=
  powerSeries_zero_subst _

private lemma gam0_one {R : Type} [CommRing R] (lam : R) (un : R⟦X⟧) : gam0 lam un (1 : R⟦X⟧) = 1 :=
  subst_one_lemma_2 _

def unitPosition (F : Type) [Field F] : Slot F 1 1 1 where
  Pk := fun _ => 1
  Dk := fun _ => 0
  A := ![0, 1]
  Bb := fun _ => 0
  P2 := fun _ => 1
  D2 := fun _ => 0
  B := fun _ => !![1, 0]
  B' := fun _ => !![1, 0]
  C := fun _ => !![1, 0]
  E := fun _ => !![0; 1]

theorem unitPosition_chain (F : Type) [Field F] {l : ℕ} (hl : 0 < l) (un : F⟦X⟧) :
    (unitPosition F).Chain (unitPosition F) l un 1 0 (fun _ => 1) (fun _ => 0) (fun _ => 0) ![0, 1] := by
  have r0 : ∀ {a b : ℕ} (A : Mx F⟦X⟧ a b), (∀ i j, A i j = 0 ∨ A i j = 1) →
      RedHom l un 1 0 1 0 A A := by
    intro a b A hA
    unfold RedHom
    have e1 : A.map (frob0 l) = A := by
      ext i j
      rcases hA i j with h | h <;> simp [h, frob0_zero, frob0_one]
    have e2 : A.map (gam0 0 un) = A := by
      ext i j
      rcases hA i j with h | h <;> simp [h, gam0_zero, gam0_one]
    rw [e1, e2]
    simp
  unfold Slot.Chain
  refine ⟨fun k => ?_, fun k => ?_, fun s => ?_⟩
  · fin_cases k
    · refine ⟨r0 _ ?_, ?_⟩
      · intro i j
        simp [unitPosition]
      · unfold lrank
        simp [unitPosition]
    · refine ⟨r0 _ ?_, ?_⟩
      · intro i j
        fin_cases i
        fin_cases j
        simp [unitPosition]
      · unfold lrank
        simp [unitPosition]
  · fin_cases k
    simp [unitPosition]
  · refine ⟨r0 _ ?_, r0 _ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      fin_cases i
      fin_cases j <;> simp [unitPosition]
    · intro i j
      fin_cases i
      fin_cases j <;> simp [unitPosition]
    · simp only [unitPosition]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [unitPosition]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · simp [unitPosition]
    · unfold lrank
      refine (rank_of_mul_eq_one (!![0, 1] : Mx (LaurentSeries F) 1 2) _ ?_).2
      simp only [unitPosition]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · unfold lrank
      refine (rank_of_mul_eq_one _ (!![1; 0] : Mx (LaurentSeries F) 2 1) ?_).1
      simp only [unitPosition]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · unfold lrank
      refine (rank_of_mul_eq_one _ (!![1; 0] : Mx (LaurentSeries F) 2 1) ?_).1
      simp only [unitPosition]
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply, Fin.sum_univ_two]

end Chains

section Local

variable {l : ℕ} [Fact l.Prime]

def toOm (LL : FinExt l) : ↥(OL LL) →+* PadicAlgCl l := (LL.1.val.toRingHom).comp ((OL LL).val.toRingHom)

variable {K LL : FinExt l} {n n' : ℕ}

def repOf {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) ↥(OL LL)) : Representation ↥LL.1 Γ (Fin n → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp
    ((Units.coeHom _).comp ((Matrix.GeneralLinearGroup.map (algebraMap ↥(OL LL) ↥LL.1)).comp r))

theorem repOf_apply {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) ↥(OL LL)) (g : Γ) (v : Fin n → ↥LL.1) :
    repOf r g v = ((r g : Mx ↥(OL LL) n n).map (algebraMap ↥(OL LL) ↥LL.1)).mulVec v := rfl

def Cont (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) : Prop :=
  ∀ a b, Continuous fun g => (((r g : Mx ↥(OL LL) n n) a b : ↥(OL LL)) : ↥LL.1)

def stdMap (LL : FinExt l) (n : ℕ) : (Fin n → ↥(OL LL)) →ₗ[↥(OL LL)] (Fin n → ↥LL.1) :=
  (Algebra.linearMap ↥(OL LL) ↥LL.1).compLeft (Fin n)

theorem stdMap_apply (x : Fin n → ↥(OL LL)) (j : Fin n) : stdMap LL n x j = (x j : ↥LL.1) := rfl

theorem stdMap_injective : Function.Injective (stdMap LL n) := by
  intro x y hxy
  funext j
  have hj := congrFun hxy j
  rw [stdMap_apply, stdMap_apply] at hj
  exact Subtype.ext hj

theorem stdMap_mulVec (A : Mx ↥(OL LL) n' n) (x : Fin n → ↥(OL LL)) :
    (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (stdMap LL n x) = stdMap LL n' (A.mulVec x) := by
  funext j
  rw [stdMap_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, stdMap_apply]
  push_cast
  rfl

set_option synthInstance.maxHeartbeats 400000 in

def latOf (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (hr : Cont r) : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := Fin n → ↥LL.1
  ρ := repOf r
  cont := fun x => by
    refine continuous_pi fun j => ?_
    change Continuous fun g => ∑ b, (((r g : Mx ↥(OL LL) n n) j b : ↥(OL LL)) : ↥LL.1) * x b
    exact continuous_finset_sum _ fun b _ => (hr j b).mul continuous_const
  L :=
    { T := LinearMap.range (stdMap LL n)
      stable := by
        rintro g _ ⟨x, rfl⟩
        exact ⟨_, (stdMap_mulVec _ x).symm⟩
      fg := by
        rw [LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ stdMap_injective)
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL.1 (Fin n)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        by_cases h : j' = j <;> simp [stdMap_apply, Pi.single_apply, h] }

set_option synthInstance.maxHeartbeats 400000 in

def basisOf (r : ↥(GK K) →* GL (Fin n) ↥(OL LL)) (hr : Cont r) :
    Module.Basis (Fin n) ↥(OL LL) ↥(latOf r hr).L.T :=
  (Pi.basisFun ↥(OL LL) (Fin n)).map (LinearEquiv.ofInjective _ stdMap_injective)

set_option synthInstance.maxHeartbeats 400000 in

def homOf {r : ↥(GK K) →* GL (Fin n) ↥(OL LL)} (hr : Cont r) {r' : ↥(GK K) →* GL (Fin n') ↥(OL LL)} (hr' : Cont r')
    (A : Mx ↥(OL LL) n' n) (hA : Tw r r' A) : LatHom (latOf r hr).L (latOf r' hr').L where
  f := Matrix.toLin' (A.map (algebraMap ↥(OL LL) ↥LL.1))
  equiv := fun g x => by
    have key : ∀ y : Fin n → ↥LL.1, (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec (repOf r g y) =
        repOf r' g ((A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec y) := fun y => by
      rw [repOf_apply, repOf_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
        hA g]
    exact key x
  cont := by
    change Continuous fun x : Fin n → ↥LL.1 => (A.map (algebraMap ↥(OL LL) ↥LL.1)).mulVec x
    exact continuous_const.matrix_mulVec continuous_id
  T_le := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (stdMap_mulVec A x).symm⟩

def MatGood (P : LocPrime l) {f : ℕ} (emb : ZMod f → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (r : ↥(GK K) →* GL (Fin n) ↥(OL LL))
    (U : ZMod f → Multiset ℤ) : Prop :=
  Cont r ∧ GlobalTheory.AdmLoc.CrysWith (P.PD K) emb (repOf r) U

variable {P : LocPrime l} {f : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) f)

def IsFrame (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (γ : W.Gam)
    (b : Module.Basis (Fin n) (LetA ↥(OL LL) f) ↥(W.N T)) (N : Lat (ZMod f) n ↥(OL LL)) : Prop :=
  (∀ k, (b k : W.DD T) ∈ W.NΔ T) ∧
  (∀ k, W.φD T (b k : W.DD T) =
    ∑ m, (fun i => inc l ↥(OL LL) (N.P i m k) : LetA ↥(OL LL) f) • (b m : W.DD T)) ∧
  (∀ k, W.γD T γ (b k : W.DD T) =
    ∑ m, (fun i => inc l ↥(OL LL) ((1 + (X : (↥(OL LL))⟦X⟧) • N.D i) m k) : LetA ↥(OL LL) f) • (b m : W.DD T)) ∧
  ∀ i a c, (X - C (l : ↥(OL LL))) ∣ N.D i a c - C (N.Th i a c)

def IsMapMat {T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (g : LatHom T.L T'.L)
    (b : Module.Basis (Fin n) (LetA ↥(OL LL) f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) f) ↥(W.N T'))
    (A : ZMod f → Mx (↥(OL LL))⟦X⟧ n' n) : Prop :=
  ∀ k, W.map g (b k : W.DD T) =
    ∑ m, (fun i => inc l ↥(OL LL) (A i m k) : LetA ↥(OL LL) f) • (b' m : W.DD T')

def RingFacts : Prop :=
  (∀ a, W.φ₀ a = phi l ↥(OL LL) a) ∧ W.q₀ = q l ↥(OL LL) ∧
  (∀ (g : W.Gam) (z : ℤ_[l]), (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) z →
    ∀ a, W.γ₀ g a = act l ↥(OL LL) z a) ∧
  (∀ z : ℤ_[l]ˣ, ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l])) ∧
  (∀ a : (↥(OL LL))⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ↔ ∃ y, inc l ↥(OL LL) y = a) ∧
  IsUnit (W.DelF.card : ↥(OL LL))

end Local

end GlobalTheory.WachPlace

end
