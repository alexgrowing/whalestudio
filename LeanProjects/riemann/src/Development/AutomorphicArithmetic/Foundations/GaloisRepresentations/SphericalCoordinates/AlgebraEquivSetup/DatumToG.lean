import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact

noncomputable section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E := (IsCMField.complexConj E : E →+* E)

structure Arith (E : Type) [Field E] [NumberField E] [IsCMField E] where
  bar : 𝓞 E ≃+* 𝓞 E
  bar_eq : ∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)
  ω : 𝓞 E
  tr : ℤ
  nm : ℤ
  tr_eq : ω + bar ω = (tr : 𝓞 E)
  nm_eq : ω * bar ω = (nm : 𝓞 E)
  disc_neg : tr ^ 2 - 4 * nm < 0
  τ₀ : E →+* ℂ
  c : 𝓞 E
  c_real : bar c = c
  c_neg : (τ₀ (c : E)).re < 0
  c_pos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ (c : E)).re
  δ : E
  δ_im : IsCMField.complexConj E δ = -δ
  δ_int : ∀ x : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (δ * x) = m
  δ_sign : ∀ τ : E →+* ℂ, τ (ω : E) = τ₀ (ω : E) → (τ δ).im < 0

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Arith

variable (A : Arith E)

def trd : 𝓞 E →ₗ[ℤ] ℤ :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x => (A.δ_int x).choose
      map_zero' := by
        have h := (A.δ_int 0).choose_spec
        have h0 : Algebra.trace ℚ E (A.δ * ((0 : 𝓞 E) : E)) = 0 := by simp
        have h1 : (((A.δ_int 0).choose : ℤ) : ℚ) = 0 := h.symm.trans h0
        exact_mod_cast h1
      map_add' := fun x y => by
        have h := (A.δ_int (x + y)).choose_spec
        have h1 := (A.δ_int x).choose_spec
        have h2 := (A.δ_int y).choose_spec
        have : (((A.δ_int (x + y)).choose : ℤ) : ℚ) = ((A.δ_int x).choose : ℤ) + ((A.δ_int y).choose : ℤ) := by
          rw [← h, ← h1, ← h2, ← map_add, ← mul_add]; simp
        exact_mod_cast this }

theorem trd_spec (x : 𝓞 E) : ((A.trd x : ℤ) : ℚ) = Algebra.trace ℚ E (A.δ * x) := (A.δ_int x).choose_spec.symm

def dg (n : ℕ) (i : Fin n) : 𝓞 E := if (i : ℕ) = 0 then 1 else A.c

def hd (n : ℕ) (i : Fin n) : 𝓞 E := -A.c * A.dg n i

def H (n : ℕ) : Matrix (Fin n) (Fin n) E := Matrix.diagonal fun i => ((A.hd n i : 𝓞 E) : E)

def EF (n : ℕ) : LinearMap.BilinForm ℤ (Fin n → 𝓞 E) :=
  LinearMap.mk₂ ℤ (fun x y => A.trd (∑ i, A.hd n i * x i * A.bar (y i)))
    (fun x x' y => by simp [mul_add, add_mul, Finset.sum_add_distrib])
    (fun m x y => by rw [← map_smul, Finset.smul_sum]; simp [mul_assoc, mul_left_comm])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun m x y => by rw [← map_smul, Finset.smul_sum]; simp [mul_assoc, mul_left_comm])

theorem EF_apply (n : ℕ) (x y : Fin n → 𝓞 E) : A.EF n x y = A.trd (∑ i, A.hd n i * x i * A.bar (y i)) := rfl

def SplitK (q : ℕ) : Prop := ¬ (q : ℤ) ∣ A.tr ^ 2 - 4 * A.nm ∧ ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm

def PerfAt (q : ℕ) : Prop :=
  ∃ e : ℕ, e.Coprime q ∧ (∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ y, A.trd (x * y) = e * f y) ∧ ∃ c' : 𝓞 E, A.c * c' = (e : 𝓞 E)

def Good (q : ℕ) : Prop := A.SplitK q ∧ A.PerfAt q

def FormOK (n : ℕ) : Prop :=
  (∀ x, A.EF n x x = 0) ∧ Function.Injective (A.EF n) ∧ ∀ (b : 𝓞 E) x y, A.EF n (b • x) y = A.EF n x (A.bar b • y)

def FormPerf (n q : ℕ) : Prop := ∃ e : ℕ, e.Coprime q ∧ ∀ f : (Fin n → 𝓞 E) →ₗ[ℤ] ℤ, ∃ x, A.EF n x = e • f

def tau : Fin 1 ↪ (E →+* ℂ) := ⟨fun _ => A.τ₀, fun _ _ _ => Subsingleton.elim _ _⟩

def Dom (n : ℕ) : Prop :=
  ∃ J : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E), (∀ x, J (J x) = -x) ∧
    (∀ x y, (A.EF n).baseChange ℝ (J x) (J y) = (A.EF n).baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < (A.EF n).baseChange ℝ (J x) x) ∧
    (∀ (b : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E)),
      (∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (b • x)) → J ∘ₗ M = M ∘ₗ J) ∧
    ∀ (c : 𝓞 E) (M : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] ℝ ⊗[ℤ] (Fin n → 𝓞 E)),
      (∀ x : Fin n → 𝓞 E, M (1 ⊗ₜ x) = 1 ⊗ₜ (c • x)) →
      let S : ℂ := A.τ₀ (c : E) +
        ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (A.ω : E) = (starRingEnd ℂ) (A.τ₀ (A.ω : E))), (n : ℂ) * τ (c : E) -
        (starRingEnd ℂ) (A.τ₀ (c : E))
      LinearMap.trace ℝ _ M = 2 * S.re ∧ LinearMap.trace ℝ _ (J ∘ₗ M) = -2 * S.im

structure Facts (n : ℕ) : Prop where
  pos : 1 ≤ n
  form : A.FormOK n
  dom : A.Dom n

theorem bar_bar (x : 𝓞 E) : A.bar (A.bar x) = x := by
  ext
  rw [A.bar_eq, A.bar_eq, IsCMField.complexConj_apply_apply]

theorem splitOne (q : ℕ) [Fact q.Prime] :
    Nonempty ((𝓞 E ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 E] Matrix (Fin 1) (Fin 1) (𝓞 E ⊗[ℤ] ℤ_[q])) := by
  refine ⟨
    { toFun := fun x => Matrix.of fun _ _ => x
      invFun := fun M => M 0 0
      left_inv := fun x => rfl
      right_inv := fun M => by
        ext i j
        fin_cases i; fin_cases j; rfl
      map_mul' := fun x y => by
        ext i j
        simp [Matrix.mul_apply]
      map_add' := fun x y => by
        ext i j
        rfl
      commutes' := fun r => by
        ext i j
        fin_cases i; fin_cases j
        simp [Matrix.algebraMap_matrix_apply] }⟩

theorem root : (A.τ₀ (A.ω : E)) ^ 2 - A.tr * A.τ₀ (A.ω : E) + A.nm = 0 := by
  have h : A.ω ^ 2 - (A.tr : 𝓞 E) * A.ω + (A.nm : 𝓞 E) = 0 := by
    rw [← A.tr_eq, ← A.nm_eq]; ring
  have h2 := congrArg (fun y : 𝓞 E => A.τ₀ (y : E)) h
  simpa using h2

def datum {n : ℕ} (h : A.Facts n) (q : ℕ) [Fact q.Prime] (hs : A.SplitK q) (hp : A.FormPerf n q) : Datum q where
  F := E
  bar := A.bar
  bar_eq := A.bar_eq
  ω := A.ω
  tr := A.tr
  nm := A.nm
  tr_eq := A.tr_eq
  nm_eq := A.nm_eq
  disc_neg := A.disc_neg
  disc_p := hs.1
  split := hs.2
  O := 𝓞 E
  freeO := inferInstance
  finO := inferInstance
  m := 1
  m_pos := one_pos
  rankO := by rw [RingOfIntegers.rank]; simp
  central x _ := ⟨x, 1, one_ne_zero, by simp⟩
  star := A.bar.trans (RingEquiv.toOpposite (𝓞 E))
  star_star x := A.bar_bar x
  star_F _ := rfl
  splitP := splitOne q
  La := Fin n → 𝓞 E
  freeLa := inferInstance
  finLa := inferInstance
  n := n
  n_pos := h.pos
  rankLa := by rw [Module.finrank_pi_fintype]; simp [RingOfIntegers.rank]
  EF := A.EF n
  alt := h.form.1
  nondeg := h.form.2.1
  perfP := hp
  adj := h.form.2.2
  a := 1
  ρc := A.τ₀ (A.ω : E)
  ρc_root := A.root
  tau := A.tau
  tau_ω _ := rfl
  dom := by
    obtain ⟨J, h1, h2, h3, h4, h5⟩ := h.dom
    refine ⟨J, h1, h2, h3, h4, fun c M hM => ?_⟩
    have := h5 c M hM
    have ht : A.tau 0 = A.τ₀ := rfl
    simpa [ht] using this

theorem datum_toG {n : ℕ} (h : A.Facts n) (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hs hp hs' hp') :
    (A.datum h q hs hp).toG = (A.datum h q' hs' hp').toG := rfl

theorem herm (n : ℕ) : ((A.H n).map (cj E))ᵀ = A.H n := by
  rw [H, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  funext i
  show IsCMField.complexConj E _ = _
  rw [← A.bar_eq]
  congr 1
  simp only [hd, dg, map_mul, map_neg, A.c_real]
  split_ifs <;> simp [A.c_real]

theorem c_ne : (A.c : E) ≠ 0 := by
  intro h
  have hn := A.c_neg
  have h0 : A.c = 0 := RingOfIntegers.ext (by simpa using h)
  rw [h0] at hn
  simp at hn

theorem det_ne (n : ℕ) : (A.H n).det ≠ 0 := by
  unfold H
  rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro i _
  have := A.c_ne
  unfold hd dg; split_ifs <;> simp [this]

def SigOK (n : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, (InfinitePlace.mk τ = InfinitePlace.mk A.τ₀ → sigPos (A.herm n) τ = 1 ∧ sigNeg (A.herm n) τ = n - 1) ∧
    (InfinitePlace.mk τ ≠ InfinitePlace.mk A.τ₀ → sigPos (A.herm n) τ = 0 ∧ sigNeg (A.herm n) τ = n)

structure AtP (p : ℕ) [Fact p.Prime] where
  Kq : Subfield E
  hKq : Module.finrank ℚ Kq = 2 ∧ ∀ τ : E →+* ℂ, ∃ x ∈ Kq, (τ x).im ≠ 0
  u : Kq →+* ℚ_[p]
  m : ℕ
  emb : Fin m → (E →+* PadicAlgCl p)
  emb_over : ∀ i, LiesOver Kq u (emb i)
  emb_inj : ∀ i j (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
    ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i) = emb j → i = j
  emb_all : ∀ τ : E →+* PadicAlgCl p, LiesOver Kq u τ →
    ∃ i, ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      τ = ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp (emb i)
  iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p
  iotaC : AlgebraicClosure ℚ →+* ℂ
  ρp : ℤ_[p]
  ρp_eq : ∃ h : (A.ω : E) ∈ Kq, u ⟨A.ω, h⟩ = (ρp : ℚ_[p])
  s : E →+* AlgebraicClosure ℚ
  s_C : ∀ x, iotaC (s x) = A.τ₀ x
  w : Fin m
  s_P : ∀ x, iotaP (s x) = emb w x

def grp {n : ℕ} (hn : 1 ≤ n) (hs : A.SigOK n) {p : ℕ} [Fact p.Prime] (P : A.AtP p) : HTGroup p :=
  ofHerm E P.Kq P.hKq P.u n hn (A.H n) (A.herm n) (A.det_ne n)
    (fun τ => (em _).imp (hs τ).1 (hs τ).2) P.m P.emb P.emb_over P.emb_inj P.emb_all P.iotaP P.iotaC

end Arith

structure Setup (A : Arith E) (n p : ℕ) [Fact p.Prime] where
  facts : A.Facts n
  sig : A.SigOK n
  good : A.Good p
  perf : A.FormPerf n p
  P : A.AtP p
  L : Link (A.datum facts p good.1 perf) (A.grp facts.pos sig P)
  L_e : ∀ x : E, L.e x = x
  L_rep : ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
    L.rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v)

namespace Setup

variable {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p)

abbrev D : Datum p := A.datum S.facts p S.good.1 S.perf

abbrev G : HTGroup p := A.grp S.facts.pos S.sig S.P

end Setup

end UpperTheory.Gal.W2.Seed
