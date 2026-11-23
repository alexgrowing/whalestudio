import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientSupportHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FixedPointImaginarySpan

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsoFam (G : Matrix (Fin r) (Fin r) E) (u : Fin d → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u

def IsHerm {ι : Type} (b : ι → Fin d → Fin d → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)

variable (X : Data E r)

def zmat (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * Data.emb τ.1 (u i) a *
      ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)

def Zb (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (zmat X u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def pairR (χ b : X.Ψ → Fin d → Fin d → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

def embH (β : Matrix (Fin d) (Fin d) E) : X.Ψ → Fin d → Fin d → ℂ := fun τ i k => τ.1 (β i k)

def LZ (d g : ℕ) : Set (X.Ψ → Fin d → Fin d → ℂ) :=
  {b | ∃ β : Matrix (Fin d) (Fin d) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = embH X β}

def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  ∀ b ∈ LZ X d g, ∃ k : ℤ, 2 * pairR X χ b = k

def IsLZBasis (g : ℕ) (ω : Fin (d * d * Fintype.card X.Ψ) → X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  (∀ j, ω j ∈ LZ X d g) ∧
    (∀ b ∈ LZ X d g, ∃! n : Fin (d * d * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω

open Classical in

def fz (u : Fin d → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHerm χ ∧ IsFreqZ X g χ then
    if h : ∃ ω, IsLZBasis (d := d) X g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (d * d * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (Zb X u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * pairR X χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0

def chiAt (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)

def uvec (u : Fin d → Fin r → E) (a : X.Ψ → Fin d → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => ∑ i, a τ i • Data.emb τ.1 (u i)

def embC (a : Fin d → E) : X.Ψ → Fin d → ℂ := fun τ i => τ.1 (a i)

section Two

theorem isIsoFam_two (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) :
    IsIsoFam G u ↔ IsIsoPair G u := Iff.rfl
theorem Zb_two (u : Fin 2 → Fin r → E) : Zb X u = X.Zb u := rfl
theorem LZ_two (g : ℕ) : LZ X 2 g = X.LZ g := rfl
theorem isFreqZ_two (g : ℕ) : IsFreqZ (d := 2) X g = X.IsFreqZ g := rfl
theorem fz_two (u : Fin 2 → Fin r → E) (g : ℕ) : fz X u g = X.fz u g := rfl
theorem chiAt_two : chiAt (d := 2) X = X.chiAt := rfl

end Two

def Am (u : Fin d → Fin r → E) (τ : X.Ψ) : Matrix (Fin r) (Fin d) ℂ :=
  Matrix.of fun a i => Data.emb τ.1 (u i) a

def Cm (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Matrix (Fin d) (Fin r) ℂ :=
  Matrix.of fun i j => -(I * X.c τ) * ∑ k, b τ i k *
    ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)

theorem zmat_eq (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    zmat X u b τ = 1 + Am X u τ * Cm X u b τ := by
  ext a j
  simp only [zmat, Am, Cm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem Cm_add (u : Fin d → Fin r → E) (b b' : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Cm X u (b + b') τ = Cm X u b τ + Cm X u b' τ := by
  ext i j
  simp only [Cm, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem Cm_mul_Am (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) : Cm X u b τ * Am X u τ = 0 := by
  have hS : ∀ i' k, ∑ j, Data.emb τ.1 (u i') j *
      ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l) = 0 := by
    intro i' k
    have h := hermC_emb τ.1 X.Gm (u i') (u k)
    rw [hu, map_zero] at h
    rw [← h]
    simp only [hermC, Finset.mul_sum, mul_assoc]
  ext i i'
  simp only [Cm, Am, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  have : ∑ j, -(I * (X.c τ : ℂ)) *
      (∑ k, b τ i k * ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)) *
      Data.emb τ.1 (u i') j = -(I * X.c τ) * ∑ k, b τ i k *
        ∑ j, Data.emb τ.1 (u i') j * ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [this]
  simp [hS]

theorem zmat_mul (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    zmat X u b τ * zmat X u b' τ = zmat X u (b + b') τ := by
  rw [zmat_eq, zmat_eq, zmat_eq, Cm_add]
  have h := Cm_mul_Am X u hu b τ
  have h0 : Am X u τ * Cm X u b τ * (Am X u τ * Cm X u b' τ) = 0 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Cm X u b τ), h, Matrix.zero_mul, Matrix.mul_zero]
  simp only [mul_add, add_mul, mul_one, one_mul, h0, add_zero]
  rw [Matrix.mul_add, add_assoc]

theorem zmat_det (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) : (zmat X u b τ).det = 1 := by
  rw [zmat_eq, Matrix.det_one_add_mul_comm, Cm_mul_Am X u hu, add_zero, Matrix.det_one]

theorem zmat_zero (u : Fin d → Fin r → E) (τ : X.Ψ) : zmat X u 0 τ = 1 := by
  ext a j; simp [zmat, Matrix.one_apply]

theorem Am_mulVec (u : Fin d → Fin r → E) (τ : X.Ψ) (y : Fin d → ℂ) :
    Am X u τ *ᵥ y = ∑ i, y i • Data.emb τ.1 (u i) := by
  funext a
  simp [Am, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem Cm_mulVec (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) (v : Fin r → ℂ)
    (i : Fin d) :
    (Cm X u b τ *ᵥ v) i =
      -(I * X.c τ) * ∑ k, b τ i k * hermC τ.1 X.Gm v (Data.emb τ.1 (u k)) := by
  simp only [Cm, Matrix.mulVec, dotProduct, Matrix.of_apply, hermC]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem zmat_mulVec (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ)
    (v : Fin r → ℂ) :
    zmat X u b τ *ᵥ v = v + ∑ i, (-(I * X.c τ) *
      ∑ k, b τ i k * hermC τ.1 X.Gm v (Data.emb τ.1 (u k))) • Data.emb τ.1 (u i) := by
  rw [zmat_eq, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, Am_mulVec]
  simp only [Cm_mulVec]

theorem zmat_fix (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) (i : Fin d) :
    zmat X u b τ *ᵥ Data.emb τ.1 (u i) = Data.emb τ.1 (u i) := by
  simp [zmat_mulVec, hermC_emb, hu]

theorem zmat_unitary (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (τ : X.Ψ) (v w : Fin r → ℂ) :
    hermC τ.1 X.Gm (zmat X u b τ *ᵥ v) (zmat X u b τ *ᵥ w) = hermC τ.1 X.Gm v w := by
  have hiso : ∀ i k, hermC τ.1 X.Gm (Data.emb τ.1 (u i)) (Data.emb τ.1 (u k)) = 0 := fun i k => by
    rw [hermC_emb, hu, map_zero]
  have hbc : ∀ i k, conj (b τ i k) = b τ k i := fun i k => (hb τ i k).symm
  have hcI : conj (I * (X.c τ : ℂ)) = -(I * X.c τ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  rw [zmat_mulVec, zmat_mulVec]
  generalize (I * (X.c τ : ℂ)) = q at hcI
  simp only [hermC_add_left, hermC_add_right, hermC_sum_left, hermC_sum_right, hermC_smul_left,
    hermC_smul_right, hiso, map_mul, map_neg, map_sum, hcI, hbc, hermC_conj τ.1 X.Gm_herm,
    mul_zero, Finset.sum_const_zero, add_zero, neg_neg]
  rw [add_assoc, add_eq_left]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  ring

theorem mat_Zb (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (Zb X u b x) τ = zmat X u b τ * mat x τ := rfl

theorem Zb_Zb (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b b' : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) :
    Zb X u b (Zb X u b' x) = Zb X u (b + b') x := by
  funext τ
  show zmat X u b τ * (zmat X u b' τ * mat x τ) = zmat X u (b + b') τ * mat x τ
  rw [← Matrix.mul_assoc, zmat_mul X u hu]

theorem Zb_zero (u : Fin d → Fin r → E) (x : Frame X.Ψ r) : Zb X u 0 x = x := by
  funext τ
  show zmat X u 0 τ * mat x τ = mat x τ
  rw [zmat_zero, Matrix.one_mul]

theorem dmin_Zb (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (Zb X u b x) τ i = dmin X.Gm x τ i := by
  have : gram τ.1 X.Gm (mat (Zb X u b x) τ) = gram τ.1 X.Gm (mat x τ) :=
    X.gram_unitary x τ _ (zmat_unitary X u hu b hb τ)
  simp only [dmin]; rw [this]

theorem Zb_dom (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Zb X u b x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_Zb, Matrix.det_mul, zmat_det X u hu, one_mul]; exact (hx τ).1
  · rw [dmin_Zb X u hu b hb]; exact (hx τ).2 i

theorem nfac_Zb (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (b : X.Ψ → Fin d → Fin d → ℂ) (hb : IsHerm b) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    X.nfac la (Zb X u b x) = X.nfac la x := by
  simp only [Data.nfac, dmin_Zb X u hu b hb]

theorem continuous_Zb (u : Fin d → Fin r → E) (y : Frame X.Ψ r) :
    Continuous fun b : X.Ψ → Fin d → Fin d → ℂ => Zb X u b y := by
  refine continuous_pi fun τ => ?_
  show Continuous fun b : X.Ψ → Fin d → Fin d → ℂ =>
    (zmat X u b τ * mat y τ : Matrix (Fin r) (Fin r) ℂ)
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [zmat, Matrix.of_apply]
  fun_prop

theorem flowV_uvec (u : Fin d → Fin r → E) (a : X.Ψ → Fin d → ℂ) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flowV (uvec X u a) s x = Zb X u (fun τ i k => s τ * a τ i * conj (a τ k)) x := by
  funext τ
  show X.flowMatV (uvec X u a τ) τ (s τ) * mat x τ = zmat X u _ τ * mat x τ
  congr 1
  ext p j
  simp only [Data.flowMatV, zmat, uvec, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, map_sum, map_mul]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem flow_eq_Zb (u : Fin d → Fin r → E) (a : Fin d → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow (∑ i, a i • u i) s x =
      Zb X u (fun τ i k => s τ * embC X a τ i * conj (embC X a τ k)) x := by
  rw [← flowV_uvec]
  have : uvec X u (embC X a) = X.embV (∑ i, a i • u i) := by
    funext τ p
    simp [uvec, embC, Data.embV, Data.emb, Finset.sum_apply]
  rw [this]
  rfl

def Mmat (u : Fin d → Fin r → E) (β : Matrix (Fin d) (Fin d) E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a j => (if a = j then 1 else 0) +
    X.κ0 * ∑ i, ∑ k, β i k * u i a * ∑ l, X.Gm j l * cc (u k l)

theorem Mmat_map (u : Fin d → Fin r → E) (β : Matrix (Fin d) (Fin d) E) (τ : X.Ψ) :
    (Mmat X u β).map τ.1 = zmat X u (embH X β) τ := by
  ext a j
  simp only [Mmat, zmat, embH, Matrix.map_apply, Matrix.of_apply, map_add, map_mul, map_sum,
    Data.emb, emb_cc, X.tau_kappa0, apply_ite, map_one, map_zero]
  ring

theorem embH_add (β β' : Matrix (Fin d) (Fin d) E) : embH X (β + β') = embH X β + embH X β' := by
  funext τ i k; simp [embH]

theorem Mmat_zero (u : Fin d → Fin r → E) : Mmat X u 0 = 1 := by
  ext a j; simp [Mmat, Matrix.one_apply]

theorem Mmat_mul (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β β' : Matrix (Fin d) (Fin d) E) : Mmat X u β * Mmat X u β' = Mmat X u (β + β') := by
  obtain ⟨τ0⟩ := X.nonempty_Psi
  apply Matrix.map_injective τ0.1.injective
  simp only
  rw [Matrix.map_mul, Mmat_map, Mmat_map, Mmat_map, zmat_mul X u hu, embH_add]

def gam (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin d) (Fin d) E) : GL (Fin r) E :=
  ⟨Mmat X u β, Mmat X u (-β), by rw [Mmat_mul X u hu, add_neg_cancel, Mmat_zero],
    by rw [Mmat_mul X u hu, neg_add_cancel, Mmat_zero]⟩

theorem isHerm_embH {β : Matrix (Fin d) (Fin d) E} (hβ : ∀ i k, cc (β i k) = β k i) :
    IsHerm (embH X β) := fun τ i k => by
  simp only [embH]
  rw [← emb_cc, hβ]

theorem isHerm_of_mem_LZ {g : ℕ} {b : X.Ψ → Fin d → Fin d → ℂ} (hb : b ∈ LZ X d g) : IsHerm b := by
  obtain ⟨β, hβ, -, rfl⟩ := hb
  exact isHerm_embH X hβ

theorem herm_Mmat (u : Fin d → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (β : Matrix (Fin d) (Fin d) E) (hβ : ∀ i k, cc (β i k) = β k i) (v w : Fin r → E) :
    herm X.Gm (Mmat X u β *ᵥ v) (Mmat X u β *ᵥ w) = herm X.Gm v w := by
  obtain ⟨τ0⟩ := X.nonempty_Psi
  apply τ0.1.injective
  rw [← hermC_emb, ← hermC_emb, Data.emb_mulVec, Data.emb_mulVec, Mmat_map]
  exact zmat_unitary X u hu _ (isHerm_embH X hβ) τ0 _ _

theorem Mmat_mulVec (u : Fin d → Fin r → E) (β : Matrix (Fin d) (Fin d) E) (v : Fin r → E) :
    Mmat X u β *ᵥ v = v + ∑ i, (X.κ0 * ∑ k, β i k * herm X.Gm v (u k)) • u i := by
  funext a
  simp only [Mmat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, herm, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

section Level

variable (Y : DataX E r)

theorem Mmat_cong (u : Fin d → Fin r → E) (hmem : ∀ i, u i ∈ Y.Λ) (β : Matrix (Fin d) (Fin d) E)
    (hβ : ∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((Y.g * dEnat E : ℕ) : E) / 2 * γ) :
    ∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ, Mmat Y.toData u β *ᵥ v - v = (Y.g : E) • y := by
  intro v hv
  choose γ hγi hγ using hβ
  set D := (NumberField.discr E).natAbs with hd
  have hint : ∀ k, IsIntegral ℤ ((D : E) * (Y.ξ0 * herm Y.Gm v (u k))) :=
    fun k => Y.discr_mul_hermitian_integral hv (hmem k)
  have hc : ∀ i k, IsIntegral ℤ (Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k)) := by
    intro i k
    rcases Y.κ0_xi with h | h
    · have e1 : Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) =
          γ i k * ((D : E) * (Y.ξ0 * herm Y.Gm v (u k))) := by
        rw [h]; ring
      rw [e1]; exact (hγi i k).mul (hint k)
    · have e1 : Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) =
          -(γ i k * ((D : E) * (Y.ξ0 * herm Y.Gm v (u k)))) := by
        rw [h]; ring
      rw [e1]; exact ((hγi i k).mul (hint k)).neg
  set c : Fin d → E := fun i => ∑ k, Y.κ0 / 2 * D * γ i k * herm Y.Gm v (u k) with hcdef
  have hci : ∀ i, IsIntegral ℤ (c i) := fun i => IsIntegral.sum _ fun k _ => hc i k
  refine ⟨∑ i, c i • u i, Submodule.sum_mem _ fun i _ => smul_mem_of_int Y.Λ (hci i) (hmem i), ?_⟩
  rw [Mmat_mulVec, add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [hcdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ i k, hd]
  unfold dEnat
  push_cast
  ring

theorem exists_gamma (u : Fin d → Fin r → E) (hiso : ∀ i k, herm Y.Gm (u i) (u k) = 0)
    (hmem : ∀ i, u i ∈ Y.Λ) (b : Y.Ψ → Fin d → Fin d → ℂ) (hb : b ∈ LZ Y.toData d Y.g) :
    ∃ γ ∈ Y.Γ, (∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (Y.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = zmat Y.toData u b τ := by
  obtain ⟨β, hβh, hβi, rfl⟩ := hb
  have hγc : ∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ, Mmat Y.toData u β *ᵥ v - v = (Y.g : E) • y :=
    Mmat_cong Y u hmem β hβi
  have hγc' : ∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ, Mmat Y.toData u (-β) *ᵥ v - v = (Y.g : E) • y :=
    Mmat_cong Y u hmem (-β) (fun i k => by
      obtain ⟨γ', h1, h2⟩ := hβi i k
      exact ⟨-γ', h1.neg, by simp [h2]⟩)
  have hstab : IsUStab Y.Gm Y.Λ (gam Y.toData u hiso β) := by
    refine ⟨fun x y => herm_Mmat Y.toData u hiso β hβh x y,
      fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨y, hy, hyeq⟩ := hγc x hx
      have e1 : Mmat Y.toData u β *ᵥ x = x + (Y.g : E) • y := by rw [← hyeq]; abel
      show Mmat Y.toData u β *ᵥ x ∈ Y.Λ
      rw [e1]; exact Y.Λ.add_mem hx (Y.g_smul_mem hy)
    · change Mmat Y.toData u β *ᵥ x ∈ Y.Λ at hx
      have hinv : Mmat Y.toData u (-β) *ᵥ (Mmat Y.toData u β *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, Mmat_mul _ u hiso, neg_add_cancel, Mmat_zero, Matrix.one_mulVec]
      obtain ⟨y, hy, hyeq⟩ := hγc' _ hx
      have e1 : Mmat Y.toData u (-β) *ᵥ (Mmat Y.toData u β *ᵥ x) =
          Mmat Y.toData u β *ᵥ x + (Y.g : E) • y := by
        rw [← hyeq]; abel
      rw [← hinv, e1]; exact Y.Λ.add_mem hx (Y.g_smul_mem hy)
  exact ⟨gam Y.toData u hiso β, Y.cong _ hstab hγc, hγc, fun τ => Mmat_map _ u β τ⟩

theorem LZ_periodic (u : Fin d → Fin r → E) (hiso : ∀ i k, herm Y.Gm (u i) (u k) = 0)
    (hmem : ∀ i, u i ∈ Y.Λ) (la : Wt Y.Ψ r) (P : Frame Y.Ψ r → ℂ) (hP : Y.IsSec la P)
    (hχ : ∀ γ ∈ Y.Γ, (∀ v ∈ Y.Λ, ∃ y ∈ Y.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (Y.g : E) • y) → Y.χ la γ = 1)
    (b : Y.Ψ → Fin d → Fin d → ℂ) (hb : b ∈ LZ Y.toData d Y.g) (x : Frame Y.Ψ r) (hx : x ∈ Y.dom) :
    P (Zb Y.toData u b x) = P x := by
  obtain ⟨γ, hγΓ, hγc, hmap⟩ := exists_gamma Y u hiso hmem b hb
  have e1 : Zb Y.toData u b x = lact γ x := funext fun τ => by
    show zmat Y.toData u b τ * mat x τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
    rw [hmap]
  rw [e1, hP.2.2 γ hγΓ x hx, hχ γ hγΓ hγc, one_mul]

end Level

end

end GlobalTheory.MaxCusp
