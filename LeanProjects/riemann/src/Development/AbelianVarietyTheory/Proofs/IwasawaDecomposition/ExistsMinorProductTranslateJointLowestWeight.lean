import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FsubMinorMinus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JointHarm.MinorBottom

section Mat

variable {m : ℕ}

def revTail (m p : ℕ) : Equiv.Perm (Fin m) :=
  Function.Involutive.toPerm
    (fun a => if h : (a : ℕ) < p then a else ⟨p + (m - 1 - a), by have := a.isLt; omega⟩)
    (fun a => by
      have := a.isLt
      by_cases h : (a : ℕ) < p
      · simp [h]
      · simp only [h, dite_false]
        rw [dif_neg (by simp)]
        ext
        simp only
        omega)

theorem revTail_val (p : ℕ) (a : Fin m) :
    (revTail m p a : ℕ) = if (a : ℕ) < p then (a : ℕ) else p + (m - 1 - a) := by
  change ((if h : (a : ℕ) < p then a else ⟨p + (m - 1 - a), by have := a.isLt; omega⟩ : Fin m) : ℕ) = _
  by_cases h : (a : ℕ) < p <;> simp [h]

theorem revTail_mul_self (p : ℕ) : revTail m p * revTail m p = 1 := by
  ext a
  have := a.isLt
  simp only [Equiv.Perm.mul_apply, revTail_val, Equiv.Perm.one_apply]
  split_ifs <;> omega

theorem revTail_symm (p : ℕ) : (revTail m p).symm = revTail m p := rfl

theorem comm_Jm_iff (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) :
    k * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * k ↔ ∀ a b, k a b ≠ 0 → ε a = ε b := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun a b => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  cases ε a <;> cases ε b <;> simp [neg_eq_iff_add_eq_zero, eq_neg_iff_add_eq_zero]

theorem perm_conj (σ : Equiv.Perm (Fin m)) (hσ : σ.symm = σ) (k : Matrix (Fin m) (Fin m) ℂ) :
    σ.permMatrix ℂ * k * σ.permMatrix ℂ = k.submatrix σ σ := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, hσ]
  rfl

theorem perm_mem_Kset (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a) :
    σ.permMatrix ℂ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, (comm_Jm_iff _ _).2 fun a b hab => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp
  · have : σ a = b := by
      by_contra hne
      exact hab (by simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hne])
    rw [← this, h]

theorem Kset_KC {ε : Fin m → Bool} {k : Matrix (Fin m) (Fin m) ℂ} (h : k ∈ Formalism.REAL.Kset ε) :
    k ∈ GlobalTheory.Dec.KC ε :=
  ⟨(Unitary.toUnits ⟨k, h.1⟩).isUnit, h.2⟩

theorem KC_mul {ε : Fin m → Bool} {a b : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε)
    (hb : b ∈ GlobalTheory.Dec.KC ε) : a * b ∈ GlobalTheory.Dec.KC ε :=
  ⟨ha.1.mul hb.1, by rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]⟩

theorem KC_one (ε : Fin m → Bool) : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ GlobalTheory.Dec.KC ε :=
  ⟨isUnit_one, by simp⟩

theorem KC_inv_transpose {ε : Fin m → Bool} {a : Matrix (Fin m) (Fin m) ℂ} (ha : a ∈ GlobalTheory.Dec.KC ε) :
    (a⁻¹)ᵀ ∈ GlobalTheory.Dec.KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  have h1 : a⁻¹ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * a⁻¹ := by
    calc a⁻¹ * Formalism.REAL.Jm ε = a⁻¹ * (Formalism.REAL.Jm ε * a) * a⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
      _ = Formalism.REAL.Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  refine ⟨by simpa using ha.1, (comm_Jm_iff _ _).2 fun x y h => ?_⟩
  exact ((comm_Jm_iff _ _).1 h1 y x h).symm

theorem detP_submatrix (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a)
    (k : Matrix (Fin m) (Fin m) ℂ) (hk : ∀ a b, k a b ≠ 0 → a ≤ b) :
    detP ε (k.submatrix σ σ) = ∏ a, if ε a then k a a else 1 := by
  have e : (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k.submatrix σ σ + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) =
      (Matrix.of fun a b => if ε a then k a b else if a = b then 1 else 0).submatrix σ σ := by
    ext a b
    simp only [Formalism.REAL.Jm, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_sub,
      ← Matrix.diagonal_smul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.submatrix_apply,
      Matrix.of_apply, h, Matrix.diagonal_apply, Pi.smul_apply, EmbeddingLike.apply_eq_iff_eq]
    cases ε a <;> by_cases hab : a = b <;> simp [hab] <;> ring
  rw [detP, e, Matrix.det_submatrix_equiv_self, Matrix.det_of_isUpperTriangular]
  · simp
  · intro a b hab
    have h1 : k a b = 0 := by
      by_contra h0
      exact absurd (hk a b h0) (not_le.2 hab)
    have h2 : a ≠ b := ne_of_gt hab
    simp [h1, h2]

theorem detM_submatrix (ε : Fin m → Bool) (σ : Equiv.Perm (Fin m)) (h : ∀ a, ε (σ a) = ε a)
    (k : Matrix (Fin m) (Fin m) ℂ) (hk : ∀ a b, k a b ≠ 0 → a ≤ b) :
    detM ε (k.submatrix σ σ) = ∏ a, if ε a then 1 else k a a := by
  have e : (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k.submatrix σ σ + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) =
      (Matrix.of fun a b => if ε a then (if a = b then 1 else 0) else k a b).submatrix σ σ := by
    ext a b
    simp only [Formalism.REAL.Jm, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_sub,
      ← Matrix.diagonal_smul, Matrix.add_apply, Matrix.diagonal_mul, Matrix.submatrix_apply,
      Matrix.of_apply, h, Matrix.diagonal_apply, Pi.smul_apply, EmbeddingLike.apply_eq_iff_eq]
    cases ε a <;> by_cases hab : a = b <;> simp [hab] <;> ring
  rw [detM, e, Matrix.det_submatrix_equiv_self, Matrix.det_of_isUpperTriangular]
  · simp
  · intro a b hab
    have h1 : k a b = 0 := by
      by_contra h0
      exact absurd (hk a b h0) (not_le.2 hab)
    have h2 : a ≠ b := ne_of_gt hab
    simp [h1, h2]

theorem det_lo {u : Matrix (Fin m) (Fin m) ℂ} (hu : GlobalTheory.Dec.IsLo u) : u.det = ∏ j, u j j :=
  Matrix.det_of_lowerTriangular u (fun i j h => hu i j (by simpa using h))

theorem inv_transpose_lo {g : Matrix (Fin m) (Fin m) ℂ} (hg : IsUnit g) (hl : GlobalTheory.Dec.IsLo g) :
    (∀ a b, (g⁻¹)ᵀ a b ≠ 0 → a ≤ b) ∧ ∀ a, (g⁻¹)ᵀ a a = (g a a)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  letI := hg.invertible
  have hb : g.BlockTriangular OrderDual.toDual := fun i j h => hl i j (by simpa using h)
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have h0 : ∀ a b, a < b → g⁻¹ a b = 0 := fun a b h => hi (by simpa using h)
  refine ⟨fun a b h => not_lt.1 fun hlt => h (h0 b a hlt), fun a => ?_⟩
  have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul g hd) a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single a] at h1
  · exact eq_inv_of_mul_eq_one_left h1
  · intro b _ hba
    rcases lt_or_gt_of_ne hba with h | h
    · rw [hl b a h, mul_zero]
    · rw [h0 a b h, zero_mul]
  · simp

end Mat

theorem eigen (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ)
    (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ) (hmn : m ≤ n) (hpq : ∀ τ, p τ + q τ = m)
    (hε : ∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) (hap : ∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a)
    (ham : ∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hk : ∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) (hup : ∀ τ a b, k τ a b ≠ 0 → a ≤ b) (hk0 : ∀ τ a, k τ a a ≠ 0)
    (hu : ∀ τ, IsUnit (u τ) ∧ GlobalTheory.Dec.IsLo (u τ)) :
    fact ε x₁ x₂ x₃ k u
        (fact ε x₁ x₂ x₃ (fun τ => (revTail m (p τ)).permMatrix ℂ) 1 (delta p q ap am : PolF D m n)) =
      (∏ τ, (∏ a, k τ a a ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a) *
          ∏ j, u τ j j ^ wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j) •
        fact ε x₁ x₂ x₃ (fun τ => (revTail m (p τ)).permMatrix ℂ) 1 (delta p q ap am : PolF D m n) := by
  obtain ⟨-, hmul, -⟩ := GlobalTheory.JointHarm.fact_one_mul_adj D m n ε x₁ x₂ x₃
  have hσ : ∀ τ a, ε τ (revTail m (p τ) a) = ε τ a := by
    intro τ a
    rw [hε, hε, revTail_val]
    split_ifs with h <;> simp [h]
  set κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ := fun τ => (revTail m (p τ)).permMatrix ℂ with hκ
  have hκK : ∀ τ, κ τ ∈ GlobalTheory.Dec.KC (ε τ) := fun τ => Kset_KC (perm_mem_Kset _ _ (hσ τ))
  have hκ2 : κ * κ = 1 := by
    funext τ
    simp [hκ, ← Matrix.permMatrix_mul, revTail_mul_self]
  have hk' : ∀ τ, (κ * k * κ) τ ∈ GlobalTheory.Dec.KC (ε τ) := fun τ => KC_mul (KC_mul (hκK τ) (hk τ)) (hκK τ)
  have hsub : ∀ τ, (κ * k * κ) τ = (k τ).submatrix (revTail m (p τ)) (revTail m (p τ)) :=
    fun τ => perm_conj _ (revTail_symm _) _
  have h1 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  have e1 : fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ κ 1 =
      fact ε x₁ x₂ x₃ κ 1 * fact ε x₁ x₂ x₃ (κ * k * κ) u := by
    rw [← hmul _ _ _ _ hk hκK (fun τ => (hu τ).1) h1, ← hmul _ _ _ _ hκK hk' h1 (fun τ => (hu τ).1),
      ← mul_assoc, ← mul_assoc, hκ2, one_mul, one_mul, mul_one]
  have hd := GlobalTheory.JointHarm.DeltaEig.fsub_delta D m n ε p q ap am hmn hpq hε hap ham (κ * k * κ) u hk' (by
    intro τ a b hab
    rw [hsub, Matrix.submatrix_apply] at hab
    have h2 : (revTail m (p τ) a : ℕ) ≤ revTail m (p τ) b := hup τ _ _ hab
    have h3 := (comm_Jm_iff _ _).1 (hk τ).2 _ _ hab
    rw [hσ, hσ, hε, hε, decide_eq_decide] at h3
    rw [revTail_val, revTail_val] at h2
    have := a.isLt
    have := b.isLt
    simp only [Fin.le_def]
    split_ifs at h2 <;> omega) hu
  rw [← Module.End.mul_apply, e1, Module.End.mul_apply, ← map_smul]
  congr 1
  rw [fact, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hd, smul_smul, fchar, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hu0 : ∀ j, u τ j j ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 (hu τ).1).ne_zero
    rw [det_lo (hu τ).2, Finset.prod_ne_zero_iff] at this
    exact fun j => this j (Finset.mem_univ _)
  rw [hsub, detP_submatrix _ _ (hσ τ) _ (hup τ), detM_submatrix _ _ (hσ τ) _ (hup τ), det_lo (hu τ).2,
    mul_mul_mul_comm, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_zpow,
    ← Finset.prod_mul_distrib]
  congr 1
  · rw [← Equiv.prod_comp (revTail m (p τ)) (fun a => (if ε τ a then k τ a a else 1) ^ x₁ τ *
        (if ε τ a then 1 else k τ a a) ^ x₂ τ),
      ← Equiv.prod_comp (revTail m (p τ)) (fun a => k τ a a ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have := a.isLt
    have hp := hpq τ
    rw [hσ, hε, Matrix.submatrix_apply, wtK, revTail_val]
    by_cases h : (a : ℕ) < p τ
    · simp [h, zpow_add₀ (hk0 τ _), mul_comm]
    · have h4 : m - 1 - (p τ + (m - 1 - a)) = a - p τ := by omega
      simp only [h, if_false, decide_false, Bool.false_eq_true, _root_.one_zpow, one_mul, h4]
      rw [if_neg (by omega), zpow_add₀ (hk0 τ _), mul_comm]
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_add₀ (hu0 j)]
    congr 1
    simp only [wtU]
    ring

theorem isUnit_diag_exp {n : ℕ} (θ : Fin n → ℝ) :
    IsUnit (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  exact fun a _ => Complex.exp_ne_zero _

theorem mulSingle_cases {ι M : Type} [DecidableEq ι] [One M] (P : ι → M → Prop) (τ : ι) (g : M) (hg : P τ g)
    (h1 : ∀ i, P i 1) (i : ι) : P i ((Pi.mulSingle τ g : ι → M) i) := by
  by_cases h : i = τ
  · subst h
    simpa using hg
  · simpa [h] using h1 i

theorem isLo_one (n : ℕ) : GlobalTheory.Dec.IsLo (1 : Matrix (Fin n) (Fin n) ℂ) :=
  fun _ _ h => Matrix.one_apply_ne (ne_of_lt h)

theorem exists_joint_bottom : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), m ≤ n → (∀ τ, p τ + q τ = m) → (∀ τ a, ε τ a = decide ((a : ℕ) < p τ)) → (∀ τ a b, a ≤ b → b < p τ → ap τ b ≤ ap τ a) → (∀ τ a b, a ≤ b → b < q τ → am τ b ≤ am τ a) → ∃ (κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (Δ' : PolF D m n), (∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ)) ∧ fact ε x₁ x₂ x₃ κ 1 Δ' = delta p q ap am ∧ IsBotFam ε (factK n ε x₁ x₂ x₃) (fun τ a => -(wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a : ℝ)) Δ' ∧ IsBotFam (fun _ => allPos n) (factU ε x₁ x₂ x₃) (fun τ j => (wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j : ℝ)) Δ' := by
  intro D m n ε p q ap am x₁ x₂ x₃ hmn hpq hε hap ham
  have hE := eigen D m n ε p q ap am x₁ x₂ x₃ hmn hpq hε hap ham
  obtain ⟨hone, hmul, -⟩ := GlobalTheory.JointHarm.fact_one_mul_adj D m n ε x₁ x₂ x₃
  have hσ : ∀ τ a, ε τ (revTail m (p τ) a) = ε τ a := by
    intro τ a
    rw [hε, hε, revTail_val]
    split_ifs with h <;> simp [h]
  set κ : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ := fun τ => (revTail m (p τ)).permMatrix ℂ with hκ
  have hκK : ∀ τ, κ τ ∈ Formalism.REAL.Kset (ε τ) := fun τ => perm_mem_Kset _ _ (hσ τ)
  have hκ2 : κ * κ = 1 := by
    funext τ
    simp [hκ, ← Matrix.permMatrix_mul, revTail_mul_self]
  have h1 : ∀ τ, IsUnit ((1 : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) τ) := fun _ => isUnit_one
  set Δ' : PolF D m n := fact ε x₁ x₂ x₃ κ 1 (delta p q ap am : PolF D m n) with hΔ
  have hK : ∀ τ (g : Matrix (Fin m) (Fin m) ℂ), g ∈ GlobalTheory.Dec.KC (ε τ) → GlobalTheory.Dec.IsLo g →
      factK n ε x₁ x₂ x₃ (Pi.mulSingle τ g) Δ' =
        (∏ a, (g a a)⁻¹ ^ wtK (p τ) (ap τ) (am τ) (x₁ τ) (x₂ τ) a) • Δ' := by
    intro τ g hg hl
    have hg' := mulSingle_cases (fun i g => g ∈ GlobalTheory.Dec.KC (ε i) ∧ GlobalTheory.Dec.IsLo g) τ g ⟨hg, hl⟩
      (fun i => ⟨KC_one _, isLo_one _⟩)
    have hi := fun i => inv_transpose_lo (hg' i).1.1 (hg' i).2
    rw [factK, hE _ 1 (fun i => KC_inv_transpose (hg' i).1) (fun i => (hi i).1) ?_
      (fun i => ⟨isUnit_one, isLo_one _⟩)]
    · congr 1
      rw [Finset.prod_eq_single τ]
      · simp only [(hi τ).2]
        simp
      · intro i _ hne
        simp [hne]
      · simp
    · intro i a
      have := ((Matrix.isUnit_iff_isUnit_det _).1 (hg' i).1.1).ne_zero
      rw [det_lo (hg' i).2, Finset.prod_ne_zero_iff] at this
      rw [(hi i).2]
      exact inv_ne_zero (this a (Finset.mem_univ _))
  have hU : ∀ τ (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → GlobalTheory.Dec.IsLo g →
      factU ε x₁ x₂ x₃ (Pi.mulSingle τ g) Δ' =
        (∏ j, g j j ^ wtU (p τ) (q τ) (ap τ) (am τ) (x₃ τ) j) • Δ' := by
    intro τ g hg hl
    have hg' := mulSingle_cases (fun _ g => IsUnit g ∧ GlobalTheory.Dec.IsLo g) τ g ⟨hg, hl⟩
      (fun i => ⟨isUnit_one, isLo_one _⟩)
    rw [factU, hE 1 _ (fun i => KC_one _) ?_ (fun i a => by simp) hg']
    · congr 1
      rw [Finset.prod_eq_single τ]
      · simp
      · intro i _ hne
        simp [hne]
      · simp
    · intro i a b hab
      by_contra h
      exact hab (Matrix.one_apply_ne (fun e => h e.le))
  have hdl : ∀ {l : ℕ} (v : Fin l → ℂ), GlobalTheory.Dec.IsLo (Matrix.diagonal v) :=
    fun v _ _ h => Matrix.diagonal_apply_ne _ (ne_of_lt h)
  refine ⟨κ, Δ', hκK, ?_, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩, fun τ => ⟨fun g hg hl => ?_, fun θ => ?_⟩⟩
  · rw [hΔ, ← Module.End.mul_apply, ← hmul _ _ _ _ (fun τ => Kset_KC (hκK τ)) (fun τ => Kset_KC (hκK τ)) h1 h1,
      hκ2, mul_one, hone, Module.End.one_apply]
  · have := hK τ g hg (fun i j h => (hl i j).1 h)
    simpa [fun a => (hl a a).2 rfl] using this
  · refine (hK τ _ ⟨isUnit_diag_exp θ, ?_⟩ (hdl _)).trans ?_
    · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]
    · congr 1
      simp only [Matrix.diagonal_apply_eq, ← Complex.exp_neg, ← Complex.exp_int_mul, ← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
  · have := hU τ g hg.1 (fun i j h => (hl i j).1 h)
    simpa [fun a => (hl a a).2 rfl] using this
  · refine (hU τ _ (isUnit_diag_exp θ) (hdl _)).trans ?_
    congr 1
    simp only [Matrix.diagonal_apply_eq, ← Complex.exp_int_mul, ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.JointHarm.MinorBottom

end
