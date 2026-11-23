import Mathlib
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta

namespace GlobalTheory.HolDS

variable {n : ℕ}

def IsHolChamber (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  ∀ a b, ε a = true → ε b = false → lam b < lam a

def pPlus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ a b, ¬ (ε a = true ∧ ε b = false) → Z a b = 0}

def pMinus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ b a, ¬ (ε b = false ∧ ε a = true) → Z b a = 0}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def raisingSpan (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) ∧
    ∃ v ∈ S, w = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v}

def IsLowestWeightOver (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧
      μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
  (∀ v, IsKFin ε σ v → SmoothVec {X | inG ε X} σ v) ∧
  (∀ Z ∈ pMinus ε, ∀ v ∈ lowKSub ε lam σ, GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = 0) ∧
  ∀ v, IsKFin ε σ v ↔ v ∈ raisingSpan ε σ (lowKSub ε lam σ)

end GlobalTheory.HolDS

namespace GlobalTheory.Published

open GlobalTheory.HolDS

def HolomorphicDiscreteSeries : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ → IsLowestWeightOver ε lam σ

end GlobalTheory.Published

namespace GlobalTheory.HolDS

open Formalism.L2.NTheta

variable {n : ℕ}

theorem single_mem_pPlus {ε : Fin n → Bool} {a b : Fin n} (ha : ε a = true) (hb : ε b = false) (z : ℂ) :
    Matrix.single a b z ∈ pPlus ε := by
  intro c d h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨ha, hb⟩

theorem single_mem_pMinus {ε : Fin n → Bool} {a b : Fin n} (ha : ε a = true) (hb : ε b = false) (z : ℂ) :
    Matrix.single b a z ∈ pMinus ε := by
  intro c d h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨hb, ha⟩

theorem torus_mul_single (θ : Fin n → ℝ) (a b : Fin n) :
    (Matrix.diagonal fun c => Complex.exp ((θ c : ℂ) * Complex.I)) * Matrix.single a b (1 : ℂ) =
      Complex.exp (((∑ c, root a b c * θ c : ℝ) : ℂ) * Complex.I) •
        (Matrix.single a b (1 : ℂ) * Matrix.diagonal fun c => Complex.exp ((θ c : ℂ) * Complex.I)) := by
  have h : ∑ c, root a b c * θ c = θ a - θ b := by
    simp [root, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  rw [h]
  ext c d
  rw [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    rw [mul_one, one_mul, smul_eq_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp

theorem IsHolChamber.lt {ε : Fin n → Bool} {lam : Fin n → ℝ} (h : IsHolChamber ε lam) (hl : StrictAnti lam)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = false) : a < b :=
  hl.lt_iff_gt.1 (h a b ha hb)

theorem le_raisingSpan {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : S ≤ raisingSpan ε σ S :=
  fun v hv => Submodule.subset_span ⟨[], by simp, v, hv, rfl⟩

theorem dRepC_single_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Fin n → ℝ} {v : H} (hv : IsWtOn (Kset ε) σ μ v)
    (a : Fin n) : GlobalTheory.SmVec.dRepC (Jm ε) σ (Matrix.single a a 1) v = (μ a : ℂ) • v := by
  have hJ : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv (Jm_mul_self ε)
  have hc : GlobalTheory.SmVec.conjG (Jm ε) (Matrix.single a a (1 : ℂ)) = -Matrix.single a a 1 := by
    unfold GlobalTheory.SmVec.conjG
    rw [hJ]
    congr 1
    ext c d
    simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h : a = c ∧ a = d
    · obtain ⟨rfl, rfl⟩ := h
      cases ε a <;> simp
    · have h' : ¬ (a = d ∧ a = c) := fun h' => h ⟨h'.2, h'.1⟩
      rw [if_neg h, if_neg h']
      simp
  have he : ∀ t : ℝ, σ (NormedSpace.exp (t • ((1 / (2 * Complex.I)) •
      (Matrix.single a a (1 : ℂ) - -Matrix.single a a 1)))) v =
      Complex.exp ((-(μ a : ℂ) * Complex.I) * t) • v := by
    intro t
    have h1 : t • ((1 / (2 * Complex.I)) • (Matrix.single a a (1 : ℂ) - -Matrix.single a a 1)) =
        Matrix.diagonal fun c => (((Pi.single a (-t) : Fin n → ℝ) c : ℝ) : ℂ) * Complex.I := by
      ext c d
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply, Matrix.diagonal_apply,
        Pi.single_apply, smul_eq_mul, Complex.real_smul]
      by_cases h : a = c ∧ a = d
      · obtain ⟨rfl, rfl⟩ := h
        simp only [and_self, if_true]
        field_simp
        push_cast
        linear_combination (2 * (t : ℂ)) * Complex.I_sq
      · rw [if_neg h]
        split_ifs with h2 h3
        · exact absurd ⟨h3.symm, h3.symm.trans h2⟩ h
        · simp
        · simp
    have h2 : NormedSpace.exp (Matrix.diagonal fun c => (((Pi.single a (-t) : Fin n → ℝ) c : ℝ) : ℂ) * Complex.I) =
        Matrix.diagonal fun c => Complex.exp ((((Pi.single a (-t) : Fin n → ℝ) c : ℝ) : ℂ) * Complex.I) := by
      rw [Matrix.exp_diagonal]
      congr 1
      funext c
      rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]
    rw [h1, h2, hv]
    · congr 2
      simp [Pi.single_apply]
      ring
    · refine ⟨?_, by unfold Jm; exact Matrix.commute_diagonal _ _⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext c
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_ofReal_mul_I]
      simp
  unfold GlobalTheory.SmVec.dRepC dRep
  rw [hc, add_neg_cancel, smul_zero]
  simp only [smul_zero, deriv_const, zero_add, he]
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((-(μ a : ℂ) * Complex.I) * t) • v)
      ((-(μ a : ℂ) * Complex.I) • v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (-(μ a : ℂ) * Complex.I) * t) (-(μ a : ℂ) * Complex.I) 0 := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (-(μ a : ℂ) * Complex.I)
    simpa using h1.cexp.smul_const v
  rw [hd.deriv, smul_smul]
  congr 1
  linear_combination (-(μ a : ℂ)) * Complex.I_sq

variable {p q : ℕ} {κ : Fin p ⊕ Fin q → ℤ}

theorem strictAnti_holEnt (h : HolOK p q κ) :
    StrictAnti fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective c
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rw [Fin.lt_def] at hcd
  rcases x with i | i <;> rcases y with j | j <;> simp at hcd
  · have h1 : ((κ (Sum.inl j) : ℤ) : ℚ) ≤ κ (Sum.inl i) := by exact_mod_cast h.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inl]
    linarith
  · exact h.2.2 i j
  · omega
  · have h1 : ((κ (Sum.inr j) : ℤ) : ℚ) ≤ κ (Sum.inr i) := by exact_mod_cast h.2.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inr]
    linarith

theorem holOK_one_one : HolOK 1 1 (Sum.elim (fun _ => 1) fun _ => -1) := by
  refine ⟨fun _ _ _ => le_rfl, fun _ _ _ => le_rfl, fun i j => ?_⟩
  simp only [holEnt, Sum.elim_inl, Sum.elim_inr, Fin.val_eq_zero]
  norm_num

theorem enum_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lam (Fin.cast hn (finSumFinEquiv x)) = holEnt p q κ x ∧
      ε (Fin.cast hn (finSumFinEquiv x)) = Sum.elim (fun _ => true) (fun _ => false) x := by
  obtain ⟨hl, r, hr, hS⟩ := he
  have hra : StrictAnti r := fun a b hab => by
    have := hl hab
    rw [hr, hr] at this
    exact_mod_cast this
  have hs := strictAnti_holEnt h
  have hinj : Function.Injective (holEnt p q κ) := fun x y hxy =>
    finSumFinEquiv.injective (hs.injective (by simpa using hxy))
  have hn : p + q = n := by
    have := congrArg Finset.card hS
    unfold holPar at this
    rw [Finset.card_image_of_injective _ fun x y hxy => hinj (congrArg Prod.fst hxy),
      Finset.card_image_of_injective _ fun x y hxy => hra.injective (congrArg Prod.fst hxy)] at this
    simpa using this
  subst hn
  have hm : ∀ z, (∃ x, (holEnt p q κ x, Sum.elim (fun _ => true) (fun _ => false) x) = z) ↔
      ∃ a, (r a, ε a) = z := fun z => by
    simpa [holPar] using Finset.ext_iff.1 hS z
  have hrr : (fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c)) = r := by
    rw [← hs.range_inj hra]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := (hm _).1 ⟨finSumFinEquiv.symm c, rfl⟩
      exact ⟨a, congrArg Prod.fst ha⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := (hm _).2 ⟨a, rfl⟩
      exact ⟨finSumFinEquiv x, by simpa using congrArg Prod.fst hx⟩
  refine ⟨rfl, fun x => ?_⟩
  have h1 : r (finSumFinEquiv x) = holEnt p q κ x := by rw [← hrr]; simp
  refine ⟨by rw [Fin.cast_eq_self, hr, h1], ?_⟩
  obtain ⟨y, hy⟩ := (hm _).2 ⟨finSumFinEquiv x, rfl⟩
  obtain rfl : y = x := hinj ((congrArg Prod.fst hy).trans h1)
  exact (congrArg Prod.snd hy).symm

theorem isHCParam_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    IsHCParam lam ∧ IsHolChamber ε lam := by
  obtain ⟨rfl, hx⟩ := enum_holPar h he
  simp only [Fin.cast_eq_self] at hx
  refine ⟨⟨he.1, fun a => ?_⟩, fun a b ha hb => ?_⟩
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective a
    rw [(hx x).1]
    rcases x with i | i
    · exact ⟨κ (Sum.inl i) - q - (i : ℕ), by simp only [holEnt, Sum.elim_inl]; push_cast; ring⟩
    · exact ⟨κ (Sum.inr i) - (i : ℕ), by simp only [holEnt, Sum.elim_inr]; push_cast; ring⟩
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective b
    rw [(hx _).2] at ha hb
    rw [(hx x).1, (hx y).1]
    rcases x with i | i <;> rcases y with j | j <;> simp at ha hb
    exact_mod_cast h.2.2 i j

theorem lowK_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lowK ε lam (Fin.cast hn (finSumFinEquiv x)) = κ x := by
  obtain ⟨rfl, hx⟩ := enum_holPar h he
  simp only [Fin.cast_eq_self] at hx
  refine ⟨rfl, fun x => ?_⟩
  have hc : ∀ P : Fin (p + q) → Prop, ∀ _ : DecidablePred P, (univ.filter P).card =
      (univ.filter fun i : Fin p => P (finSumFinEquiv (Sum.inl i))).card +
        (univ.filter fun j : Fin q => P (finSumFinEquiv (Sum.inr j))).card := by
    intro P _
    simp only [Finset.card_filter]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Fin.cast_eq_self, lowK, Pi.add_apply, Pi.sub_apply, rhoN, rhoC]
  rw [hc, hc, hc, hc, (hx x).1]
  simp only [(hx _).2]
  rcases x with i | i
  · have h1 : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd p j := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin q, ¬ Fin.natAdd p j < Fin.castAdd q i := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin p, Fin.castAdd q j < Fin.castAdd q j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((p - 1 - i : ℕ)) : ℝ) = p - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring
  · have h1 : ∀ j : Fin p, Fin.castAdd q j < Fin.natAdd p i := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin p, ¬ Fin.natAdd p i < Fin.castAdd q j := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin q, Fin.natAdd p j < Fin.natAdd p j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((q - 1 - i : ℕ)) : ℝ) = q - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring

end GlobalTheory.HolDS

namespace GlobalTheory.Published

theorem HolomorphicDiscreteSeries.of_holOK (hp : HolomorphicDiscreteSeries) {p q : ℕ} {κ : Fin p ⊕ Fin q → ℤ}
    (h : Formalism.L2.NTheta.HolOK p q κ) {n : ℕ} {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (he : IsEnum (Formalism.L2.NTheta.holPar p q κ) lam ε) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : GlobalTheory.HolDS.IsLowestWeightOver ε lam σ :=
  hp n ε lam (GlobalTheory.HolDS.isHCParam_holPar h he).1 (GlobalTheory.HolDS.isHCParam_holPar h he).2 H σ hσ

end GlobalTheory.Published

end
