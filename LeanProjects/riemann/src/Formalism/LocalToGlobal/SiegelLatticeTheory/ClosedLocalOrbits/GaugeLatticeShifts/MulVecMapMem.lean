import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

noncomputable section

open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

namespace SetCorrespondence

abbrev Mk (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
abbrev Vk (k r : ℕ) := Fin (2 * r + k + 1) → ℂ

variable {k r : ℕ}

def stdX (k r : ℕ) (b : Fin r) : Vk k r := Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b)

def supSub (k r a : ℕ) : Submodule ℂ (Vk k r) where
  carrier := {v | ∀ i : Fin (2 * r + k + 1), a ≤ i.val → v i = 0}
  add_mem' := by
    intro v w hv hw i hi
    simp only [Set.mem_ofPred_eq] at hv hw
    simp [hv i hi, hw i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by
    intro c v hv i hi
    simp only [Set.mem_ofPred_eq] at hv
    simp [hv i hi]

lemma mem_supSub {a : ℕ} {v : Vk k r} :
    v ∈ supSub k r a ↔ ∀ i : Fin (2 * r + k + 1), a ≤ i.val → v i = 0 := Iff.rfl

lemma supSub_mono {a b : ℕ} (h : a ≤ b) {v : Vk k r} (hv : v ∈ supSub k r a) : v ∈ supSub k r b :=
  mem_supSub.2 fun i hi => mem_supSub.1 hv i (le_trans h hi)

lemma colEntry (A : Mk k r) (i j : Fin (2 * r + k + 1)) : (A *ᵥ Formalism.QuantumDeterminants.bvec j) i = A i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma span_eq (a : ℕ) (ha : a ≤ r) :
    Submodule.span ℂ (stdX k r '' {b | b.1 < a}) = supSub k r a := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, mem_supSub]
    intro i hi
    have hb' : b.1 < a := hb
    simp only [stdX, Formalism.QuantumDeterminants.bvec]
    rw [Pi.single_apply, if_neg]
    intro h
    have h2 : i.val = b.val := congrArg Fin.val h
    omega
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases h : i.val < a
    · have hi : i = Formalism.QuantumDeterminants.eI k r ⟨i.val, by omega⟩ := Fin.ext rfl
      have e : Pi.single i (v i) = v i • stdX k r ⟨i.val, by omega⟩ := by
        rw [stdX, ← hi]; ext j; simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h, rfl⟩)
    · rw [mem_supSub.1 hv i (by omega), Pi.single_zero]
      exact Submodule.zero_mem _

lemma mulVec_map_mem (P : Mk k r) (hP : IsUnit P.det) (S : Submodule ℂ (Vk k r)) (w : Vk k r) :
    P *ᵥ w ∈ S.map P.mulVecLin ↔ w ∈ S := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyw⟩
    rw [Matrix.mulVecLin_apply] at hyw
    have h2 : P⁻¹ *ᵥ (P *ᵥ y) = P⁻¹ *ᵥ (P *ᵥ w) := by rw [hyw]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec,
      Matrix.one_mulVec] at h2
    exact h2 ▸ hy
  · intro hw
    exact ⟨w, hw, by simp⟩

lemma transport (P U : Mk k r) (hP : IsUnit P.det) (w : Vk k r) :
    (U - 1) *ᵥ (P *ᵥ w) = P *ᵥ ((P⁻¹ * U * P - 1) *ᵥ w) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [mul_sub, sub_mul, one_mul, mul_one, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hP, one_mul]

def InSstd (g : Mk k r) (zH : Vk k r) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ stdX k r a ∈ supSub k r a.1) ∧ (g - 1) *ᵥ zH ∈ supSub k r r

lemma inS_transport (P : Mk k r) (hP : IsUnit P.det) (zH : Vk k r) (U : Mk k r) :
    Formalism.L2.SG.HidaSetting.InS (fun a => P *ᵥ stdX k r a) (P *ᵥ zH) U ↔ InSstd (P⁻¹ * U * P) zH := by
  have hsp : ∀ a : ℕ, a ≤ r → ∀ w, P *ᵥ w ∈ Formalism.L2.SG.HidaSetting.spanLt (fun a => P *ᵥ stdX k r a) a ↔
      w ∈ supSub k r a := by
    intro a ha w
    have : Formalism.L2.SG.HidaSetting.spanLt (fun a => P *ᵥ stdX k r a) a =
        (Submodule.span ℂ (stdX k r '' {b | b.1 < a})).map P.mulVecLin := by
      rw [Formalism.L2.SG.HidaSetting.spanLt, Submodule.map_span, ← Set.image_comp]; rfl
    rw [this, mulVec_map_mem P hP, span_eq a ha]
  simp only [Formalism.L2.SG.HidaSetting.InS, InSstd]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, ?_⟩
    · have := h1 a; rw [transport P U hP] at this; exact (hsp a.1 a.2.le _).1 this
    · rw [transport P U hP] at h2; exact (hsp r le_rfl _).1 h2
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, ?_⟩
    · rw [transport P U hP]; exact (hsp a.1 a.2.le _).2 (h1 a)
    · rw [transport P U hP]; exact (hsp r le_rfl _).2 h2

lemma fixX (A : Mk k r) (hA : ∀ b, A *ᵥ stdX k r b = stdX k r b) (v : Vk k r) (hv : v ∈ supSub k r r) :
    A *ᵥ v = v := by
  rw [← span_eq r le_rfl] at hv
  have hle : Submodule.span ℂ (stdX k r '' {b | b.1 < r}) ≤ LinearMap.ker (A - 1).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨b, _, rfl⟩
    simp [hA b]
  have := hle hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  exact this

lemma Hpk_apply' (i j : Fin (2 * r + k + 1)) : Formalism.QuantumDeterminants.Hpk k r i j =
    if i.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val then (if i.val = r + k then -1 else 1) else 0 := by
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]

lemma HpkMul (A : Mk k r) (p : Fin (2 * r + k + 1)) (hp : p.val < r) (j : Fin (2 * r + k + 1)) :
    (Formalism.QuantumDeterminants.Hpk k r * A) p j = A ⟨2 * r + k - p.val, by omega⟩ j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]
  · rw [Hpk_apply', if_pos ⟨hp, by show p.val + (2 * r + k - p.val) = 2 * r + k; omega⟩, one_mul]
  · intro q _ hq
    have : q.val ≠ 2 * r + k - p.val := fun h => hq (Fin.ext h)
    rw [Hpk_apply', if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma HpkZero (p : Fin (2 * r + k + 1)) (hp : p.val < r) (j : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) :
    Formalism.QuantumDeterminants.Hpk k r p j = 0 := by
  rw [Hpk_apply', if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma ring_key {R : Type*} [Ring R] (D H g gs S : R) (hDD : D * D = D) (hDH : D * H = H * D)
    (hHg : gs * H * g = H) (hH1 : H * (1 - D) = S * H + H * S) (hSg : S * g * D = 0)
    (hgS : D * gs * S = 0) : (D * gs * D + (1 - D)) * H * (D * g * D + (1 - D)) = H := by
  have a1 : D * H * (1 - D) = 0 := by rw [hDH, mul_assoc, mul_sub, mul_one, hDD, sub_self, mul_zero]
  have a2 : (1 - D) * H * D = 0 := by
    rw [mul_assoc, ← hDH, ← mul_assoc, sub_mul, one_mul, hDD, sub_self, zero_mul]
  have a3 : D * H * D = H * D := by rw [hDH, mul_assoc, hDD]
  have a4 : (1 - D) * H * (1 - D) = H * (1 - D) := by
    have : (1 - D) * H * (1 - D) = H * (1 - D) - D * H * (1 - D) := by noncomm_ring
    rw [this, a1, sub_zero]
  have a5 : D * gs * H * D * g * D = H * D := by
    have e : D * gs * H * D * g * D = D * (gs * H * g) * D - D * gs * (H * (1 - D)) * g * D := by noncomm_ring
    rw [e, hHg, a3, hH1]
    have e2 : D * gs * (S * H + H * S) * g * D = (D * gs * S) * H * g * D + D * gs * H * (S * g * D) := by
      noncomm_ring
    rw [e2, hgS, hSg]; noncomm_ring
  calc (D * gs * D + (1 - D)) * H * (D * g * D + (1 - D))
      = D * gs * (D * H * D) * g * D + D * gs * (D * H * (1 - D)) + ((1 - D) * H * D) * g * D
          + (1 - D) * H * (1 - D) := by noncomm_ring
    _ = D * gs * H * D * g * D + H * (1 - D) := by rw [a3, a1, a2, a4]; noncomm_ring
    _ = H := by rw [a5]; noncomm_ring

def dW (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if r ≤ i.val ∧ i.val ≤ r + k then 1 else 0
def dS (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := fun i => if r + k < i.val then 1 else 0

def hW (g : Mk k r) : Mk k r := Matrix.of fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then g i j else if i = j then 1 else 0

lemma hW_eq (g : Mk k r) :
    hW g = diagonal (dW k r) * g * diagonal (dW k r) + (1 - diagonal (dW k r)) := by
  ext i j
  simp only [hW, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.one_apply, Matrix.diagonal_apply, dW]
  rcases eq_or_ne i j with rfl | hij
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> simp [hi]
  · by_cases hi : r ≤ i.val ∧ i.val ≤ r + k <;> by_cases hj : r ≤ j.val ∧ j.val ≤ r + k <;> simp [hi, hj, hij]

lemma diag_ct (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, star (d i) = d i) : (diagonal d)ᴴ = diagonal d := by
  rw [diagonal_conjTranspose]; congr 1; funext i; exact hd i

lemma dW_star (i : Fin (2 * r + k + 1)) : star (dW k r i) = dW k r i := by unfold dW; split_ifs <;> simp
lemma dS_star (i : Fin (2 * r + k + 1)) : star (dS k r i) = dS k r i := by unfold dS; split_ifs <;> simp

lemma fwd (g : Mk k r) (zH : Vk k r) (hg : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r)
    (hz : Formalism.QuantumDeterminants.inWb k r zH) (hI : InSstd g zH) : g ∈ Formalism.QuantumDeterminants.Sset k r zH := by
  have G1 : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (Formalism.QuantumDeterminants.eI k r a) = if i.val = a.val then 1 else 0 := by
    intro a i hi
    have := mem_supSub.1 (hI.1 a) i hi
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, stdX, colEntry, sub_eq_zero] at this
    rw [this, Formalism.QuantumDeterminants.bvec, Pi.single_apply]
    by_cases h : i.val = a.val
    · rw [if_pos (Fin.ext h), if_pos h]
    · rw [if_neg (fun e => h (congrArg Fin.val e)), if_neg h]
  have G2 : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (g *ᵥ zH) i = zH i := by
    intro i hi
    have := mem_supSub.1 hI.2 i hi
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at this
  have G3 : ∀ (a : ℕ) (ha : a < r) (j : Fin (2 * r + k + 1)), j.val ≤ r + k →
      g ⟨2 * r + k - a, by omega⟩ j = 0 := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a IH =>
      intro ha j hj
      have hh := congrFun (congrFun hg (Formalism.QuantumDeterminants.eI k r ⟨a, ha⟩)) j
      rw [HpkZero (Formalism.QuantumDeterminants.eI k r ⟨a, ha⟩) ha j hj, Matrix.mul_assoc, Matrix.mul_apply,
        Finset.sum_eq_single (Formalism.QuantumDeterminants.eI k r ⟨a, ha⟩)] at hh
      · rw [Matrix.conjTranspose_apply, G1 ⟨a, ha⟩ (Formalism.QuantumDeterminants.eI k r ⟨a, ha⟩) le_rfl,
          if_pos (show (Formalism.QuantumDeterminants.eI k r ⟨a, ha⟩).val = (⟨a, ha⟩ : Fin r).val from rfl), star_one, one_mul,
          HpkMul g _ ha j] at hh
        exact hh
      · intro p _ hp
        have hpv : p.val ≠ a := fun h => hp (Fin.ext h)
        rw [Matrix.conjTranspose_apply]
        by_cases hpa : a ≤ p.val
        · rw [G1 ⟨a, ha⟩ p hpa, if_neg (show ¬ p.val = (⟨a, ha⟩ : Fin r).val from hpv), star_zero, zero_mul]
        · rw [HpkMul g p (by omega) j, IH p.val (by omega) (by omega) j hj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  have G3' : ∀ i j : Fin (2 * r + k + 1), r + k < i.val → j.val ≤ r + k → g i j = 0 := by
    intro i j hi hj
    have e : i = ⟨2 * r + k - (2 * r + k - i.val), by omega⟩ :=
      Fin.ext (by have := i.isLt; show i.val = 2 * r + k - (2 * r + k - i.val); omega)
    rw [e]; exact G3 _ (by have := i.isLt; omega) j hj
  have hDD : diagonal (dW k r) * diagonal (dW k r) = diagonal (dW k r) := by
    rw [diagonal_mul_diagonal]; congr 1; funext i; unfold dW; split_ifs <;> simp
  have hDH : diagonal (dW k r) * Formalism.QuantumDeterminants.Hpk k r = Formalism.QuantumDeterminants.Hpk k r * diagonal (dW k r) := by
    ext i j
    rw [diagonal_mul, mul_diagonal, Hpk_apply']
    unfold dW
    split_ifs <;> first | (exfalso; omega) | simp
  have hH1 : Formalism.QuantumDeterminants.Hpk k r * (1 - diagonal (dW k r)) =
      diagonal (dS k r) * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * diagonal (dS k r) := by
    ext i j
    rw [mul_sub, mul_one, Matrix.sub_apply, Matrix.add_apply, mul_diagonal, diagonal_mul, mul_diagonal,
      Hpk_apply']
    unfold dW dS
    split_ifs <;> first | (exfalso; omega) | simp
  have hSg : diagonal (dS k r) * g * diagonal (dW k r) = 0 := by
    ext i j
    rw [mul_diagonal, diagonal_mul, Matrix.zero_apply]
    unfold dS dW
    split_ifs with h1 h2
    · rw [G3' i j h1 h2.2]; simp
    all_goals simp
  have hgS : diagonal (dW k r) * gᴴ * diagonal (dS k r) = 0 := by
    have := congrArg conjTranspose hSg
    rw [conjTranspose_mul, conjTranspose_mul, diag_ct _ dW_star, diag_ct _ dS_star, conjTranspose_zero,
      ← mul_assoc] at this
    exact this
  have hU : (hW g)ᴴ * Formalism.QuantumDeterminants.Hpk k r * hW g = Formalism.QuantumDeterminants.Hpk k r := by
    rw [hW_eq, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
      diag_ct _ dW_star, ← mul_assoc]
    exact ring_key _ _ _ _ _ hDD hDH hg hH1 hSg hgS
  have hX : ∀ b : Fin r, hW g *ᵥ stdX k r b = stdX k r b := by
    intro b; ext i
    rw [stdX, colEntry]
    simp only [hW, Matrix.of_apply]
    rw [if_neg (fun h => absurd h.2.1 (by show ¬ r ≤ b.val; have := b.isLt; omega)), Formalism.QuantumDeterminants.bvec,
      Pi.single_apply]
  have hSx : ∀ b : Fin r, hW g *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r b) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r b) := by
    intro b; ext i
    rw [colEntry]
    simp only [hW, Matrix.of_apply]
    rw [if_neg (fun h => absurd h.2.2 (by show ¬ 2 * r + k - b.val ≤ r + k; have := b.isLt; omega)),
      Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  have hZ : hW g *ᵥ zH = zH := by
    ext i
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · have G := G2 i hi.1
      simp only [Matrix.mulVec, dotProduct] at G ⊢
      rw [← G]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hW, Matrix.of_apply]
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · rw [if_pos ⟨hi, hj⟩]
      · rw [if_neg (fun h => hj h.2), hz j (by omega), mul_zero, mul_zero]
    · simp [Matrix.mulVec, dotProduct, hW, hi]
  obtain ⟨hinv, hinvDef⟩ : ∃ M : Mk k r, M = Formalism.QuantumDeterminants.Hpk k r * (hW g)ᴴ * Formalism.QuantumDeterminants.Hpk k r := ⟨_, rfl⟩
  have hih : hinv * hW g = 1 := by
    calc hinv * hW g = Formalism.QuantumDeterminants.Hpk k r * ((hW g)ᴴ * Formalism.QuantumDeterminants.Hpk k r * hW g) := by
          rw [hinvDef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hhi : hW g * hinv = 1 := mul_eq_one_comm.1 hih
  have hinvX : ∀ v ∈ supSub k r r, hinv *ᵥ v = v := by
    refine fixX hinv (fun b => ?_)
    conv_lhs => rw [← hX b]
    rw [Matrix.mulVec_mulVec, hih, Matrix.one_mulVec]
  have hinvU : hinvᴴ * Formalism.QuantumDeterminants.Hpk k r * hinv = Formalism.QuantumDeterminants.Hpk k r := by
    calc hinvᴴ * Formalism.QuantumDeterminants.Hpk k r * hinv = hinvᴴ * ((hW g)ᴴ * Formalism.QuantumDeterminants.Hpk k r * hW g) * hinv := by rw [hU]
      _ = (hW g * hinv)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (hW g * hinv) := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hhi, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmU : (hinv * g)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (hinv * g) = Formalism.QuantumDeterminants.Hpk k r := by
    calc (hinv * g)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (hinv * g) = gᴴ * (hinvᴴ * Formalism.QuantumDeterminants.Hpk k r * hinv) * g := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hinvU, hg]
  refine ⟨hW g, ⟨hU, fun a => ⟨hX a, hSx a⟩, hZ⟩, hinv * g, ⟨hmU, ?_, ?_⟩, ?_⟩
  · intro a i hai
    have hg1 : g *ᵥ stdX k r a ∈ supSub k r r := by
      rw [mem_supSub]; intro i' hi'
      rw [stdX, colEntry, G1 a i' (by have := a.isLt; omega), if_neg (by have := a.isLt; omega)]
    have := congrFun (show (hinv * g) *ᵥ stdX k r a = g *ᵥ stdX k r a by
      rw [← Matrix.mulVec_mulVec]; exact hinvX _ hg1) i
    rw [stdX, colEntry, colEntry] at this
    rw [this, G1 a i hai]
    by_cases hia : i.val = a.val
    · rw [if_pos hia, if_pos (Fin.ext hia)]
    · rw [if_neg hia, if_neg (fun h => hia (congrArg Fin.val h))]
  · intro i j hj1 hj2 hi
    have hx : g *ᵥ Formalism.QuantumDeterminants.bvec j - hW g *ᵥ Formalism.QuantumDeterminants.bvec j ∈ supSub k r r := by
      rw [mem_supSub]; intro i' hi'
      rw [Pi.sub_apply, colEntry, colEntry]
      simp only [hW, Matrix.of_apply]
      by_cases hw : r ≤ i'.val ∧ i'.val ≤ r + k
      · rw [if_pos ⟨hw, hj1, hj2⟩, sub_self]
      · rw [if_neg (fun h => hw h.1), if_neg (fun h => hw (by rw [h]; exact ⟨hj1, hj2⟩)), sub_zero,
          G3' i' j (by omega) hj2]
    have hm : (hinv * g) *ᵥ Formalism.QuantumDeterminants.bvec j =
        Formalism.QuantumDeterminants.bvec j + (g *ᵥ Formalism.QuantumDeterminants.bvec j - hW g *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      have e : g *ᵥ Formalism.QuantumDeterminants.bvec j =
          hW g *ᵥ Formalism.QuantumDeterminants.bvec j + (g *ᵥ Formalism.QuantumDeterminants.bvec j - hW g *ᵥ Formalism.QuantumDeterminants.bvec j) := by abel
      rw [← Matrix.mulVec_mulVec]
      conv_lhs => rw [e]
      rw [Matrix.mulVec_add, hinvX _ hx, Matrix.mulVec_mulVec, hih, Matrix.one_mulVec]
    have := congrFun hm i
    rw [colEntry, Pi.add_apply, mem_supSub.1 hx i hi, add_zero, Formalism.QuantumDeterminants.bvec, Pi.single_apply] at this
    exact this
  · rw [← Matrix.mul_assoc, hhi, Matrix.one_mul]

lemma bwd (s : Mk k r) (zH : Vk k r) (hz : Formalism.QuantumDeterminants.inWb k r zH) (hs : s ∈ Formalism.QuantumDeterminants.Sset k r zH) :
    InSstd s zH := by
  obtain ⟨h, ⟨_, hfix, hhz⟩, m, ⟨_, hm2, hm3⟩, rfl⟩ := hs
  have hfX : ∀ b, h *ᵥ stdX k r b = stdX k r b := fun b => (hfix b).1
  have hfixX := fixX h hfX
  constructor
  · intro a
    have hx : m *ᵥ stdX k r a - stdX k r a ∈ supSub k r a.1 := by
      rw [mem_supSub]; intro i hi
      rw [Pi.sub_apply, stdX, colEntry, hm2 a i hi, Formalism.QuantumDeterminants.bvec, Pi.single_apply, sub_self]
    have hms : h *ᵥ (m *ᵥ stdX k r a) = m *ᵥ stdX k r a := by
      have e : m *ᵥ stdX k r a = stdX k r a + (m *ᵥ stdX k r a - stdX k r a) := by abel
      rw [e, Matrix.mulVec_add, hfX a, hfixX _ (supSub_mono a.isLt.le hx)]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hms]
    exact hx
  · have hy : m *ᵥ zH - zH ∈ supSub k r r := by
      rw [mem_supSub]; intro i hi
      rw [Pi.sub_apply, sub_eq_zero]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · by_cases hw : i.val ≤ r + k
        · rw [hm3 i i hi hw hi, if_pos rfl, one_mul]
        · rw [hz i (Or.inr (by omega)), mul_zero]
      · intro j _ hji
        by_cases hjw : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hm3 i j hjw.1 hjw.2 hi, if_neg (Ne.symm hji), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hmz : h *ᵥ (m *ᵥ zH) = m *ᵥ zH := by
      have e : m *ᵥ zH = zH + (m *ᵥ zH - zH) := by abel
      rw [e, Matrix.mulVec_add, hhz, hfixX _ hy]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hmz]
    exact hy

lemma gUH {ε : Fin (2 * r + k + 1) → Bool} (P : Mk k r) (hPu : IsUnit P.det)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (U : Mk k r)
    (hu : Uᴴ * Formalism.REAL.Jm ε * U = Formalism.REAL.Jm ε) :
    (P⁻¹ * U * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * U * P) = Formalism.QuantumDeterminants.Hpk k r := by
  rw [← hP]
  have h1 : ∀ X : Mk k r, (P⁻¹)ᴴ * (Pᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ hPu, conjTranspose_one, Matrix.one_mul]
  have h2 : ∀ X : Mk k r, P * (P⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
  have h3 : ∀ X : Mk k r, Uᴴ * (Formalism.REAL.Jm ε * (U * X)) = Formalism.REAL.Jm ε * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hu]
  simp only [conjTranspose_mul, Matrix.mul_assoc, h1, h2, h3]

end SetCorrespondence

theorem setCorr_holds : SetCorr := by
  intro r k ε e z zH P hP hPu he hzW hzP _hT u
  have hE : e = fun a => P *ᵥ SetCorrespondence.stdX k r a := funext fun a => (he a).symm
  subst hE
  subst hzP
  have hu : (Formalism.MainNotions.S.uMat u)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat u = Formalism.REAL.Jm ε := u.2
  show Formalism.L2.SG.HidaSetting.InS _ _ (Formalism.MainNotions.S.uMat u) ↔ _
  rw [SetCorrespondence.inS_transport P hPu zH (Formalism.MainNotions.S.uMat u)]
  exact ⟨SetCorrespondence.fwd _ zH (SetCorrespondence.gUH P hPu hP (Formalism.MainNotions.S.uMat u) hu) hzW, SetCorrespondence.bwd _ zH hzW⟩

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
