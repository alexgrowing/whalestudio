import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.GermSumLattices

theorem finsum_if {α : Type} {P : α → Prop} {inst : DecidablePred P} (hfin : {x | P x}.Finite)
    (G : α → ℂ) : ∑ᶠ x, (if P x then G x else 0) = ∑ x ∈ hfin.toFinset, G x := by
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (by simpa using hx)]
  · intro x hx
    simp only [Function.mem_support] at hx
    by_contra h
    apply hx
    rw [if_neg]
    simpa using h

section Top

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem compact_mul_small {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ C, ∀ e ∈ E, z * e ∈ W := by
  obtain ⟨W', hW'W, hW'o, h0⟩ := mem_nhds_iff.1 hW
  have hn : IsOpen {p : K × K | p.1 * p.2 ∈ W'} := hW'o.preimage continuous_mul
  obtain ⟨u, v, hu, hv, hCu, h0v, huv⟩ :=
    generalized_tube_lemma hC (isCompact_singleton (x := (0 : K))) hn (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      have hb' : b = 0 := hb
      subst hb'
      simpa using h0)
  exact ⟨v, hv.mem_nhds (h0v rfl), fun z hz e he =>
    hW'W (huv (show ((z, e) : K × K) ∈ u ×ˢ v from ⟨hCu hz, he⟩))⟩

theorem lat_inf {L M : AddSubgroup K} (hL : IsLat L) (hM : IsOpen (M : Set K)) :
    IsLat (L ⊓ M) := by
  refine ⟨by rw [AddSubgroup.coe_inf]; exact hL.1.inter hM, ?_⟩
  rw [AddSubgroup.coe_inf]
  exact hL.2.inter_right (AddSubgroup.isClosed_of_isOpen M hM)

theorem exists_lat_le {ι : Type} (I : Finset ι) (M : ι → AddSubgroup K)
    (hM : ∀ i ∈ I, IsOpen (M i : Set K)) {Λ : AddSubgroup K} (hΛ : IsLat Λ) :
    ∃ Λ' : AddSubgroup K, IsLat Λ' ∧ Λ' ≤ Λ ∧ ∀ i ∈ I, Λ' ≤ M i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨Λ, hΛ, le_rfl, by simp⟩
  | insert a I ha ih =>
    obtain ⟨Λ', h1, h2, h3⟩ := ih (fun i hi => hM i (Finset.mem_insert_of_mem hi))
    refine ⟨Λ' ⊓ M a, lat_inf h1 (hM a (Finset.mem_insert_self _ _)), inf_le_left.trans h2, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact inf_le_right
    · exact inf_le_left.trans (h3 i hi)

theorem cut_finite (R : Subring K) (hRo : IsOpen (R : Set K)) {S : Set K} (hS : IsCompact S)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr) : {x | (cr x : K) ∈ S}.Finite := by
  have : DiscreteTopology (K ⧸ R.toAddSubgroup) := QuotientAddGroup.discreteTopology hRo
  have h1 : IsCompact ((QuotientAddGroup.mk : K → K ⧸ R.toAddSubgroup) '' S) :=
    hS.image QuotientAddGroup.continuous_mk
  refine h1.finite_of_discrete.subset ?_
  intro x hx
  exact ⟨cr x, hx, hcr x⟩

theorem cutSet_compact (m : ℕ) {Om : Set K} (hOm : IsCompact Om) (t : Kˣ) :
    IsCompact (cutSet m Om t) := by
  have h : cutSet m Om t = (fun z : K => ((((-t) ^ m)⁻¹ : Kˣ) : K) * z ^ (m + 1)) '' Om := by
    ext c
    constructor
    · rintro ⟨z, hz, hzc⟩
      refine ⟨z, hz, ?_⟩
      have : (-(t : K)) ^ m = (((-t) ^ m : Kˣ) : K) := by push_cast; rfl
      simp only
      rw [hzc, this, ← mul_assoc, Units.inv_mul, one_mul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, hz, ?_⟩
      have : (-(t : K)) ^ m = (((-t) ^ m : Kˣ) : K) := by push_cast; rfl
      rw [this, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h]
  exact hOm.image (by fun_prop)

end Top

section Alg

variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem germSum_eq (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (t c : Kˣ)
    (f : Kˣ → ℂ) : germSum R ψ m γ t c f =
      ((modK R (t : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ∑ z ∈ (hroots ((-t) ^ m * c)).toFinset, germCoef R ψ m γ t z * f z := by
  unfold germSum
  congr 1
  exact finsum_if (hroots ((-t) ^ m * c)) _

theorem roots_reindex (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite) (D z₀ : Kˣ) (hz₀ : z₀ ^ (m + 1) = D)
    (G : Kˣ → ℂ) : ∑ z ∈ (hroots D).toFinset, G z = ∑ ζ ∈ μ, G (ζ * z₀) := by
  symm
  apply Finset.sum_bij (fun ζ _ => ζ * z₀)
  · intro ζ hζ
    simp [mul_pow, (hμ ζ).1 hζ, hz₀]
  · intro a _ b _ hab
    exact mul_right_cancel hab
  · intro z hz
    have hz' : z ^ (m + 1) = D := by simpa using hz
    refine ⟨z * z₀⁻¹, (hμ _).2 ?_, by simp⟩
    rw [mul_pow, inv_pow, hz', hz₀, mul_inv_cancel]
  · intros
    rfl

theorem double_germ (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m) :
    uGram R ψ m cr S h h' t₁ t₂ =
      ((modK R ((t₁ : K) * (t₂ : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
      ((((modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ((modK R (t₂ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ)) *
      ∑ ζ ∈ μ, ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ (ζ * κ * z)) *
          Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z))) := by
  unfold uGram
  congr 1
  rw [finsum_if hSfin, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' : (cr x : K) ∈ S := by simpa using hx
  rw [hG1 x hx', germSum_eq R ψ m γ hroots, Finset.sum_comm, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hz' : z ^ (m + 1) = (-t₁) ^ m * cr x := by simpa using hz
  rw [hherm (pt2 h' m t₂ (cr x)) (addBlock h (m + 1) z), hG2 x hx', germSum_eq R ψ m γ hroots,
    map_mul, Complex.conj_ofReal, map_sum]
  have hz₀ : (κ * z) ^ (m + 1) = (-t₂) ^ m * cr x := by
    rw [mul_pow, hκ, hz', ← mul_assoc, ← mul_pow]
    congr 2
    rw [mul_neg, mul_assoc, inv_mul_cancel, mul_one]
  rw [roots_reindex m μ hμ hroots _ (κ * z) hz₀, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  rw [map_mul, ← hherm, mul_assoc ζ κ z]
  ring

end Alg

section Mod

variable {K : Type} [CommRing K] (R : Subring K)

def MM : Prop := ∀ x y : Kˣ,
  0 < modK R (x : K) ∧ modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K)

variable {R}

theorem mm_one (h : MM R) : modK R (1 : K) = 1 := by
  have h1 := h 1 1
  simp only [Units.val_one, mul_one] at h1
  exact (mul_right_cancel₀ h1.1.ne' (by rw [one_mul]; exact h1.2)).symm

theorem mm_pow (h : MM R) (z : Kˣ) (n : ℕ) : modK R ((z : K) ^ n) = modK R (z : K) ^ n := by
  induction n with
  | zero => simpa using mm_one h
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, ← Units.val_pow_eq_pow_val]
    exact (h (z ^ n) z).2

theorem mm_inv (h : MM R) (z : Kˣ) : modK R ((z⁻¹ : Kˣ) : K) = (modK R (z : K))⁻¹ := by
  have h1 := (h z z⁻¹).2
  rw [Units.mul_inv, mm_one h] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem mm_root (h : MM R) (z : Kˣ) (n : ℕ) (hz : modK R (z : K) ^ (n + 1) = 1) :
    modK R (z : K) = 1 :=
  (pow_eq_one_iff_of_nonneg (h z z).1.le (Nat.succ_ne_zero n)).1 hz

theorem mm_root_one (h : MM R) (z : Kˣ) (n : ℕ) (hz : z ^ (n + 1) = 1) : modK R (z : K) = 1 := by
  apply mm_root h z n
  rw [← mm_pow h, ← Units.val_pow_eq_pow_val, hz, Units.val_one, mm_one h]

theorem half_sq (A : ℝ) (hA : 0 < A) (m : ℕ) :
    A ^ ((m : ℝ) ^ 2 / 2) * A ^ ((m : ℝ) ^ 2 / 2) = A ^ (m ^ 2) := by
  rw [← Real.rpow_add hA, ← Real.rpow_natCast A (m ^ 2)]
  congr 1
  push_cast
  ring

theorem neg_half_sq (A : ℝ) (hA : 0 < A) (m : ℕ) :
    A ^ (-((m : ℝ) ^ 2) / 2) * A ^ (-((m : ℝ) ^ 2) / 2) = (A ^ (m ^ 2))⁻¹ := by
  rw [← Real.rpow_add hA, ← Real.rpow_natCast A (m ^ 2), ← Real.rpow_neg hA.le]
  congr 1
  push_cast
  ring

theorem inv_half_sq (A : ℝ) (hA : 0 < A) :
    A ^ (-(1 : ℝ) / 2) * A ^ (-(1 : ℝ) / 2) = A⁻¹ := by
  rw [← Real.rpow_add hA, ← Real.rpow_neg_one]
  congr 1
  norm_num

theorem tri_pow (A : ℝ) (m : ℕ) : (A * A) ^ (m * (m + 1) / 2) = A ^ (m ^ 2 + m) := by
  rw [← pow_two, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self m)]
  congr 1
  ring

variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem coef_mul (hMM : MM R) (hun : ∀ x : K, conj (ψ x) = ψ (-x))
    (hs : IsUnit ((m + 1 : ℕ) : K)) (t₁ t₂ z z' : Kˣ) (hN : modK R (z' : K) = modK R (z : K)) :
    germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ z') =
      γ (z * t₁) * conj (γ (z' * t₂)) *
        (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) *
        ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
          ((m + 1 : ℕ) : K) * (z' : K) * ((t₂⁻¹ : Kˣ) : K)) := by
  have hS : 0 < modK R ((m + 1 : ℕ) : K) := by
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact (hMM u u).1
  have key : ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
      modK R (z : K) ^ ((m : ℝ) ^ 2 / 2) : ℝ) : ℂ) *
      ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) * modK R (z : K) ^ ((m : ℝ) ^ 2 / 2) : ℝ) : ℂ) =
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← inv_half_sq _ hS, ← half_sq _ (hMM z z).1 m]
    ring
  unfold germCoef
  rw [map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ), Complex.conj_ofReal, hun, hN, sub_eq_add_neg, AddChar.map_add_eq_mul,
    ← key]
  ring

theorem nsK_unit (hMM : MM R) (h h' : Point K) (z : Kˣ) :
    NsK R ψ (m + 1) h h' (z : K) = ((modK R (z : K) ^ (m ^ 2 + m) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) z) := by
  unfold NsK
  rw [dif_pos z.isUnit, IsUnit.unit_of_val_units]
  unfold Ns
  rw [(hMM z z).2, Nat.add_sub_cancel, mul_comm (m + 1) m, tri_pow]

open Classical in

def amp (h h' : Point K) (t₁ ζ : Kˣ) (z : K) : ℂ :=
  if hz : IsUnit z then
    γ (hz.unit * t₁) * conj (γ (ζ * hz.unit * t₁)) *
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R z ^ (m ^ 2) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) hz.unit) (addBlock h' (m + 1) (ζ * hz.unit))
  else 0

theorem amp_unit (h h' : Point K) (t₁ ζ z : Kˣ) :
    amp R ψ m γ h h' t₁ ζ (z : K) = γ (z * t₁) * conj (γ (ζ * z * t₁)) *
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * z)) := by
  unfold amp
  rw [dif_pos z.isUnit, IsUnit.unit_of_val_units]

theorem amp_latInv (h h' : Point K) (t₁ ζ : Kˣ) (Om Esq : Set K) (Λ' Λ₁ Λ₂ : AddSubgroup K)
    (hγ2 : ∀ a b : Kˣ, γ (a * b ^ 2) = γ a)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hOmU : ∀ z ∈ Om, IsUnit z)
    (hML : ∀ z ∈ Om, ∀ l ∈ Λ', IsUnit (z + l) ∧ modK R (z + l) = modK R z ∧
      l * Ring.inverse z ∈ Esq)
    (hsq : ∀ a : Kˣ, (a : K) - 1 ∈ Esq → ∃ b : Kˣ, a = b ^ 2)
    (hLC1 : ∀ z z' : Kˣ, (z : K) ∈ Om → (z' : K) - (z : K) ∈ Λ₁ → ∀ w' : Point K,
      Kp R ψ (addBlock h (m + 1) z') w' = Kp R ψ (addBlock h (m + 1) z) w')
    (hLC2 : ∀ z z' : Kˣ, (z : K) ∈ Om → (z' : K) - (z : K) ∈ Λ₂ → ∀ w' : Point K,
      Kp R ψ (addBlock h' (m + 1) z') w' = Kp R ψ (addBlock h' (m + 1) z) w')
    (h1 : ∀ l ∈ Λ', l ∈ Λ₁) (h2 : ∀ l ∈ Λ', (ζ : K) * l ∈ Λ₂)
    (hζ : ∀ z ∈ Om, (ζ : K) * z ∈ Om) :
    LatInv Λ' Om (amp R ψ m γ h h' t₁ ζ) := by
  intro z hz l hl
  obtain ⟨u, rfl⟩ := hOmU z hz
  obtain ⟨hu', hmod, hE⟩ := hML _ hz l hl
  obtain ⟨u', hu'⟩ := hu'
  rw [← hu', amp_unit, amp_unit, hu', hmod]
  rw [Ring.inverse_unit] at hE
  obtain ⟨b, hb⟩ := hsq (u' * u⁻¹) (by
    rw [Units.val_mul, hu', add_mul, Units.mul_inv, add_sub_cancel_left]
    exact hE)
  have hub : u' = u * b ^ 2 := by rw [← hb]; simp
  have e1 : γ (u' * t₁) = γ (u * t₁) := by
    rw [hub, mul_right_comm, hγ2]
  have e2 : γ (ζ * u' * t₁) = γ (ζ * u * t₁) := by
    rw [hub, ← mul_assoc, mul_right_comm, hγ2]
  have e3 : Kp R ψ (addBlock h (m + 1) u') (addBlock h' (m + 1) (ζ * u')) =
      Kp R ψ (addBlock h (m + 1) u) (addBlock h' (m + 1) (ζ * u)) := by
    rw [hLC1 u u' hz (by rw [hu', add_sub_cancel_left]; exact h1 l hl), hherm,
      hLC2 (ζ * u) (ζ * u') (by rw [Units.val_mul]; exact hζ _ hz) (by
        rw [Units.val_mul, Units.val_mul, hu', mul_add, add_sub_cancel_left]
        exact h2 l hl), ← hherm]
  rw [e1, e2, e3]

theorem intLat_smul (Λ : AddSubgroup K) (Om : Set K) (F G : K → ℂ) (c : ℂ)
    (hF : ∀ z ∈ Om, F z = c * G z) : intLat R Λ Om F = c * intLat R Λ Om G := by
  unfold intLat
  rw [mul_left_comm]
  congr 1
  rw [← smul_eq_mul, smul_finsum]
  apply finsum_congr
  intro y
  split_ifs with hy
  · rw [hF _ hy, smul_eq_mul]
  · simp

end Mod

section Core

variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem back {cr : K ⧸ R.toAddSubgroup → Kˣ} {S : Set K} (t₁ : Kˣ)
    (hSfin : {x | (cr x : K) ∈ S}.Finite) (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    {i1 : DecidablePred fun x => (cr x : K) ∈ S}
    {i2 : ∀ x, DecidablePred fun z : Kˣ => z ^ (m + 1) = (-t₁) ^ m * cr x} (G : Kˣ → ℂ) :
    ∑ᶠ x, (if (cr x : K) ∈ S then
      ∑ᶠ z : Kˣ, (if z ^ (m + 1) = (-t₁) ^ m * cr x then G z else 0) else 0) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset, G z := by
  rw [finsum_if hSfin]
  apply Finset.sum_congr rfl
  intro x _
  exact finsum_if (hroots _) G

def f1 (h h' : Point K) (d : K) (z : K) : ℂ :=
  (((modK R ((m + 1 : ℕ) : K))⁻¹ * (modK R z ^ m)⁻¹ : ℝ) : ℂ) *
    (NsK R ψ (m + 1) h h' z * ψ (z * d))

open Classical in
theorem core2 (hMM : MM R) (hun : ∀ x : K, conj (ψ x) = ψ (-x)) (hψR : ∀ r ∈ R, ψ r = 1)
    (hs : IsUnit ((m + 1 : ℕ) : K)) (hγ1 : ∀ a, ‖γ a‖ = 1)
    (hγ2 : ∀ a b : Kˣ, γ (a * b ^ 2) = γ a)
    (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S Om : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m)
    (hT : modK R (t₂ : K) = modK R (t₁ : K))
    (b : Kˣ) (hb : κ * t₂ * t₁⁻¹ = b ^ 2)
    (hmem : ∀ x, (cr x : K) ∈ S → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * cr x → (z : K) ∈ Om)
    (hμOm : ∀ z ∈ Om, ∀ ζ ∈ μ, (ζ : K) * z ∈ Om)
    (hLCκ : ∀ z : Kˣ, (z : K) ∈ Om → ∀ w', Kp R ψ (addBlock h' (m + 1) (κ * z)) w' =
      Kp R ψ (addBlock h' (m + 1) z) w')
    (d : K) (hphase : ∀ z ∈ Om, ((m + 1 : ℕ) : K) * z * ((t₁⁻¹ : Kˣ) : K) -
      ((m + 1 : ℕ) : K) * ((κ : K) * z) * ((t₂⁻¹ : Kˣ) : K) - z * d ∈ R)
    (hX : ∀ ζ ∈ μ, ζ ≠ 1 → ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then
          amp R ψ m γ h h' t₁ ζ (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) else 0
        else 0) = 0)
    (I : ℂ)
    (hCV : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then f1 R ψ m h h' d (z : K) else 0
        else 0) =
      (((modK R (t₁ : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) : ℝ) : ℂ) *
        ((((modK R ((m + 1 : ℕ) : K))⁻¹ : ℝ) : ℂ) * I)) :
    uGram R ψ m cr S h h' t₁ t₂ = I := by
  have hS : 0 < modK R ((m + 1 : ℕ) : K) := by
    obtain ⟨u, hu⟩ := hs
    rw [← hu]
    exact (hMM u u).1
  have hTp : 0 < modK R (t₁ : K) := (hMM t₁ t₁).1
  have h1μ : (1 : Kˣ) ∈ μ := (hμ 1).2 (one_pow _)
  have hNκ : modK R (κ : K) = 1 := by
    apply mm_root hMM κ m
    rw [← mm_pow hMM, ← Units.val_pow_eq_pow_val, hκ, Units.val_pow_eq_pow_val, mm_pow hMM,
      Units.val_mul, (hMM _ _).2, mm_inv hMM, hT, mul_inv_cancel₀ hTp.ne', one_pow]
  rw [double_germ R ψ m γ h h' t₁ t₂ κ cr S μ hμ hSfin hroots hherm hG1 hG2 hκ]
  have hterm : ∀ ζ ∈ μ, ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ (ζ * κ * z)) *
          Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z)) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        amp R ψ m γ h h' t₁ ζ (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) := by
    intro ζ hζ
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro z hz
    have hzOm : (z : K) ∈ Om := hmem x (by simpa using hx) z (by simpa using hz)
    have hNζ : modK R (ζ : K) = 1 := mm_root_one hMM ζ m ((hμ ζ).1 hζ)
    have hN : modK R ((ζ * κ * z : Kˣ) : K) = modK R (z : K) := by
      rw [Units.val_mul, (hMM _ _).2, Units.val_mul, (hMM _ _).2, hNζ, hNκ, one_mul, one_mul]
    rw [coef_mul R ψ m γ hMM hun hs t₁ t₂ z (ζ * κ * z) hN, amp_unit]
    have e1 : γ (ζ * κ * z * t₂) = γ (ζ * z * t₁) := by
      have e : ζ * κ * z * t₂ = ζ * z * t₁ * b ^ 2 := by
        rw [← hb]
        have e' : ζ * z * t₁ * (κ * t₂ * t₁⁻¹) = ζ * κ * z * t₂ * (t₁ * t₁⁻¹) := by ac_rfl
        rw [e', mul_inv_cancel, mul_one]
      rw [e, hγ2]
    have e2 : Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z)) =
        Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * z)) := by
      rw [hherm, show ζ * κ * z = κ * (ζ * z) by ac_rfl,
        hLCκ (ζ * z) (by rw [Units.val_mul]; exact hμOm _ hzOm ζ hζ), ← hherm]
    rw [e1, e2]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem 1 h1μ (fun ζ hζ hne => by
    rw [← back R m t₁ hSfin hroots]
    exact hX ζ hζ hne)]
  have hdiag : ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        amp R ψ m γ h h' t₁ 1 (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * (((1 : Kˣ) : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) =
      ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        f1 R ψ m h h' d (z : K) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro z hz
    have hzOm : (z : K) ∈ Om := hmem x (by simpa using hx) z (by simpa using hz)
    have hNz : 0 < modK R (z : K) := (hMM z z).1
    rw [amp_unit, one_mul, Units.val_one, one_mul]
    have e1 : γ (z * t₁) * conj (γ (z * t₁)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hγ1]
      simp
    have e2 : ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
        ((m + 1 : ℕ) : K) * ((κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) = ψ ((z : K) * d) := by
      have e := hψR _ (hphase _ hzOm)
      rw [← sub_add_cancel (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
        ((m + 1 : ℕ) : K) * ((κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) ((z : K) * d),
        AddChar.map_add_eq_mul, e, one_mul]
    have e3 : (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) =
        (((modK R ((m + 1 : ℕ) : K))⁻¹ * (modK R (z : K) ^ m)⁻¹ : ℝ) : ℂ) *
          ((modK R (z : K) ^ (m ^ 2 + m) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [pow_add]
      field_simp
    rw [e1, e2, f1, nsK_unit R ψ m hMM, e3]
    ring
  rw [hdiag, ← back R m t₁ hSfin hroots, hCV, (hMM t₁ t₂).2, hT]
  have hP : (modK R (t₁ : K) * modK R (t₁ : K)) ^ (m * (m + 1) / 2) *
      (modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2) * modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2)) *
      ((modK R (t₁ : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K)) * (modK R ((m + 1 : ℕ) : K))⁻¹ = 1 := by
    rw [tri_pow, neg_half_sq _ hTp, pow_add]
    field_simp
  have hP' := congrArg (fun r : ℝ => (r : ℂ)) hP
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at hP' ⊢
  linear_combination I * hP'

end Core

section Cut

variable {K : Type} [CommRing K]

theorem cut_Q (m : ℕ) (Om : Set K) (t c : Kˣ) (hc : (c : K) ∈ cutSet m Om t) :
    (c : K) * (t : K) ^ m ∈ (fun z : K => (-1) ^ m * z ^ (m + 1)) '' Om := by
  obtain ⟨z, hz, hzc⟩ := hc
  refine ⟨z, hz, ?_⟩
  simp only
  rw [hzc, neg_pow (t : K) m]
  have h1 : ((-1 : K) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  linear_combination ((t : K) ^ m * c) * h1

theorem cut_mem [TopologicalSpace K] (m : ℕ) (Om : Set K) (hOm : IsOmega (m + 1) Om) (t c z : Kˣ)
    (hc : (c : K) ∈ cutSet m Om t) (hz : z ^ (m + 1) = (-t) ^ m * c) : (z : K) ∈ Om := by
  obtain ⟨z₀, hz₀, hzc⟩ := hc
  obtain ⟨u, rfl⟩ := hOm.2.2.1 z₀ hz₀
  have h1 : ((z * u⁻¹ : Kˣ) : K) ^ (m + 1) = 1 := by
    have h2 : (z * u⁻¹) ^ (m + 1) = 1 := by
      have hu : u ^ (m + 1) = (-t) ^ m * c := Units.ext (by push_cast; exact hzc)
      rw [mul_pow, inv_pow, hz, hu, mul_inv_cancel]
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have h3 := hOm.2.2.2 u hz₀ _ h1
  simpa using h3

theorem shift_ratio (t t₁ t₂ : Kˣ) (σ σ' : K) (h1 : IsShift t t₁ σ) (h2 : IsShift t t₂ σ') :
    ((t₂ * t₁⁻¹ : Kˣ) : K) = 1 + (σ - σ') * (t₂ : K) := by
  unfold IsShift at h1 h2
  have h3 : (t₂ : K) * ((t₂⁻¹ : Kˣ) : K) = 1 := Units.mul_inv t₂
  rw [Units.val_mul, h1]
  rw [h2] at h3
  linear_combination h3

end Cut

end Formalism.FourierDecayAlt.P.GermSumLattices

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.GermSumLattices

theorem germIdentityOfSteps : Formalism.FourierDecayAlt.A6.GermIdentityAssemble := by
  intro hGH hGK hKH hA2 hMMp hRF hSU hSS hCS hRC hSN hPD hLC hML hIR hCV hXV K _ _ _ R ψ hD hn m hm
    n₀ F hF Om Sg Λ hOm hΛ hOmΛ hNs hψ
  classical
  have iA := hD.artin
  have iR := hD.red
  obtain ⟨γ, hγ⟩ := hGH K R ψ hD hn m
  have hMM : MM R := hMMp K R ψ hD
  have hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w') := hKH K R ψ
  have hψR : ∀ r ∈ R, ψ r = 1 := by
    intro r hr
    have h1 := (hD.selfDual 1).2 R.one_mem r hr
    rwa [one_mul] at h1
  have hs : IsUnit ((m + 1 : ℕ) : K) := hn (m + 1) (Nat.succ_ne_zero m)
  have hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite := hRF K (m + 1) (by omega)
  obtain ⟨μ, hμ⟩ : ∃ μ : Finset Kˣ, ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1 :=
    ⟨(hroots 1).toFinset, fun ζ => by simp⟩
  have h1μ : (1 : Kˣ) ∈ μ := (hμ 1).2 (one_pow _)
  have hOmc : IsCompact Om := hOm.2.1
  have hOmU : ∀ z ∈ Om, IsUnit z := hOm.2.2.1
  have hμOm : ∀ z ∈ Om, ∀ ζ ∈ μ, (ζ : K) * z ∈ Om := by
    intro z hz ζ hζ
    refine hOm.2.2.2 z hz ζ ?_
    rw [← Units.val_pow_eq_pow_val, (hμ ζ).1 hζ, Units.val_one]

  obtain ⟨Q, hQdef⟩ : ∃ Q : Set K, Q = (fun z : K => (-1) ^ m * z ^ (m + 1)) '' Om := ⟨_, rfl⟩
  have hQc : IsCompact Q := by
    rw [hQdef]
    exact hOmc.image (by fun_prop)
  have hQu : ∀ d ∈ Q, IsUnit d := by
    rw [hQdef]
    rintro _ ⟨z, hz, rfl⟩
    exact ((isUnit_one.neg).pow m).mul ((hOmU z hz).pow _)

  choose VG hVG hVG' using fun h : Point K => hGK K R ψ hD hn m hm γ hγ h Q hQc hQu
  choose ΛL hΛL hΛL' using fun h : Point K =>
    hLC K R ψ hD hn (m + 1) h Om (by omega) hOmc hOmU
  obtain ⟨Esq, hEsq, hsq⟩ := hSN K R ψ hD hn
  obtain ⟨ΛM, hΛM, hΛM'⟩ := hML K R ψ hD hn Om hOmc hOmU Esq hEsq

  obtain ⟨Λ', hΛ'lat, hΛ'le, hΛ'M⟩ := exists_lat_le (F ×ˢ μ)
    (fun p => (ΛL p.1).comap (AddMonoidHom.mulLeft (p.2 : K)))
    (fun p _ => (hΛL p.1).1.preimage (continuous_const.mul continuous_id))
    (lat_inf hΛ hΛM.1)
  have hΛ'Λ : Λ' ≤ Λ := hΛ'le.trans inf_le_left
  have hΛ'ΛM : Λ' ≤ ΛM := hΛ'le.trans inf_le_right
  have hΛ'ζ : ∀ h ∈ F, ∀ ζ ∈ μ, ∀ l ∈ Λ', (ζ : K) * l ∈ ΛL h := by
    intro h hh ζ hζ l hl
    exact hΛ'M (h, ζ) (Finset.mem_product.2 ⟨hh, hζ⟩) hl
  have hΛ'1 : ∀ h ∈ F, ∀ l ∈ Λ', l ∈ ΛL h := by
    intro h hh l hl
    have h1 := hΛ'ζ h hh 1 h1μ l hl
    rwa [Units.val_one, one_mul] at h1
  have hst : ∀ z ∈ Om, ∀ l ∈ Λ', z + l ∈ Om := fun z hz l hl => hOmΛ z hz l (hΛ'Λ hl)
  have hML' : ∀ z ∈ Om, ∀ l ∈ Λ', IsUnit (z + l) ∧ modK R (z + l) = modK R z ∧
      l * Ring.inverse z ∈ Esq := fun z hz l hl => hΛM' z hz l (hΛ'ΛM hl)
  obtain ⟨VCV, hVCV, hCV'⟩ := hCV K R ψ hD hn m hm Om Λ' hOm hΛ'lat hst
    (fun z hz l hl => (hML' z hz l hl).2.1)
  choose EX hEX VX hVX hXX using fun (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1) (h2 : ζ ≠ 1) =>
    hXV K R ψ hD hn m hm Om Λ' Sg ζ hOm hΛ'lat hst h1 h2
  obtain ⟨EXs, hEXs, hEXs'⟩ : ∃ E ∈ 𝓝 (0 : K), ∀ x ∈ E, ∀ (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1)
      (h2 : ζ ≠ 1), x ∈ EX ζ h1 h2 := by
    refine ⟨⋂ ζ ∈ μ, (if hh : ζ ^ (m + 1) = 1 ∧ ζ ≠ 1 then EX ζ hh.1 hh.2 else Set.univ),
      (Filter.biInter_finset_mem μ).2 (fun ζ _ => ?_), ?_⟩
    · split_ifs with hh
      · exact hEX ζ hh.1 hh.2
      · exact Filter.univ_mem
    · intro x hx ζ h1 h2
      have h3 := Set.mem_iInter₂.1 hx ζ ((hμ ζ).2 h1)
      rwa [dif_pos ⟨h1, h2⟩] at h3
  obtain ⟨VXs, hVXs, hVXs'⟩ : ∃ E ∈ 𝓝 (0 : K), ∀ x ∈ E, ∀ (ζ : Kˣ) (h1 : ζ ^ (m + 1) = 1)
      (h2 : ζ ≠ 1), x ∈ VX ζ h1 h2 := by
    refine ⟨⋂ ζ ∈ μ, (if hh : ζ ^ (m + 1) = 1 ∧ ζ ≠ 1 then VX ζ hh.1 hh.2 else Set.univ),
      (Filter.biInter_finset_mem μ).2 (fun ζ _ => ?_), ?_⟩
    · split_ifs with hh
      · exact hVX ζ hh.1 hh.2
      · exact Filter.univ_mem
    · intro x hx ζ h1 h2
      have h3 := Set.mem_iInter₂.1 hx ζ ((hμ ζ).2 h1)
      rwa [dif_pos ⟨h1, h2⟩] at h3
  obtain ⟨EP, hEP, VP, hVP, hP⟩ := hPD K R ψ hD hn m Om Sg hOmc
  obtain ⟨ELC, hELC, hELC'⟩ := compact_mul_small hOmc (hΛ'lat.1.mem_nhds Λ'.zero_mem)

  obtain ⟨E1, hE1, W1, hW1, hEW⟩ : ∃ E1 ∈ 𝓝 (0 : K), ∃ W1 ∈ 𝓝 (0 : K), ∀ a ∈ E1, ∀ b ∈ W1,
      a * (1 + b) + b ∈ Esq := by
    have hc : Continuous (fun p : K × K => p.1 * (1 + p.2) + p.2) := by fun_prop
    have ht : Tendsto (fun p : K × K => p.1 * (1 + p.2) + p.2) (𝓝 ((0 : K), (0 : K)))
        (𝓝 (0 : K)) := by
      simpa using hc.tendsto ((0 : K), (0 : K))
    have h1 := ht hEsq
    rw [nhds_prod_eq] at h1
    obtain ⟨E1, hE1, W1, hW1, hsub⟩ := Filter.mem_prod_iff.1 h1
    exact ⟨E1, hE1, W1, hW1, fun a ha b hb => hsub (show ((a, b) : K × K) ∈ E1 ×ˢ W1 from ⟨ha, hb⟩)⟩
  obtain ⟨W2, hW2, hW2'⟩ := compact_mul_small
    (C := (((Sg ×ˢ Sg).image (fun p : K × K => p.1 - p.2) : Finset K) : Set K))
    (Finset.finite_toSet _).isCompact hW1
  obtain ⟨VR, hVR, hR⟩ := hRC K R ψ hD hn m Sg (EP ∩ ELC ∩ E1 ∩ EXs)
    (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hEP hELC) hE1) hEXs)
  obtain ⟨VS, hVS, hS⟩ := hSS K R ψ hD hn Sg ((⋂ h ∈ F, VG h) ∩ VCV ∩ W2)
    (Filter.inter_mem (Filter.inter_mem ((Filter.biInter_finset_mem F).2 fun h _ => hVG h) hVCV)
      hW2)
  obtain ⟨VU, hVU, hU⟩ := hSU K R ψ hD hn Sg
  obtain ⟨VC, hVC, hC⟩ := hCS K R ψ hD hn m hm Om Sg hOm
  refine ⟨VS ∩ VU ∩ VC ∩ VR ∩ VP ∩ VXs, Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
    (Filter.inter_mem (Filter.inter_mem hVS hVU) hVC) hVR) hVP) hVXs, ?_⟩
  rintro t t₁ t₂ cr ⟨⟨⟨⟨⟨htS, htU⟩, htC⟩, htR⟩, htP⟩, htX⟩ hcr σ hσ σ' hσ' hsh1 hsh2 h hh h' hh'
  obtain ⟨κ, hκ, ⟨⟨⟨hκP, hκLC⟩, hκ1⟩, hκX⟩⟩ := hR t t₁ t₂ htR σ hσ σ' hσ' hsh1 hsh2
  obtain ⟨⟨ht1G, ht1CV⟩, -⟩ := hS t t₁ htS σ hσ hsh1
  obtain ⟨⟨ht2G, -⟩, ht2W⟩ := hS t t₂ htS σ' hσ' hsh2
  have hcut1 : cutSet m Om t₁ = cutSet m Om t := (hC t htC).1 σ hσ t₁ hsh1
  have hcut2 : cutSet m Om t₂ = cutSet m Om t := (hC t htC).1 σ' hσ' t₂ hsh2
  have hSfin : {x | (cr x : K) ∈ cutSet m Om t}.Finite :=
    cut_finite R hD.isOpen (cutSet_compact m hOmc t) cr hcr
  have hmod : ∀ (t' : Kˣ) (τ : K), τ ∈ Sg → IsShift t t' τ → modK R (t' : K) = modK R (t : K) := by
    intro t' τ hτ hsh
    have h1 := (hU t htU τ hτ).2
    rw [← hsh, mm_inv hMM, mm_inv hMM] at h1
    exact inv_injective h1
  obtain ⟨b, hb⟩ := hsq (κ * t₂ * t₁⁻¹) (by
    have h1 := hEW _ hκ1 _ (hW2' (σ - σ') (by
      rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨(σ, σ'), Finset.mem_product.2 ⟨hσ, hσ'⟩, rfl⟩) _ ht2W)
    have h2 := shift_ratio t t₁ t₂ σ σ' hsh1 hsh2
    have h3 : ((κ * t₂ * t₁⁻¹ : Kˣ) : K) - 1 =
        ((κ : K) - 1) * (1 + (σ - σ') * (t₂ : K)) + (σ - σ') * (t₂ : K) := by
      rw [mul_assoc, Units.val_mul, h2]
      ring
    rw [h3]
    exact h1)
  have hGinv : LatInv Λ Om (fun z => NsK R ψ (m + 1) h h' z * ψ (z * (σ - σ'))) := by
    intro z hz l hl
    simp only
    rw [hNs h hh h' hh' z hz l hl, add_mul, AddChar.map_add_eq_mul, hψ σ hσ σ' hσ' l hl, mul_one]
  refine core2 R ψ m γ hMM hD.unitary hψR hs hγ.1 hγ.2.1 h h' t₁ t₂ κ cr (cutSet m Om t) Om μ hμ
    hSfin hroots hherm ?_ ?_ hκ ((hmod t₂ σ' hσ' hsh2).trans (hmod t₁ σ hσ hsh1).symm) b hb ?_ hμOm
    ?_ (σ - σ') (hP t t₁ t₂ κ htP σ hσ σ' hσ' hsh1 hsh2 hκ hκP) ?_ _ ?_
  · intro x hx w'
    refine hVG' h t₁ (cr x) (Set.mem_iInter₂.1 ht1G h hh) ?_ w'
    rw [hQdef]
    exact cut_Q m Om t₁ (cr x) (hcut1 ▸ hx)
  · intro x hx w'
    refine hVG' h' t₂ (cr x) (Set.mem_iInter₂.1 ht2G h' hh') ?_ w'
    rw [hQdef]
    exact cut_Q m Om t₂ (cr x) (hcut2 ▸ hx)
  · intro x hx z hz
    exact cut_mem m Om hOm t₁ (cr x) z (hcut1 ▸ hx) hz
  · intro z hz w'
    refine hΛL' h' z (κ * z) hz ?_ w'
    have h1 := hΛ'1 h' hh' _ (hELC' _ hz _ hκLC)
    have h2 : ((κ * z : Kˣ) : K) - (z : K) = (z : K) * ((κ : K) - 1) := by
      rw [Units.val_mul]
      ring
    rw [h2]
    exact h1
  · intro ζ hζ hne
    have hζ1 := (hμ ζ).1 hζ
    refine hXX ζ hζ1 hne t t₁ t₂ κ cr (amp R ψ m γ h h' t₁ ζ) (hVXs' _ htX ζ hζ1 hne) σ hσ σ' hσ'
      hsh1 hsh2 hκ (hEXs' _ hκX ζ hζ1 hne) hcr ?_ ?_
    · exact amp_latInv R ψ m γ h h' t₁ ζ Om Esq Λ' (ΛL h) (ΛL h') hγ.2.1 hherm hOmU hML' hsq
        (hΛL' h) (hΛL' h') (hΛ'1 h hh) (hΛ'ζ h' hh' ζ hζ) (fun z hz => hμOm z hz ζ hζ)
    · intro z _ hne0
      rw [amp_unit] at hne0
      refine hA2 K R ψ hD (m + 1) (by omega) h h' z (ζ * z) ((hF h hh).trans (hF h' hh').symm) ?_
      unfold Ns
      refine mul_ne_zero ?_ (right_ne_zero_of_mul hne0)
      rw [(hMM z (ζ * z)).2]
      exact_mod_cast (pow_pos (mul_pos (hMM z z).1 (hMM (ζ * z) z).1) _).ne'
  · have hf1 : LatInv Λ' Om (f1 R ψ m h h' (σ - σ')) := by
      intro z hz l hl
      unfold f1
      rw [(hML' z hz l hl).2.1]
      congr 1
      exact hGinv z hz l (hΛ'Λ hl)
    have h1 := hCV' t₁ cr (f1 R ψ m h h' (σ - σ')) ht1CV hcr hf1
    rw [hcut1] at h1
    rw [h1]
    congr 1
    rw [← hIR K R ψ hD Λ Λ' Om _ hΛ hΛ'lat hΛ'Λ hOmc hOmΛ hGinv]
    apply intLat_smul
    intro z hz
    obtain ⟨u, rfl⟩ := hOmU z hz
    have hNz : 0 < modK R (u : K) := (hMM u u).1
    unfold f1
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp

end Formalism.FourierDecayAlt.P
