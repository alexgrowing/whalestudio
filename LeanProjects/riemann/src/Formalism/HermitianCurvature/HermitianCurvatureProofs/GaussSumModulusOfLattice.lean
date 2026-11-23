import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelNonzeroModulusDeterminantEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem phase_critical_points : Formalism.FourierDecayAlt.A6.CritPoints := by
  intro K _ m hm D' x
  constructor
  · intro h
    obtain ⟨k0⟩ : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hx : ∀ k, x k = x k0 := by
      intro k
      have := (h k).trans (h k0).symm
      exact mul_right_cancel this
    refine ⟨x k0, hx, ?_⟩
    have := h k0
    rw [Finset.prod_congr rfl (fun j _ => hx j)] at this
    simpa [pow_succ, mul_comm] using this
  · rintro ⟨z, hz, hD⟩ k
    rw [Finset.prod_congr rfl (fun j _ => hz j), hz k]
    simpa [pow_succ, mul_comm] using hD

theorem phase_critical_value : Formalism.FourierDecayAlt.A6.CritValue := by
  intro K _ m z
  unfold g0
  simp only [Finset.sum_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : Ring.inverse ((z : K) ^ m) = ((z⁻¹ : Kˣ) : K) ^ m := by
    rw [← Units.val_pow_eq_pow_val, Ring.inverse_unit, ← Units.val_pow_eq_pow_val, inv_pow]
  rw [this, pow_succ, mul_assoc, mul_comm (z : K), ← mul_assoc, ← mul_pow]
  simp [add_mul]

theorem phase_hessian_determinant : Formalism.FourierDecayAlt.A6.HessDet := by
  intro K _ m a
  unfold hessM
  rw [Matrix.det_smul, Fintype.card_fin]
  have : (1 + Matrix.of fun _ _ => (1 : K) : Matrix (Fin m) (Fin m) K) =
      1 + Matrix.replicateCol Unit (fun _ => (1:K)) * Matrix.replicateRow Unit (fun _ => (1:K)) := by
    ext i j; simp [Matrix.mul_apply]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [dotProduct, mul_comm, add_comm]

namespace A6x6

section Jet

open MvPolynomial

variable {m : ℕ}

theorem X_mem (k : Fin m) : (X k : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ :=
  Ideal.subset_span ⟨k, rfl⟩

theorem e_mem (s : Finset (Fin m)) :
    (∑ k ∈ s, X k : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ :=
  Ideal.sum_mem _ fun k _ => X_mem k

theorem p_mem (s : Finset (Fin m)) :
    (∑ k ∈ s, X k ^ 2 : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ ^ 2 :=
  Ideal.sum_mem _ fun k _ => Ideal.pow_mem_pow (X_mem k) 2

theorem two_half : (2 : MvPolynomial (Fin m) ℚ) * C (1 / 2 : ℚ) = 1 := by
  have : (2 : MvPolynomial (Fin m) ℚ) = C 2 := (map_ofNat C 2).symm
  rw [this, ← C_mul]; norm_num

theorem prod_jet (s : Finset (Fin m)) :
    (∏ k ∈ s, (1 + X k) - (1 + ∑ k ∈ s, X k + C (1 / 2 : ℚ) *
      ((∑ k ∈ s, X k) ^ 2 - ∑ k ∈ s, X k ^ 2)) : MvPolynomial (Fin m) ℚ) ∈
      idealOfVars (Fin m) ℚ ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : (X a * (C (1 / 2 : ℚ) * ((∑ k ∈ s, X k) ^ 2 - ∑ k ∈ s, X k ^ 2)) :
        MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ ^ 3 := by
      rw [pow_succ' _ 2]
      exact Ideal.mul_mem_mul (X_mem a)
        (Ideal.mul_mem_left _ _ (Ideal.sub_mem _ (Ideal.pow_mem_pow (e_mem s) 2) (p_mem s)))
    have h2 := Ideal.add_mem _ (Ideal.mul_mem_left _ (1 + X a) ih) h1
    convert h2 using 1
    linear_combination (-((∑ k ∈ s, X k) * X a)) * (two_half (m := m))

end Jet

open Formalism.FourierDecayAlt.P.A5x5

section Abs

theorem gauss_abs {H : Type} [AddCommGroup H] [Fintype H] (F : H → ℂ) (B : H → H → ℂ)
    (hF : ∀ y w, F (y + w) = F y * F w * B y w)
    (hn : ∀ y, F y * conj (F y) = 1)
    (hB : ∀ w y y', B (y + y') w = B y w * B y' w)
    (hB0 : ∀ w, B 0 w = 1)
    (h1 : ∀ w, (∀ y, B y w = 1) → F w = 1) :
    (∑ y, F y) * conj (∑ y, F y) =
      (Nat.card H : ℂ) * (Nat.card {w : H // ∀ y, B y w = 1} : ℂ) := by
  classical
  have hχ : ∀ w, ∑ z, B z w = if ∀ y, B y w = 1 then (Fintype.card H : ℂ) else 0 := by
    intro w
    let χ : AddChar H ℂ := ⟨fun y => B y w, hB0 w, hB w⟩
    have h := AddChar.sum_eq_ite χ
    have e : χ = 0 ↔ ∀ y, B y w = 1 := by
      rw [DFunLike.ext_iff]; rfl
    simp only [e] at h
    exact h
  calc (∑ y, F y) * conj (∑ y, F y) = ∑ z, ∑ y, F y * conj (F z) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.sum_comm]
    _ = ∑ z, ∑ w, F (z + w) * conj (F z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        exact (Fintype.sum_equiv (Equiv.addLeft z) _ _ fun w => rfl).symm
    _ = ∑ z, ∑ w, F w * B z w := by
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun w _ => ?_
        rw [hF]; linear_combination (F w * B z w) * hn z
    _ = ∑ w, F w * ∑ z, B z w := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ w, if ∀ y, B y w = 1 then (Fintype.card H : ℂ) else 0 := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hχ]; split_ifs with h
        · rw [h1 w h, one_mul]
        · simp
    _ = _ := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
          Nat.card_eq_fintype_card, Fintype.card_subtype, mul_comm]

end Abs

section Pi

variable {K : Type} [CommRing K] {m : ℕ}

def PL (L : AddSubgroup K) (m : ℕ) : AddSubgroup (Fin m → K) :=
  AddSubgroup.pi Set.univ (fun _ => L)

theorem mem_PL {L : AddSubgroup K} {v : Fin m → K} : v ∈ PL L m ↔ ∀ i, v i ∈ L := by
  simp [PL, AddSubgroup.mem_pi]

def prj (Λ : AddSubgroup K) (m : ℕ) : (Fin m → K) →+ (Fin m → K ⧸ Λ) :=
  (QuotientAddGroup.mk' Λ).compLeft (Fin m)

theorem prj_apply (Λ : AddSubgroup K) (x : Fin m → K) (i : Fin m) :
    prj Λ m x i = (x i : K ⧸ Λ) := rfl

theorem ker_prj (Λ : AddSubgroup K) : (prj Λ m).ker = PL Λ m := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_PL, funext_iff]
  exact forall_congr' fun i => by
    rw [prj_apply, Pi.zero_apply, QuotientAddGroup.eq_zero_iff]

def sec (Λ : AddSubgroup K) (y : Fin m → K ⧸ Λ) : Fin m → K := fun i => Quotient.out (y i)

theorem prj_sec (Λ : AddSubgroup K) (y : Fin m → K ⧸ Λ) : prj Λ m (sec Λ y) = y := by
  funext i
  exact Quotient.out_eq' (y i)

theorem sec_prj_sub (Λ : AddSubgroup K) (x : Fin m → K) : sec Λ (prj Λ m x) - x ∈ PL Λ m := by
  rw [← ker_prj, AddMonoidHom.mem_ker, map_sub, prj_sec, sub_self]

theorem relIndex_PL (Λ L : AddSubgroup K) :
    (PL Λ m).relIndex (PL L m) = Λ.relIndex L ^ m := by
  have e : ∀ y : Fin m → K ⧸ Λ, y ∈ (PL L m).map (prj Λ m) ↔
      ∀ i, y i ∈ L.map (QuotientAddGroup.mk' Λ) := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      exact ⟨x i, mem_PL.1 hx i, rfl⟩
    · intro h
      choose x hx hxy using h
      exact ⟨x, mem_PL.2 hx, funext hxy⟩
  rw [← ker_prj, AddSubgroup.relIndex_ker]
  have h2 : Λ.relIndex L = Nat.card (L.map (QuotientAddGroup.mk' Λ)) := by
    conv_lhs => rw [← QuotientAddGroup.ker_mk' Λ]
    exact AddSubgroup.relIndex_ker _ _
  rw [h2]
  have := Nat.card_congr ((Equiv.subtypeEquivRight e).trans
    (Equiv.subtypePiEquivPi (p := fun (_ : Fin m) (b : K ⧸ Λ) => b ∈ L.map (QuotientAddGroup.mk' Λ))))
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at this
  exact this

theorem relIndex_eq_card (Λ : AddSubgroup K) (N : AddSubgroup (Fin m → K)) :
    (PL Λ m).relIndex N = Nat.card (N.map (prj Λ m)) := by
  have h := AddSubgroup.relIndex_ker (K := N) (prj Λ m)
  rwa [ker_prj] at h

theorem gi_PL (A B : AddSubgroup K) : gi (PL A m) (PL B m) = gi A B ^ m := by
  unfold gi
  rw [relIndex_PL, relIndex_PL, div_pow]
  push_cast
  rfl

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem lat_PL {L : AddSubgroup K} (hL : IsLat L) : Lat (PL L m) := by
  have e : ((PL L m : AddSubgroup (Fin m → K)) : Set (Fin m → K)) =
      Set.pi Set.univ (fun _ => (L : Set K)) := by
    ext v; simp [mem_PL]
  constructor
  · rw [e]; exact isOpen_set_pi Set.finite_univ (fun _ _ => hL.1)
  · rw [e]; exact isCompact_univ_pi (fun _ => hL.2)

end Pi

section Main

variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)

theorem psi_ne_zero (x : K) : ψ x ≠ 0 := by
  intro h
  have h1 := AddChar.map_add_eq_mul ψ x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

theorem dot_perp {L : AddSubgroup K} {x u : Fin m → K} (hx : x ∈ PL L m)
    (hu : u ∈ PL (perp ψ L) m) : ψ (x ⬝ᵥ u) = 1 := by
  unfold dotProduct
  refine Finset.sum_induction _ (fun a => ψ a = 1)
    (fun a b ha hb => by rw [AddChar.map_add_eq_mul, ha, hb, one_mul])
    (AddChar.map_zero_eq_one ψ) fun i _ => ?_
  rw [mul_comm]
  exact mem_PL.1 hu i _ (mem_PL.1 hx i)

theorem mem_perp_of_dot {L : AddSubgroup K} {v : Fin m → K}
    (h : ∀ x ∈ PL L m, ψ (x ⬝ᵥ v) = 1) : v ∈ PL (perp ψ L) m := by
  classical
  rw [mem_PL]
  intro i l hl
  have h1 := h (Pi.single i l) (mem_PL.2 fun j => by
    by_cases hj : j = i
    · subst hj; simpa using hl
    · simp [hj])
  rwa [single_dotProduct, mul_comm] at h1

variable {M : Matrix (Fin m) (Fin m) K}

theorem symm_dot (hM : M.IsSymm) (x y : Fin m → K) : y ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ y := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

theorem q_add (hM : M.IsSymm) (x y : Fin m → K) :
    (x + y) ⬝ᵥ M *ᵥ (x + y) = x ⬝ᵥ M *ᵥ x + y ⬝ᵥ M *ᵥ y + 2 * (x ⬝ᵥ M *ᵥ y) := by
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, symm_dot hM x y]
  ring

theorem psi_q_add (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (x y : Fin m → K) :
    ψ (Ring.inverse 2 * ((x + y) ⬝ᵥ M *ᵥ (x + y))) =
      ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) * ψ (Ring.inverse 2 * (y ⬝ᵥ M *ᵥ y)) *
        ψ (x ⬝ᵥ M *ᵥ y) := by
  have h := Ring.inverse_mul_cancel 2 h2
  have e : Ring.inverse 2 * ((x + y) ⬝ᵥ M *ᵥ (x + y)) =
      Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x) + Ring.inverse 2 * (y ⬝ᵥ M *ᵥ y) + x ⬝ᵥ M *ᵥ y := by
    rw [q_add hM]; linear_combination (x ⬝ᵥ M *ᵥ y) * h
  rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]

variable {L Λ : AddSubgroup K}

theorem gaussF_of_mem {x : Fin m → K} (hx : x ∈ PL L m) :
    gaussF ψ L M x = ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) := by
  unfold gaussF; rw [if_pos (mem_PL.1 hx)]

theorem gaussF_of_not_mem {x : Fin m → K} (hx : x ∉ PL L m) : gaussF ψ L M x = 0 := by
  unfold gaussF; rw [if_neg (fun h => hx (mem_PL.2 h))]

variable {ψ}

theorem PL_le (hInv : LatInvN Λ (gaussF ψ L M)) : PL Λ m ≤ PL L m := by
  intro l hl
  by_contra h
  have h1 := hInv 0 l (mem_PL.1 hl)
  rw [zero_add, gaussF_of_not_mem ψ h, gaussF_of_mem ψ (PL L m).zero_mem] at h1
  exact psi_ne_zero ψ _ h1.symm

theorem q_inv (hInv : LatInvN Λ (gaussF ψ L M)) {x l : Fin m → K} (hx : x ∈ PL L m)
    (hl : l ∈ PL Λ m) :
    ψ (Ring.inverse 2 * ((x + l) ⬝ᵥ M *ᵥ (x + l))) = ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) := by
  have h1 := hInv x l (mem_PL.1 hl)
  rwa [gaussF_of_mem ψ hx, gaussF_of_mem ψ ((PL L m).add_mem hx (PL_le hInv hl))] at h1

theorem b_one (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x l : Fin m → K} (hx : x ∈ PL L m) (hl : l ∈ PL Λ m) : ψ (x ⬝ᵥ M *ᵥ l) = 1 := by
  have h1 := q_inv hInv hx hl
  have h0 := q_inv hInv (PL L m).zero_mem hl
  rw [zero_add] at h0
  rw [psi_q_add ψ h2 hM, h0] at h1
  simp only [mulVec_zero, dotProduct_zero, mul_zero, AddChar.map_zero_eq_one, mul_one] at h1
  exact mul_left_cancel₀ (psi_ne_zero ψ _) (h1.trans (mul_one _).symm)

theorem cq (hInv : LatInvN Λ (gaussF ψ L M)) {x x' : Fin m → K} (hx : x' ∈ PL L m)
    (hl : x - x' ∈ PL Λ m) :
    ψ (Ring.inverse 2 * (x ⬝ᵥ M *ᵥ x)) = ψ (Ring.inverse 2 * (x' ⬝ᵥ M *ᵥ x')) := by
  have := q_inv hInv hx hl
  rwa [add_sub_cancel] at this

theorem cb2 (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x x' u : Fin m → K} (hu : u ∈ PL L m) (hl : x - x' ∈ PL Λ m) :
    ψ (u ⬝ᵥ M *ᵥ x) = ψ (u ⬝ᵥ M *ᵥ x') := by
  have e : x = x' + (x - x') := by abel
  rw [e, mulVec_add, dotProduct_add, AddChar.map_add_eq_mul, b_one h2 hM hInv hu hl, mul_one]

theorem cb1 (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    {x x' u : Fin m → K} (hu : u ∈ PL L m) (hl : x - x' ∈ PL Λ m) :
    ψ (x ⬝ᵥ M *ᵥ u) = ψ (x' ⬝ᵥ M *ᵥ u) := by
  rw [symm_dot hM u x, symm_dot hM u x', cb2 h2 hM hInv hu hl]

theorem sec_mem (hle : PL Λ m ≤ PL L m) {y : Fin m → K ⧸ Λ} (hy : y ∈ (PL L m).map (prj Λ m)) :
    sec Λ y ∈ PL L m := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := (PL L m).add_mem (hle (sec_prj_sub Λ x)) hx
  rwa [sub_add_cancel] at this

theorem sec_add (y w : Fin m → K ⧸ Λ) : sec Λ (y + w) - (sec Λ y + sec Λ w) ∈ PL Λ m := by
  rw [← ker_prj, AddMonoidHom.mem_ker, map_sub, map_add, prj_sec, prj_sec, prj_sec, sub_self]

theorem sec_zero : sec Λ (0 : Fin m → K ⧸ Λ) ∈ PL Λ m := by
  rw [← ker_prj, AddMonoidHom.mem_ker, prj_sec]

theorem inv_mem (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hAdm : GaussAdm ψ L M) {u : Fin m → K}
    (hu : u ∈ PL (perp ψ L) m) : M⁻¹ *ᵥ u ∈ PL (perp ψ (perp ψ L)) m := by
  apply mem_perp_of_dot
  intro x hx
  have hMi : (M⁻¹).IsSymm := hM.inv
  have h1 := hAdm (x + u) (mem_PL.1 ((PL _ m).add_mem hx hu))
  rw [psi_q_add ψ h2 hMi, hAdm x (mem_PL.1 hx), hAdm u (mem_PL.1 hu), one_mul, one_mul] at h1
  exact h1

theorem normSq_sum (h2 : IsUnit (2 : K)) (hM : M.IsSymm) (hInv : LatInvN Λ (gaussF ψ L M))
    (hu : ∀ x : K, conj (ψ x) = ψ (-x)) (hdet : IsUnit M.det)
    (hAdm : GaussAdm ψ L M) (hPP : perp ψ (perp ψ L) = L)
    (hfin : (PL Λ m).relIndex (PL L m) ≠ 0) :
    (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) *
        conj (∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)) =
      ((PL Λ m).relIndex (PL L m) : ℂ) *
        ((PL Λ m).relIndex ((PL (perp ψ L) m).map (mv M⁻¹)) : ℂ) := by
  classical
  have hle := PL_le hInv
  have hcard : Nat.card ((PL L m).map (prj Λ m)) = (PL Λ m).relIndex (PL L m) :=
    (relIndex_eq_card _ _).symm
  have : Finite ((PL L m).map (prj Λ m)) := Nat.finite_of_card_ne_zero (hcard ▸ hfin)
  have : Fintype ((PL L m).map (prj Λ m)) := Fintype.ofFinite _
  let F : (PL L m).map (prj Λ m) → ℂ :=
    fun y => ψ (Ring.inverse 2 * (sec Λ y.1 ⬝ᵥ M *ᵥ sec Λ y.1))
  let B : (PL L m).map (prj Λ m) → (PL L m).map (prj Λ m) → ℂ :=
    fun y w => ψ (sec Λ y.1 ⬝ᵥ M *ᵥ sec Λ w.1)
  have hS : ∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y) = ∑ y, F y := by
    rw [finsum_eq_sum_of_support_subset (s := (Finset.univ : Finset ((PL L m).map (prj Λ m))).map
      ⟨Subtype.val, Subtype.val_injective⟩)]
    · rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun y _ => gaussF_of_mem ψ (sec_mem hle y.2)
    · intro y hy
      by_contra h
      apply hy
      apply gaussF_of_not_mem
      intro hs
      apply h
      simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ, Set.image_univ,
        Subtype.range_coe_subtype]
      exact ⟨_, hs, prj_sec _ _⟩

  have hrad : ∀ w : (PL L m).map (prj Λ m), (∀ y, B y w = 1) → M *ᵥ sec Λ w.1 ∈ PL (perp ψ L) m := by
    intro w hw
    apply mem_perp_of_dot
    intro x hx
    have := hw ⟨prj Λ m x, x, hx, rfl⟩
    rw [← this]
    exact (cb1 h2 hM hInv (sec_mem hle w.2) (sec_prj_sub Λ x)).symm
  rw [hS, gauss_abs F B, hcard]
  · congr 2
    rw [relIndex_eq_card]
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeExists _ _).trans
      (Equiv.subtypeEquivRight fun y => ?_))
    constructor
    · rintro ⟨hy, hw⟩
      refine ⟨sec Λ y, ⟨M *ᵥ sec Λ y, hrad ⟨y, hy⟩ hw, ?_⟩, prj_sec _ _⟩
      simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
    · rintro ⟨_, ⟨u, hu', rfl⟩, rfl⟩
      have hx : M⁻¹ *ᵥ u ∈ PL L m := by
        have := inv_mem h2 hM hAdm hu'
        rwa [hPP] at this
      refine ⟨⟨_, hx, rfl⟩, fun y' => ?_⟩
      show ψ (sec Λ y'.1 ⬝ᵥ M *ᵥ sec Λ (prj Λ m (mv M⁻¹ u))) = 1
      rw [cb2 h2 hM hInv (sec_mem hle y'.2) (sec_prj_sub Λ _), mv_apply, mulVec_mulVec,
        mul_nonsing_inv _ hdet, one_mulVec]
      exact dot_perp ψ (sec_mem hle y'.2) hu'
  · intro y w
    show ψ _ = ψ _ * ψ _ * ψ _
    rw [← psi_q_add ψ h2 hM]
    exact cq hInv ((PL L m).add_mem (sec_mem hle y.2) (sec_mem hle w.2)) (sec_add _ _)
  · intro y
    show ψ _ * conj (ψ _) = 1
    rw [hu, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  · intro w y y'
    show ψ _ = ψ _ * ψ _
    rw [← AddChar.map_add_eq_mul, ← add_dotProduct]
    exact cb1 h2 hM hInv (sec_mem hle w.2) (sec_add _ _)
  · intro w
    show ψ _ = 1
    rw [symm_dot hM]
    exact b_one h2 hM hInv (sec_mem hle w.2) sec_zero
  · intro w hw
    have h1 := hAdm _ (mem_PL.1 (hrad w hw))
    rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, dotProduct_comm] at h1
    exact h1

end Main

section Final

theorem gi_of_ge {V : Type} [AddCommGroup V] {A B : AddSubgroup V} (h : B ≤ A) :
    gi A B = (B.relIndex A : ℝ) := by
  rw [gi, AddSubgroup.relIndex_eq_one.2 h]; simp

theorem rpow_of_sq {x X : ℝ} (hx : 0 < x) (hX : 0 ≤ X) (h : X ^ 2 * x = 1) :
    X = x ^ (-(1 : ℝ) / 2) := by
  have h1 : (x ^ (-(1 : ℝ) / 2)) ^ 2 = x⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    exact Real.rpow_neg_one x
  have h2 : X ^ 2 = (x ^ (-(1 : ℝ) / 2)) ^ 2 := by
    rw [h1]; field_simp; exact h
  exact (pow_left_inj₀ hX (Real.rpow_nonneg hx.le _) (by norm_num)).1 h2

theorem gaussModulus_of (hPL : PerpLat) : GaussModulus := by
  intro K _ _ _ R ψ hd hn m M hM hdet L Λ hL hΛ hAdm hInv
  obtain ⟨hP, hPP, hvol⟩ := hPL K R ψ hd hn L hL
  have h2 : IsUnit (2 : K) := by simpa using hn 2 (by norm_num)
  have lΛ : Lat (PL Λ m) := lat_PL hΛ
  have lL : Lat (PL L m) := lat_PL hL
  have lP : Lat (PL (perp ψ L) m) := lat_PL hP
  have lR : Lat (LL R (Fin m)) := lat_LL hd.isOpen hd.isCompact
  have hdi : IsUnit (M⁻¹).det := Matrix.isUnit_nonsing_inv_det M hdet
  have lN : Lat ((PL (perp ψ L) m).map (mv M⁻¹)) := lat_map hdi lP
  have hfin := relIndex_ne_zero lΛ.op lL.cp
  have hS := normSq_sum h2 hM hInv hd.unitary hdet hAdm hPP hfin
  have hle := PL_le hInv
  have hleN : PL Λ m ≤ (PL (perp ψ L) m).map (mv M⁻¹) := by
    intro l hl
    refine ⟨M *ᵥ l, mem_perp_of_dot ψ fun x hx => b_one h2 hM hInv hx hl, ?_⟩
    simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hS
  have hS' : ‖∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)‖ ^ 2 =
      gi (PL L m) (PL Λ m) * gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) := by
    rw [gi_of_ge hle, gi_of_ge hleN]; exact_mod_cast hS
  have hv : volL R Λ ^ m = gi (PL Λ m) (LL R (Fin m)) := (gi_PL Λ R.toAddSubgroup).symm
  have hv0 : 0 ≤ volL R Λ := by unfold volL; positivity
  have e1 : gi (PL L m) (PL Λ m) * volL R Λ ^ m = volL R L ^ m := by
    rw [hv, gi_trans lL lΛ lR]; exact gi_PL L R.toAddSubgroup
  have e2 : gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) * volL R Λ ^ m =
      volL R (perp ψ L) ^ m * modK R (M⁻¹).det := by
    rw [hv, gi_trans lN lΛ lR, ← gi_trans lN (lat_map hdi lR) lR, gi_map (mv_injective hdi)]
    congr 1
    · exact gi_PL (perp ψ L) R.toAddSubgroup
    · exact good_fin hd m M⁻¹ hdi
  have e3 : modK R (M⁻¹).det * modK R M.det = 1 := by
    rw [← modK_mul' hd hdi hdet, ← det_mul, nonsing_inv_mul _ hdet, det_one, modK_one]
  have hpos : 0 < modK R M.det := by
    have := modK_pos hd.isOpen hd.isCompact hdet.unit
    simpa using this
  apply rpow_of_sq hpos (norm_nonneg _)
  show ‖(volL R Λ : ℂ) ^ m * ∑ᶠ y : Fin m → K ⧸ Λ, gaussF ψ L M (sec Λ y)‖ ^ 2 * _ = 1
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hv0, mul_pow, hS']
  calc (volL R Λ ^ m) ^ 2 * (gi (PL L m) (PL Λ m) *
        gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m)) * modK R M.det
      = (gi (PL L m) (PL Λ m) * volL R Λ ^ m) *
        (gi ((PL (perp ψ L) m).map (mv M⁻¹)) (PL Λ m) * volL R Λ ^ m) * modK R M.det := by ring
    _ = (volL R L * volL R (perp ψ L)) ^ m * (modK R (M⁻¹).det * modK R M.det) := by
        rw [e1, e2]; ring
    _ = 1 := by rw [hvol, e3]; simp

end Final

end A6x6

theorem hessian_jet_formula : Formalism.FourierDecayAlt.A6.HessianJet := by
  intro m d hd
  have key : ((∏ k : Fin m, (1 + MvPolynomial.X k)) *
      (1 - ∑ k : Fin m, MvPolynomial.X k + MvPolynomial.C (1 / 2 : ℚ) *
        (∑ k : Fin m, MvPolynomial.X k ^ 2 + (∑ k : Fin m, MvPolynomial.X k) ^ 2)) -
      1 : MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
    have hD := A6x6.prod_jet (m := m) Finset.univ
    have he := A6x6.e_mem (m := m) Finset.univ
    have hp := A6x6.p_mem (m := m) Finset.univ
    have he2 := Ideal.pow_mem_pow he 2
    have h1 : ((∑ k : Fin m, MvPolynomial.X k) * ∑ k : Fin m, MvPolynomial.X k ^ 2 :
        MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
      rw [pow_succ' _ 2]; exact Ideal.mul_mem_mul he hp
    have h2 : (((∑ k : Fin m, MvPolynomial.X k) ^ 2 - ∑ k : Fin m, MvPolynomial.X k ^ 2) *
        ((∑ k : Fin m, MvPolynomial.X k) ^ 2 + ∑ k : Fin m, MvPolynomial.X k ^ 2) :
        MvPolynomial (Fin m) ℚ) ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 3 := by
      have : _ ∈ MvPolynomial.idealOfVars (Fin m) ℚ ^ 2 * MvPolynomial.idealOfVars (Fin m) ℚ ^ 2 :=
        Ideal.mul_mem_mul (Ideal.sub_mem _ he2 hp) (Ideal.add_mem _ he2 hp)
      rw [← pow_add] at this
      exact Ideal.pow_le_pow_right (by norm_num) this
    have h3 := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right
      (1 - ∑ k : Fin m, MvPolynomial.X k + MvPolynomial.C (1 / 2 : ℚ) *
        (∑ k : Fin m, MvPolynomial.X k ^ 2 + (∑ k : Fin m, MvPolynomial.X k) ^ 2)) _ hD) h1)
      (Ideal.mul_mem_left _ (MvPolynomial.C (1 / 2 : ℚ) ^ 2) h2)
    convert h3 using 1
    linear_combination ((∑ k : Fin m, MvPolynomial.X k) ^ 2 +
      (∑ k : Fin m, MvPolynomial.X k) * ∑ k : Fin m, MvPolynomial.X k ^ 2) *
      (A6x6.two_half (m := m))
  exact (MvPolynomial.mem_pow_idealOfVars_iff 3 _).1 key d hd

theorem gauss_sum_modulus_of_lattice : Formalism.FourierDecayAlt.A6.GaussModulus :=
  A6x6.gaussModulus_of orthogonal_lattice_properties

end Formalism.FourierDecayAlt.P
