import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebra
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriSubOnePow
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount

section Gen
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem coeff_one_mul_comm (a b : MonoidAlgebra K G) : (a * b).coeff 1 = (b * a).coeff 1 := by
  rw [Formalism.L2.DIV.coeff_mul_fin, Formalism.L2.DIV.coeff_mul_fin]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun s => by simp [mul_comm])

open Classical in

theorem coeff_lvlIdem_eq (P : Subgroup G) (ψ : P →* Kˣ) (t : G) :
    (Formalism.L2.DIV.lvlIdem P ψ).coeff t =
      if h : t ∈ P then (Nat.card P : K)⁻¹ * ((ψ (⟨t, h⟩ : P)⁻¹ : Kˣ) : K) else 0 := by
  unfold Formalism.L2.DIV.lvlIdem
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  split_ifs with ht
  · rw [Finset.sum_eq_single (⟨t, ht⟩ : P)]
    · simp
    · intro b _ hb
      rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
      intro h; exact hb (Subtype.ext h.symm)
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
    intro h; exact ht (h ▸ b.2)

end Gen

theorem coeff_one_real_of_idem {H : Type} [Group H] [Finite H] (a : MonoidAlgebra ℂ H) (ha : a * a = a) :
    (((a.coeff 1).re : ℝ) : ℂ) = a.coeff 1 := by
  have h := finrank_range_mulLeft_idem ℂ H a ha
  have hc : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have e : a.coeff 1 = (((finrank ℂ (LinearMap.range (LinearMap.mulLeft ℂ a)) : ℝ) / (Nat.card H : ℝ) : ℝ) : ℂ) := by
    push_cast
    rw [h, mul_div_cancel_left₀ _ hc]
  rw [e, Complex.ofReal_re]

theorem isUniUp_one {A : Type} [Zero A] [One A] {N : ℕ} : IsUniUp (1 : Matrix (Fin N) (Fin N) A) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => h ▸ Matrix.one_apply_eq a⟩

theorem sd_one {A : Type} [AddCommMonoid A] [One A] {N : ℕ} :
    ∑ i ∈ Finset.range (N - 1), entN (1 : Matrix (Fin N) (Fin N) A) i (i + 1) = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  unfold entN
  split_ifs with h
  · exact Matrix.one_apply_ne (by intro e; simp [Fin.ext_iff] at e)
  · rfl

variable (D : D7)

open Classical in
theorem coeff_badElt (k : Fin 2) (S : Finset (Tup D k)) (g : G0g D.nd) :
    (badElt D k S).coeff g = if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → g kv = 1 then
      ∑ t ∈ S, ∏ v : D.nd.PlG k, (D.ntypes.eSer k (t v)).coeff (g ⟨k, v⟩) else 0 := by
  unfold badElt
  rfl

end GlobalTheory.BadCount

namespace GlobalTheory.BadCount

abbrev sdg {A : Type} [AddCommMonoid A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) : A :=
  ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)

open Classical in

theorem coeff_eU (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) (x : GL (Fin N) (ZMod g)) :
    (eU g N ψ₀).coeff x =
      if IsUniUp (x : Matrix (Fin N) (Fin N) (ZMod g)) then
        ((Finset.univ.filter fun u : GL (Fin N) (ZMod g) => IsUniUp (u : Matrix (Fin N) (Fin N) (ZMod g))).card : ℂ)⁻¹ *
          (ψ₀ (sdg (x : Matrix (Fin N) (Fin N) (ZMod g))))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, Finsupp.smul_apply, Finset.sum_apply']
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, smul_eq_mul]
  split_ifs <;> simp

variable (D : D7)

def extAt (k : Fin 2) (z : ∀ v : D.nd.PlG k, GL (Fin D.R.r) (ZMod (D.host.g k))) : G0g D.nd :=
  fun kv => if h : kv.1 = k then
    (Eq.rec (motive := fun k' _ => ∀ v : D.nd.PlG k', GL (Fin D.R.r) (ZMod (D.host.g k'))) z h.symm) kv.2 else 1

theorem extAt_apply (k : Fin 2) (z : ∀ v : D.nd.PlG k, GL (Fin D.R.r) (ZMod (D.host.g k))) (v : D.nd.PlG k) :
    extAt D k z ⟨k, v⟩ = z v := by
  simp [extAt]

theorem extAt_apply_ne (k : Fin 2) (z : ∀ v : D.nd.PlG k, GL (Fin D.R.r) (ZMod (D.host.g k)))
    (kv : Σ k : Fin 2, D.nd.PlG k) (h : kv.1 ≠ k) : extAt D k z kv = 1 := by
  simp [extAt, h]

theorem extAt_restr (k : Fin 2) (y : G0g D.nd) (hy : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → y kv = 1) :
    extAt D k (fun v => y ⟨k, v⟩) = y := by
  funext ⟨k', v⟩
  by_cases h : k' = k
  · subst h
    exact extAt_apply D _ _ v
  · rw [extAt_apply_ne D k _ _ h, hy ⟨k', v⟩ h]

open Classical in

theorem sum_trivOff [Fintype (G0g D.nd)] (k : Fin 2) [Fintype (∀ v : D.nd.PlG k, GL (Fin D.R.r) (ZMod (D.host.g k)))]
    (F : (∀ v : D.nd.PlG k, GL (Fin D.R.r) (ZMod (D.host.g k))) → ℂ) :
    ∑ y : G0g D.nd, (if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → y kv = 1 then F (fun v => y ⟨k, v⟩) else 0) =
      ∑ z, F z := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun y v => y ⟨k, v⟩) (extAt D k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun kv h => extAt_apply_ne D k z kv h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact extAt_restr D k y hy
  · intro z _
    funext v
    exact extAt_apply D k z v
  · intro y _
    rfl

end GlobalTheory.BadCount

namespace GlobalTheory.BadCount

open Polynomial

variable (D : D7)

def phiAt (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (f : (ZMod (D.host.g k))[X])
    (u : GL (Fin D.R.r) (ZMod (D.host.g k))) : ℂ := by
  classical
  exact if IsUniUp (u : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) then
    (ψ₀ (sdg (u : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))))⁻¹ * (D.ntypes.eSer k f).coeff u⁻¹ else 0

open Classical in

def cardU (k : Fin 2) : ℂ :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  ((Finset.univ.filter fun u : GL (Fin D.R.r) (ZMod (D.host.g k)) =>
    IsUniUp (u : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))).card : ℂ)

theorem cardU_ne_zero (k : Fin 2) : cardU D k ≠ 0 := by
  classical
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  unfold cardU
  refine Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, ?_⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.val_one]
  exact isUniUp_one

open Classical in
theorem coeff_eUk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (x : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    (eUk D k ψ₀).coeff x = if IsUniUp (x : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) then
      (cardU D k)⁻¹ * (ψ₀ (sdg (x : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))))⁻¹ else 0 := by
  classical
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  unfold eUk cardU
  rw [coeff_eU]

theorem sum_phiAt (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (f : (ZMod (D.host.g k))[X])
    [Fintype (GL (Fin D.R.r) (ZMod (D.host.g k)))] :
    ∑ u, phiAt D k ψ₀ f u = cardU D k * (eUk D k ψ₀ * D.ntypes.eSer k f).coeff 1 := by
  classical
  rw [Formalism.L2.DIV.coeff_mul_fin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coeff_eUk, phiAt, mul_one]
  split_ifs
  · rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (cardU_ne_zero D k), one_mul]
  · simp

theorem eUk_mul_eSer_idem (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (f : (ZMod (D.host.g k))[X]) :
    (eUk D k ψ₀ * D.ntypes.eSer k f) * (eUk D k ψ₀ * D.ntypes.eSer k f) = eUk D k ψ₀ * D.ntypes.eSer k f := by
  have ha := (GlobalTheory.RowLev.LevelIdem.eUk_eJk_spec D k ψ₀ _ (Or.inl rfl)).1
  rw [mul_assoc, D.ntypes.eSer_central k f (eUk D k ψ₀ * D.ntypes.eSer k f), mul_assoc, D.ntypes.eSer_idem,
    ← mul_assoc, ha]

theorem wtOf_eUk (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) (f : (ZMod (D.host.g k))[X]) :
    ((wtOf D k (eUk D k ψ₀) f : ℝ) : ℂ) = cardU D k * (eUk D k ψ₀ * D.ntypes.eSer k f).coeff 1 := by
  classical
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  have h1 : (eUk D k ψ₀).coeff 1 = (cardU D k)⁻¹ := by
    rw [coeff_eUk, if_pos (by simpa using isUniUp_one), Units.val_one, sdg, sd_one, AddChar.map_zero_eq_one, inv_one,
      mul_one]
  have hr := coeff_one_real_of_idem _ (eUk_mul_eSer_idem D k ψ₀ f)
  obtain ⟨n, hn, -⟩ : ∃ n : ℕ, cardU D k = n ∧ n ≠ 0 := ⟨_, rfl, fun h => cardU_ne_zero D k (by
    unfold cardU at *; exact_mod_cast h)⟩
  unfold wtOf
  rw [h1, hn, show ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  push_cast
  rw [hr, div_inv_eq_mul, mul_comm]

end GlobalTheory.BadCount

namespace GlobalTheory.BadCount

open Polynomial

variable (D : D7)

open Classical in

theorem term_eq [Fintype (G0g D.nd)] (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ)
    (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (hW : IsWhit D P lam ψ)
    (k : Fin 2) (S : Finset (Tup D k)) (y : G0g D.nd) :
    (Formalism.L2.DIV.lvlIdem P lam).coeff y * (badElt D k S).coeff (y⁻¹ * 1) =
      if ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → y kv = 1 then
        (Nat.card P : ℂ)⁻¹ * ∑ t ∈ S, ∏ v : D.nd.PlG k, phiAt D k (ψ ⟨k, v⟩) (t v) (y ⟨k, v⟩) else 0 := by
  have hTi : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → (y⁻¹ * 1) kv = 1) ↔
      (∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → y kv = 1) := by
    simp only [mul_one, Pi.inv_apply, inv_eq_one]
  rw [coeff_badElt]
  by_cases hT : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kv.1 ≠ k → y kv = 1
  · rw [if_pos hT, if_pos (hTi.2 hT), coeff_lvlIdem_eq]
    split_ifs with hP
    · have hu : ∀ v : D.nd.PlG k, IsUniUp ((y ⟨k, v⟩ : GL (Fin D.R.r) (ZMod (D.host.g k))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) := fun v => (hW.2.1 y).1 hP ⟨k, v⟩
      have hlam : ((lam (⟨y, hP⟩ : P)⁻¹ : ℂˣ) : ℂ) =
          ∏ v : D.nd.PlG k, (ψ ⟨k, v⟩ (sdg ((y ⟨k, v⟩ : GL (Fin D.R.r) (ZMod (D.host.g k))) :
            Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))))⁻¹ := by
        rw [map_inv, Units.val_inv_eq_inv_val, hW.2.2, ← Finset.prod_inv_distrib, Fintype.prod_sigma,
          Fintype.prod_eq_single k]
        intro k' hk'
        refine Finset.prod_eq_one fun v _ => ?_
        have e1 : ((⟨y, hP⟩ : P) : G0g D.nd) ⟨k', v⟩ = 1 := hT ⟨k', v⟩ hk'
        rw [e1, Units.val_one, sd_one, AddChar.map_zero_eq_one, inv_one]
      rw [hlam, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [phiAt, if_pos (hu v)]
      simp only [mul_one, Pi.inv_apply]
    · rw [zero_mul]
      obtain ⟨v, hv⟩ : ∃ v : D.nd.PlG k, ¬ IsUniUp ((y ⟨k, v⟩ : GL (Fin D.R.r) (ZMod (D.host.g k))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) := by
        by_contra hc
        push_neg at hc
        apply hP
        rw [hW.2.1]
        rintro ⟨k', v⟩
        by_cases h : k' = k
        · subst h
          exact hc v
        · rw [hT ⟨k', v⟩ h, Units.val_one]
          exact isUniUp_one
      refine (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun t _ => ?_)).symm
      refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
      rw [phiAt, if_neg hv]
  · rw [if_neg hT, if_neg (fun h => hT (hTi.1 h)), mul_zero]

theorem badElt_mul_lvlIdem : ∀ (D : D7) [Fintype (G0g D.nd)] (P : Subgroup (G0g D.nd)) (lam : P →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D P lam ψ → ∀ (k : Fin 2) (S : Finset (Tup D k)) (H : Subgroup (G0g D.nd)), IsHalf D k H → (∀ g, (badElt D k S * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H) ∧ (badElt D k S * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = ((locShare D (fun k' v => eUk D k' (ψ ⟨k', v⟩)) k S : ℝ) : ℂ) / (Nat.card P : ℂ) := by
  intro D _ P lam ψ hW k S H hH
  classical
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  refine ⟨fun g hg => ?_, ?_⟩
  · rw [Formalism.L2.DIV.coeff_mul_fin] at hg
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    have h1 := left_ne_zero_of_mul hs
    have h2 := right_ne_zero_of_mul hs
    rw [coeff_badElt] at h1
    split_ifs at h1 with hT
    · rw [coeff_lvlIdem_eq] at h2
      split_ifs at h2 with hP
      · rw [hH]
        intro kv hkv
        have hu := (hW.2.1 _).1 hP kv
        have e : (s⁻¹ * g) kv = g kv := by
          simp only [Pi.mul_apply, Pi.inv_apply, hT kv hkv, inv_one, one_mul]
        rwa [e] at hu
      · exact absurd rfl h2
    · exact absurd rfl h1
  · rw [coeff_one_mul_comm, Formalism.L2.DIV.coeff_mul_fin, Finset.sum_congr rfl fun y _ => term_eq D P lam ψ hW k S y,
      sum_trivOff D k (fun z => (Nat.card P : ℂ)⁻¹ * ∑ t ∈ S, ∏ v, phiAt D k (ψ ⟨k, v⟩) (t v) (z v)), ← Finset.mul_sum, Finset.sum_comm]
    simp_rw [← Fintype.prod_sum, sum_phiAt]
    unfold locShare
    push_cast
    simp_rw [wtOf_eUk]
    rw [div_eq_inv_mul]

end GlobalTheory.BadCount
