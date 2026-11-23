import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

noncomputable section

namespace GlobalTheory.BorelChar

open Matrix Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem ext_mat {g h : GU σ n} (e : ⟪g⟫ = ⟪h⟫) : g = h := Subtype.ext (Units.ext e)

theorem exists_conj_mem_K {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {u : GU σ n} (hu : IsUnipU u) :
    ∃ s : GU σ n, IsBorelU s ∧ s * u * s⁻¹ ∈ KU σ n := by
  obtain ⟨hσσ, hσv, hσϖ, hϖ, -, -, -⟩ := hU
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have h0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ'; exact WithZero.exp_ne_zero hϖ'.symm
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ', ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  set U := ⟪u⟫ with hUdef
  obtain ⟨M, hM⟩ := GlobalTheory.UnitarySwap.exists_pow_mem hϖ' U
  let b : Fin n → ℤ := fun i => (M : ℤ) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))
  have hb : ∀ i : Fin n, b i.rev = -b i := by
    intro i
    have := i.isLt
    simp only [b, Fin.val_rev]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  obtain ⟨s, hs, hs'⟩ := Formalism.UG.P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσϖ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  have hpow : ∀ k : ℤ, 0 ≤ k → Valued.v (ϖ ^ k) ≤ 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast, map_pow]
    exact pow_le_one₀ zero_le hϖ1
  set k := s * u * s⁻¹ with hkdef
  have hkm : ⟪k⟫ = Matrix.diagonal (fun i => ϖ ^ b i) * U * Matrix.diagonal (fun i => (ϖ ^ b i)⁻¹) := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hs, hs']
  have hI : Formalism.UG.P.fIwasawaInt ⟪k⟫ := by
    intro i j
    rw [hkm, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rcases lt_trichotomy i j with hij | rfl | hij
    · have hle : (M : ℤ) ≤ b i - b j := by
        have : (i.val : ℤ) + 1 ≤ j.val := by exact_mod_cast hij
        simp only [b]
        nlinarith
      have e : ϖ ^ b i * U i j * (ϖ ^ b j)⁻¹ = ϖ ^ (b i - b j - M) * (ϖ ^ M * U i j) := by
        rw [zpow_sub₀ h0, zpow_sub₀ h0, zpow_natCast]
        field_simp
      rw [e, map_mul]
      exact mul_le_one' (hpow _ (by omega)) (hM i j)
    · have e1 : U i i = 1 := hu.2 i
      rw [e1, mul_one, mul_inv_cancel₀ (zpow_ne_zero _ h0), map_one]
    · have e1 : U i j = 0 := hu.1 i j hij
      rw [e1, mul_zero, zero_mul, map_zero]; exact zero_le
  have hkK : k ∈ Formalism.UG.KU σ n := by
    have := Formalism.UG.P.fIwasawa_mk_mem_K σ hσv _ (Formalism.UG.P.fIwasawa_mem_un σ k) hI
    have e : Formalism.UG.P.fIwasawaMk σ _ (Formalism.UG.P.fIwasawa_mem_un σ k) = k := Subtype.ext (Units.ext rfl)
    rwa [e] at this
  exact ⟨s, Formalism.UG.P.fSatake_borel_of_diag hs, hkK⟩

theorem tMat_add (ϖ : L) (h0 : ϖ ≠ 0) (m : ℕ) (a c : Fin m → ℤ) :
    tMat ϖ n m (a + c) = tMat ϖ n m a * tMat ϖ n m c := by
  unfold tMat
  rw [diagonal_mul_diagonal]
  congr 1; funext i
  split_ifs <;> simp [zpow_add₀ h0, neg_add] <;> ring

theorem tMat_zero (ϖ : L) (m : ℕ) : tMat ϖ n m 0 = 1 := by
  unfold tMat
  rw [← diagonal_one]
  congr 1; funext i
  split_ifs <;> simp

theorem borel_char : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (f : GU σ n → ℂ), (∀ b b', IsBorelU b → IsBorelU b' → f (b * b') = f b * f b') →
    (∀ k ∈ KU σ n, IsBorelU k → f k = 1) → ∀ y : Fin (n / 2) → ℂ,
    (∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → f t = y k) →
    ∀ b, IsBorelU b → f b = ∏ k, y k ^ ordL (b.1.1 (GlobalTheory.SphTheta.lo n k) (GlobalTheory.SphTheta.lo n k)) := by
  intro L _ _ ϖ σ q hU n f hmul hK y hy b hb
  have hϖ0 : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact absurd this WithZero.zero_ne_coe
  have h1 : f 1 = 1 := hK 1 (one_mem _) Formalism.UG.P.fSatake_borel_one
  have hinv : ∀ b, IsBorelU b → f b * f b⁻¹ = 1 := fun b hb => by
    rw [← hmul _ _ hb (Formalism.UG.P.fSatake_borel_inv hb), mul_inv_cancel, h1]

  have hunip : ∀ u, IsUnipU u → f u = 1 := by
    intro u hu
    obtain ⟨s, hs, hsK⟩ := exists_conj_mem_K hU hu
    have hsu := Formalism.UG.P.fSatake_borel_mul hs hu.1
    have := hK _ hsK (Formalism.UG.P.fSatake_borel_mul hsu (Formalism.UG.P.fSatake_borel_inv hs))
    rw [hmul _ _ hsu (Formalism.UG.P.fSatake_borel_inv hs), hmul _ _ hs hu.1] at this
    calc f u = f u * (f s * f s⁻¹) := by rw [hinv s hs, mul_one]
      _ = f s * f u * f s⁻¹ := by ring
      _ = 1 := this

  have hm : 2 * (n / 2) ≤ n := by omega
  have hT : ∀ a : Fin (n / 2) → ℤ, ∃ t : GU σ n, (t).1.1 = tMat ϖ n (n / 2) a :=
    fun a => Formalism.UG.P.fSatake_tMat_exists hU hm a
  choose T hTm using hT
  have hTb : ∀ a, IsBorelU (T a) := fun a => Formalism.UG.P.fSatake_borel_tMat (hTm a)
  have hTadd : ∀ a c, T (a + c) = T a * T c := fun a c => ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, hTm, hTm, hTm, tMat_add ϖ hϖ0])
  have hT0 : T 0 = 1 := ext_mat (by rw [hTm, tMat_zero]; rfl)
  have hg : ∀ a c, f (T (a + c)) = f (T a) * f (T c) := fun a c => by
    rw [hTadd, hmul _ _ (hTb a) (hTb c)]
  have hgu : ∀ a, f (T a) * f (T (-a)) = 1 := fun a => by
    rw [← hg, add_neg_cancel, hT0, h1]
  let G : Multiplicative (Fin (n / 2) → ℤ) →* ℂˣ := MonoidHom.mk'
    (fun a => ⟨f (T a.toAdd), f (T (-a.toAdd)), hgu _, by rw [mul_comm]; exact hgu _⟩)
    (fun a c => Units.ext (by simp only [toAdd_mul, Units.val_mul]; exact hg _ _))
  have hGs : ∀ k, (G (Multiplicative.ofAdd (Pi.single k 1)) : ℂ) = y k := fun k => hy k _ (hTm _)
  have hTval : ∀ a, f (T a) = ∏ k, y k ^ a k := by
    intro a
    have ea : Multiplicative.ofAdd a = ∏ k, (Multiplicative.ofAdd (Pi.single k (1 : ℤ))) ^ a k := by
      simp_rw [← ofAdd_zsmul, ← ofAdd_sum]
      congr 1
      conv_lhs => rw [← Finset.univ_sum_single a]
      refine Finset.sum_congr rfl fun k _ => ?_
      funext j
      simp [Pi.single_apply]
    have := congrArg (fun z => (G z : ℂ)) ea
    simp only [map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hGs] at this
    exact this

  obtain ⟨a, u, hu, k', hk', he⟩ := Formalism.UG.P.fSatake_cell_exists hU hm (by omega) hb (one_mem (KU σ n))
  have hbe : b = T a * u * k' := ext_mat (by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, hTm, ← he, mul_one])
  have htu := Formalism.UG.P.fSatake_borel_mul (hTb a) hu.1
  have hkb : IsBorelU k' := by
    have e : k' = (T a * u)⁻¹ * b := by rw [hbe]; group
    rw [e]; exact Formalism.UG.P.fSatake_borel_mul (Formalism.UG.P.fSatake_borel_inv htu) hb
  have hfb : f b = f (T a) := by
    rw [hbe, hmul _ _ htu hkb, hmul _ _ (hTb a) hu.1, hunip u hu, hK k' hk' hkb, mul_one, mul_one]
  rw [hfb, hTval]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1

  have hj : (j : ℕ) < n := by omega
  have hd : (b).1.1 ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) * (k').1.1 ⟨j, hj⟩ ⟨j, hj⟩ := by
    rw [hbe, Formalism.UG.P.fSatake_borel_diag_mul htu hkb, Formalism.UG.P.fSatake_borel_diag_mul (hTb a) hu.1, hu.2, mul_one,
      hTm, Formalism.UG.P.fSatake_tMat_apply_lt ϖ a j hj]
  have hw0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb ⟨j, hj⟩
  have hwr0 := Formalism.UG.P.fSatake_ne_zero_of_borel hkb (⟨j, hj⟩ : Fin n).rev
  have hpair := congrArg ordL (Formalism.UG.P.fSatake_unit_diag hkb ⟨j, hj⟩)
  rw [Formalism.UG.P.fSatake_ord_mul ((map_ne_zero σ).2 hw0) hwr0, Formalism.UG.P.fSatake_ord_of_v (hU.2.1 _),
    Formalism.UG.P.fSatake_ord_one] at hpair
  have hn1 := Formalism.UG.P.fSatake_ord_nonneg hw0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have hn2 := Formalism.UG.P.fSatake_ord_nonneg hwr0 (Formalism.UG.P.fSatake_K_int hk' _ _)
  have h3 := congrArg ordL hd
  rw [Formalism.UG.P.fSatake_ord_mul (zpow_ne_zero _ hϖ0) hw0, Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1] at h3
  show a j = ordL ((b).1.1 ⟨j, hj⟩ ⟨j, hj⟩)
  omega

end GlobalTheory.BorelChar
