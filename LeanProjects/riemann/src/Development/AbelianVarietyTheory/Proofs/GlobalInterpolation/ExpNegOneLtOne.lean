import Mathlib
import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Formalism.LocalToGlobal.Columns.BaseLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TameVal

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := by
  have hx0 : v.valuation L (x : L) ≠ 0 := by simp
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have h1 : v.valuation L (((y * x⁻¹ : Lˣ) : L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
    have : ((y * x⁻¹ : Lˣ) : L) - 1 = ((y : L) - x) * (x : L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, _root_.sub_mul, mul_inv_cancel₀ x.ne_zero]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hx0)]
    exact hxy
  have h2 : v.valuation L ((y * x⁻¹ : Lˣ) : L) = 1 := by
    have := Valuation.map_one_add_of_lt (v.valuation L) (h1.trans_lt exp_neg_one_lt_one)
    rwa [add_sub_cancel] at this
  have h3 : χ.locK v (y * x⁻¹) = 1 := by
    refine h (atFin v (y * x⁻¹)) ?_ ?_
    · exact (hval _).trans h2
    · have : ((atFin v (y * x⁻¹) : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
          algebraMap L (v.adicCompletion L) (((y * x⁻¹ : Lˣ) : L) - 1) := by
        rw [map_sub, map_one]; rfl
      rw [this, hval]
      simpa using h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h3

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

theorem locK_mem (χ : HChar L) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (htame : ∀ v, χ.TameAt v) (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : χ.locK P x ∈ G := by
  classical
  have hpr : χ.ProductRule := GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩
  have key : ∀ (a : 𝓞 L) (ha : (a : L) ≠ 0), χ.locK P (Units.mk0 (a : L) ha) ∈ G := by
    intro a ha
    have ha' : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1)
      (fun v => by split_ifs; exacts [ha', one_ne_zero])
    have hP := hy P (Finset.mem_insert_self _ _)
    simp only [if_true] at hP
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hP
      have hpos : 0 < P.valuation L (a : L) := zero_lt_iff.2 (by simpa using ha')
      have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
      rw [one_mul] at this
      exact absurd hP (not_le.2 this)
    have e1 : χ.locK P (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (a : L) ha) :=
      locK_eq_of_tame χ (htame P) _ _ hP
    have e2 : ∏ v ∈ insert P T, χ.locK v (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (y : L) hy0) := by
      refine Finset.prod_eq_single P (fun v hv hne => ?_) (fun h => absurd (Finset.mem_insert_self _ _) h)
      have h1 := hy v hv
      simp only [if_neg hne] at h1
      rw [locK_eq_of_tame χ (htame v) 1 _ (by simpa using h1), map_one]
    have h := hpr (insert P T) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (Units.mk0 (y : L) hy0)
    rw [e2, e1] at h
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ insert P T),
        χ.val v ^ ordF v (Units.mk0 (y : L) hy0)) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 : _ ∈ G := h ▸ G.one_mem
    rw [G.mul_mem_cancel_right hF, G.mul_mem_cancel_left (hinf _)] at h1
    exact h1
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 L) (x : L)
  have hb0 : (b : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have ha0 : (a : L) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab]
    change (a : L) / _ = 0
    rw [h, zero_div]
  have hx : x = Units.mk0 (a : L) ha0 * (Units.mk0 (b : L) hb0)⁻¹ := by
    apply Units.ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0) (G.inv_mem (key b hb0))

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun ha hb => M.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]; exact M.inv_mem ha

theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
  have h2 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_ofNat, div_pow, ← h1]
  field_simp

theorem locK_mem_coeff : ∀ (Z : Dat), Z.Ok → ∀ (m0 : Fin Z.R.m → Formalism.L2.Host.HChar Z.X.E) (eta : Formalism.L2.Host.HChar Z.X.E), Z.Ch.Tied Z.sig0 (fun j τ => (Z.W.row τ).e j) m0 eta → ∀ (j : Fin Z.R.m) (P : HeightOneSpectrum (𝓞 Z.X.E)) (x : Z.X.Eˣ), ∃ k : Z.X.K, Z.sig0 k = (((m0 j).locK P x : ℂˣ) : ℂ) := by
  intro Z hZ m0 eta hT j P x
  have hm := hT.mu0 j
  have hg : ((Z.Pr.g 0 : ℕ) : 𝓞 Z.X.E) * ((Z.Pr.g 1 : ℕ) : 𝓞 Z.X.E) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (hZ.primes.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (hZ.primes.g_prime 1).ne_zero)
  have hoff : ∀ v : HeightOneSpectrum (𝓞 Z.X.E),
      v ∉ divs (((Z.Pr.g 0 : ℕ) : 𝓞 Z.X.E) * ((Z.Pr.g 1 : ℕ) : 𝓞 Z.X.E)) →
      ∀ i, ((Z.Pr.g i : ℕ) : 𝓞 Z.X.E) ∉ v.asIdeal := by
    intro v hv i hi
    apply hv
    rw [Formalism.L2.Col.mem_divs hg]
    fin_cases i
    · exact v.asIdeal.mul_mem_right _ hi
    · exact v.asIdeal.mul_mem_left _ hi
  refine locK_mem (m0 j) (unitsIn Z.sig0.fieldRange) _ hm.tame (fun v hv => hm.unr v (hoff v hv))
    (fun v hv => ⟨_, hT.muVal j v (hoff v hv)⟩) (fun k => ?_) P x
  obtain ⟨n, hn, hinf⟩ := hm.inf
  change (((m0 j).inf k : ℂˣ) : ℂ) ∈ Z.sig0.fieldRange
  rw [hinf k]
  refine prod_mem fun τ _ => ?_
  obtain ⟨Q, hQ⟩ := hZ.wts.row_ok τ
  obtain ⟨z, hz⟩ := Q.e_int j
  have he : (Z.W.row τ).e j = z := by rw [← hQ]; exact hz
  have hn2 : n τ = 2 * (-z) := by
    have := hn τ
    simp only [he] at this
    exact_mod_cast this
  rw [hn2, zpow_mul, sq_div_norm ((map_ne_zero _).2 k.ne_zero), ← hZ.fields.conjE]
  exact zpow_mem (Z.sig0.fieldRange.div_mem ⟨_, rfl⟩ ⟨_, rfl⟩) _

end GlobalTheory.TameVal
