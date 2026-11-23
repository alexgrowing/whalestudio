import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
import Formalism.LocalToGlobal.Columns.BlockTriangularMulVecMemPartialFlag

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section FtY

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem tlq_ftY_pertQ (hcst : cst.Ok) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (hD : 2 * cst.M ≤ cst.D w) {n : ℕ}
    (η δ : Sp X.E n →ₗ[X.E] X.E) (y : Sp X.E n)
    (hδ : ∀ i : Fin n, IntAt w.1 (((qOf w.1 : X.E) ^ (2 * cst.M))⁻¹ * δ (Pi.single i 1)))
    (hq : ((qOf w.1 : X.E) ^ cst.M) • y ∈ stdAt X.E n w.1) :
    ftY sel mu cst w (η + δ) y = ftY sel mu cst w η y := by
  classical
  have hne1 : (1 : 𝓞 X.E) ∉ w.1.asIdeal := (Ideal.ne_top_iff_one _).mp w.1.isPrime.ne_top
  have hqn : (qOf w.1 : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact w.1.ne_bot
  have hqk : ∀ k : ℕ, IntAt w.1 ((qOf w.1 : X.E) ^ k) := fun k =>
    ⟨((qOf w.1 : ℕ) : 𝓞 X.E) ^ k, 1, hne1, by simp⟩
  have hm1 : IntAt w.1 (-1 : X.E) := ⟨-1, 1, hne1, by simp⟩
  have heps : IntAt w.1 ((epsSg : ℤ) : X.E) := ⟨((epsSg : ℤ) : 𝓞 X.E), 1, hne1, by simp⟩
  have h0 : IntAt w.1 (0 : X.E) := ⟨0, 1, hne1, by simp⟩
  have hqM : (qOf w.1 : X.E) ^ cst.M ≠ 0 := pow_ne_zero _ hqn
  have fsum : ∀ (f : Sp X.E n →ₗ[X.E] X.E) (v : Sp X.E n), f v = ∑ i, f (Pi.single i 1) * v i := by
    intro f v
    have hv : v = ∑ j, v j • (Pi.single j (1 : X.E) : Sp X.E n) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]
  have hy : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * y i) := by
    intro i
    have h1 := (ciMem_stdAt w.1 _).mp hq i
    simpa [Pi.smul_apply, smul_eq_mul] using h1
  have hδM : ∀ i, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1)) := by
    intro i
    have e : (qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1) =
        ((qOf w.1 : X.E) ^ cst.M * (qOf w.1 : X.E) ^ cst.M) *
          (((qOf w.1 : X.E) ^ (2 * cst.M))⁻¹ * δ (Pi.single i 1)) * (qOf w.1 : X.E) ^ cst.M := by
      rw [two_mul, pow_add, mul_inv]
      calc _ = ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M)⁻¹) *
            ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M)⁻¹) *
            ((qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1)) := by
            rw [mul_inv_cancel₀ hqM, one_mul, one_mul]
        _ = _ := by ring
    rw [e]
    exact IntAt.mul (IntAt.mul (IntAt.mul (hqk _) (hqk _)) (hδ i)) (hqk _)
  have hδy : IntAt w.1 (δ y) := by
    rw [fsum δ y]
    refine Finset.sum_induction _ (IntAt w.1) (fun a b ha hb => IntAt.add ha hb) h0 (fun i _ => ?_)
    have e : δ (Pi.single i 1) * y i = (((qOf w.1 : X.E) ^ (2 * cst.M))⁻¹ * δ (Pi.single i 1)) *
        ((qOf w.1 : X.E) ^ cst.M * y i) * (qOf w.1 : X.E) ^ cst.M := by
      rw [two_mul, pow_add, mul_inv]
      calc _ = ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M)⁻¹) *
            ((qOf w.1 : X.E) ^ cst.M * ((qOf w.1 : X.E) ^ cst.M)⁻¹) * (δ (Pi.single i 1) * y i) := by
            rw [mul_inv_cancel₀ hqM, one_mul, one_mul]
        _ = _ := by ring
    rw [e]
    exact IntAt.mul (IntAt.mul (hδ i) (hy i)) (hqk _)
  have hcond : (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * (η + δ) (Pi.single i 1))) ↔
      (∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))) := by
    constructor
    · intro h i
      have e : (qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1) = (qOf w.1 : X.E) ^ cst.M * (η + δ) (Pi.single i 1) +
          (-1) * ((qOf w.1 : X.E) ^ cst.M * δ (Pi.single i 1)) := by
        rw [LinearMap.add_apply]; ring
      rw [e]
      exact IntAt.add (h i) (IntAt.mul hm1 (hδM i))
    · intro h i
      rw [LinearMap.add_apply, mul_add]
      exact IntAt.add (h i) (hδM i)
  simp only [ftY, if_neg hw]
  by_cases hC : ∀ i : Fin n, IntAt w.1 ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1))
  · rw [if_pos (hcond.mpr hC), if_pos hC]
    congr 1
    have h2 : IntAt w.1 ((qOf w.1 : X.E) ^ (2 * cst.M) * η y) := by
      rw [fsum η y, Finset.mul_sum]
      refine Finset.sum_induction _ (IntAt w.1) (fun a b ha hb => IntAt.add ha hb) h0 (fun i _ => ?_)
      rw [show (qOf w.1 : X.E) ^ (2 * cst.M) * (η (Pi.single i 1) * y i) =
        ((qOf w.1 : X.E) ^ cst.M * η (Pi.single i 1)) * ((qOf w.1 : X.E) ^ cst.M * y i) by
          rw [two_mul, pow_add]; ring]
      exact IntAt.mul (hC i) (hy i)
    have hηy : IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * η y) := by
      have e : (qOf w.1 : X.E) ^ cst.D w * η y =
          (qOf w.1 : X.E) ^ (cst.D w - 2 * cst.M) * ((qOf w.1 : X.E) ^ (2 * cst.M) * η y) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hD]
      rw [e]
      exact IntAt.mul (hqk _) h2
    have hA : IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * (((epsSg : ℤ) : X.E) * η y)) := by
      rw [mul_left_comm]; exact IntAt.mul heps hηy
    have hB : IntAt w.1 ((qOf w.1 : X.E) ^ cst.D w * (((epsSg : ℤ) : X.E) * δ y)) := by
      rw [mul_left_comm]; exact IntAt.mul heps (IntAt.mul (hqk _) hδy)
    rw [LinearMap.add_apply, mul_add, hcst.psi_add w _ _ hA hB, hcst.psi_int w _ (IntAt.mul heps hδy), mul_one]
  · rw [if_neg (fun h => hC (hcond.mp h)), if_neg hC]

end FtY

section Core

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem tlq_sum_split {N : ℕ} (hN : 1 ≤ N) (f : Fin N → E) :
    ∑ j, f j = ∑ j : Fin (N - 1), f ⟨j.1, by omega⟩ + f ⟨N - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  rfl

def IsKOneType (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) {N : ℕ} (cc : ℕ) (g : Sp E N ≃ₗ[E] Sp E N) : Prop :=
  g ∈ GLint E N P ∧ (∀ (i j : Fin N), (i.1 + 1 = N ↔ ¬ j.1 + 1 = N) → IntAt P (((q : E) ^ cc)⁻¹ * g (Pi.single j 1) i)) ∧
    ∀ (i : Fin N), i.1 + 1 = N → IntAt P (((q : E) ^ cc)⁻¹ * (g (Pi.single i 1) i - 1))

end Core

section Core2

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

private theorem intAt_zero_field : IntAt P (0 : E) :=
  ⟨0, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

private theorem intAt_q_pow (k : ℕ) : IntAt P ((q : E) ^ k) :=
  ⟨((q : ℕ) : 𝓞 E) ^ k, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

private theorem intAt_q_pow_inv_mul_of_le (hq0 : (q : E) ≠ 0) {a b : ℕ} (hab : b ≤ a) {x : E}
    (h : IntAt P (((q : E) ^ a)⁻¹ * x)) : IntAt P (((q : E) ^ b)⁻¹ * x) := by
  have hqa : (q : E) ^ a ≠ 0 := pow_ne_zero _ hq0
  have e : ((q : E) ^ b)⁻¹ * x = (q : E) ^ (a - b) * (((q : E) ^ a)⁻¹ * x) := by
    calc ((q : E) ^ b)⁻¹ * x = ((q : E) ^ a * ((q : E) ^ a)⁻¹) * (((q : E) ^ b)⁻¹ * x) := by
          rw [mul_inv_cancel₀ hqa, one_mul]
      _ = ((q : E) ^ a * ((q : E) ^ b)⁻¹) * (((q : E) ^ a)⁻¹ * x) := by ring
      _ = _ := by rw [pow_sub₀ _ hq0 hab]
  rw [e]; exact IntAt.mul (intAt_q_pow _) h

private theorem intAt_q_pow_sub_inv_mul_mul (hq0 : (q : E) ≠ 0) {a M : ℕ} (hM : M ≤ a) {x y : E}
    (hx : IntAt P (((q : E) ^ a)⁻¹ * x)) (hy : IntAt P ((q : E) ^ M * y)) :
    IntAt P (((q : E) ^ (a - M))⁻¹ * (x * y)) := by
  have e : ((q : E) ^ (a - M))⁻¹ * (x * y) = (((q : E) ^ a)⁻¹ * x) * ((q : E) ^ M * y) := by
    rw [pow_sub₀ _ hq0 hM, mul_inv, inv_inv]; ring
  rw [e]; exact IntAt.mul hx hy

private theorem redP_eq_zero_of_intAt_q_pow_inv_mul (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {cc : ℕ} (hcc : 1 ≤ cc) {x : E}
    (h : IntAt P (((q : E) ^ cc)⁻¹ * x)) : redP P x = 0 := by
  classical
  haveI := P.isPrime
  obtain ⟨r', s', hs', hr'⟩ := h
  have hq0' : ((q : E) ^ cc) ≠ 0 := pow_ne_zero _ hq0
  have h1 : algebraMap (𝓞 E) E s' * x = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ cc * r') := by
    rw [map_mul, map_pow, map_natCast, ← hr']
    calc algebraMap (𝓞 E) E s' * x
        = ((q : E) ^ cc * ((q : E) ^ cc)⁻¹) * (algebraMap (𝓞 E) E s' * x) := by
          rw [mul_inv_cancel₀ hq0', one_mul]
      _ = _ := by ring
  have hmem : ((q : ℕ) : 𝓞 E) ^ cc * r' ∈ P.asIdeal :=
    P.asIdeal.mul_mem_right _ (P.asIdeal.pow_mem_of_mem hq cc (by omega))
  have h2 := reduction_spec P hs' h1
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
  have hs0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact (mul_eq_zero.mp h2).resolve_left hs0

private theorem redP_mul_of_intAt {a b : E} (ha : IntAt P a) (hb : IntAt P b) :
    redP P (a * b) = redP P a * redP P b := by
  haveI := P.isPrime
  obtain ⟨ra, sa, hsa, hra⟩ := ha
  obtain ⟨rb, sb, hsb, hrb⟩ := hb
  have hs : sa * sb ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hsa hsb
  have h3 : algebraMap (𝓞 E) E (sa * sb) * (a * b) = algebraMap (𝓞 E) E (ra * rb) := by
    rw [map_mul, map_mul, ← hra, ← hrb]; ring
  have e1 := reduction_spec P hsa hra
  have e2 := reduction_spec P hsb hrb
  have e3 := reduction_spec P hs h3
  have hs0 : Ideal.Quotient.mk P.asIdeal (sa * sb) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hs0
  rw [e3, map_mul, map_mul, ← e1, ← e2]; ring

private theorem linearEquiv_apply_eq_sum_single {N : ℕ} (g : Sp E N ≃ₗ[E] Sp E N) (v : Sp E N) (i : Fin N) :
    g v i = ∑ j, g (Pi.single j 1) i * v j := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : E) : Sp E N) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem tlq_vec (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {N M cc : ℕ} (hN : 1 ≤ N) (hMc : 3 * M + 1 ≤ cc)
    {g : Sp E N ≃ₗ[E] Sp E N} (hg : IsKOneType P q cc g) (v : Sp E N)
    (hvX : ∀ i : Fin N, i.1 < N - 1 → IntAt P (v i)) (hvL : IntAt P ((q : E) ^ M * v ⟨N - 1, by omega⟩)) :
    (∀ i : Fin N, i.1 < N - 1 → IntAt P (g v i) ∧
      redP P (g v i) = ∑ j : Fin (N - 1), redP P (g (Pi.single ⟨j.1, by omega⟩ 1) i) * redP P (v ⟨j.1, by omega⟩)) ∧
    IntAt P ((((q : E) ^ (2 * M))⁻¹) * (g v ⟨N - 1, by omega⟩ - v ⟨N - 1, by omega⟩)) := by
  obtain ⟨hgI, hgB, hgD⟩ := hg
  have hI : ∀ i j, IntAt P (g (Pi.single j 1) i) := fun i j => (ciMem_stdAt P _).1 ((hgI _).2 (ciSingle_mem j)) i
  have hqn : ∀ k : ℕ, IntAt P ((q : E) ^ k) := fun k => by
    have h := IntAt.coe P (((q : ℕ) : 𝓞 E) ^ k)
    rwa [map_pow, map_natCast] at h
  have hsplit : ∀ i, g v i = ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩ +
      g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ := fun i => by
    rw [residue_linearEquiv_apply_eq_sum g v i, tlq_sum_split hN]

  have hlastcol : ∀ i : Fin N, i.1 < N - 1 →
      IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := fun i hi => by
    have hb := hgB i ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
    have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E) =
        (q : E) ^ (cc - M - 1) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨N - 1, by omega⟩ 1) i) * ((q : E) ^ M * v ⟨N - 1, by omega⟩)) := by
      have h1 : (q : E) ^ cc = (q : E) ^ (cc - M - 1) * (q : E) ^ M * (q : E) := by
        rw [← pow_add, ← pow_succ, show cc - M - 1 + M + 1 = cc by omega]
      rw [h1]
      field_simp
    rw [e]
    exact (hqn _).mul (hb.mul hvL)
  refine ⟨fun i hi => ?_, ?_⟩
  · have hfirst : IntAt P (∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) i * v ⟨j.1, by omega⟩) :=
      ciIntAt_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)
    have hl := hlastcol i hi
    have hlI : IntAt P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩) := by
      have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ =
          (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := by field_simp
      rw [e]
      exact (hqn 1 |>.mul hl |> fun h => by simpa using h)
    refine ⟨by rw [hsplit]; exact hfirst.add hlI, ?_⟩
    rw [hsplit, reduction_add hfirst hlI]
    have hz : redP P (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩) = 0 := by
      have e : g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ =
          (q : E) * (g (Pi.single ⟨N - 1, by omega⟩ 1) i * v ⟨N - 1, by omega⟩ / (q : E)) := by field_simp
      rw [e, reduction_mul (by simpa using hqn 1) hl, redP_natCast_eq_zero hq, zero_mul]
    rw [hz, add_zero, redP_sum _ _ fun j _ => (hI _ _).mul (hvX _ j.2)]
    exact Finset.sum_congr rfl fun j _ => reduction_mul (hI _ _) (hvX _ j.2)
  · rw [hsplit]
    have e : ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩ +
          g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨N - 1, by omega⟩ - v ⟨N - 1, by omega⟩ =
        ∑ j : Fin (N - 1), g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩ +
          (g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1) * v ⟨N - 1, by omega⟩ := by ring
    rw [e, mul_add, Finset.mul_sum]
    refine (ciIntAt_sum _ _ fun j _ => ?_).add ?_
    · have hc := hgB ⟨N - 1, by omega⟩ ⟨j.1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
      have e2 : ((q : E) ^ (2 * M))⁻¹ * (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩ * v ⟨j.1, by omega⟩) =
          (q : E) ^ (cc - 2 * M) * ((((q : E) ^ cc)⁻¹ * g (Pi.single ⟨j.1, by omega⟩ 1) ⟨N - 1, by omega⟩) * v ⟨j.1, by omega⟩) := by
        have h1 : (q : E) ^ cc = (q : E) ^ (cc - 2 * M) * (q : E) ^ (2 * M) := by rw [← pow_add, show cc - 2 * M + 2 * M = cc by omega]
        rw [h1]
        field_simp
      rw [e2]
      exact (hqn _).mul (hc.mul (hvX _ j.2))
    · have hd := hgD ⟨N - 1, by omega⟩ (by first | omega | (simp; done) | (simp; omega))
      have e2 : ((q : E) ^ (2 * M))⁻¹ * ((g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1) * v ⟨N - 1, by omega⟩) =
          (q : E) ^ (cc - 3 * M) * ((((q : E) ^ cc)⁻¹ * (g (Pi.single ⟨N - 1, by omega⟩ 1) ⟨N - 1, by omega⟩ - 1)) *
            ((q : E) ^ M * v ⟨N - 1, by omega⟩)) := by
        have h1 : (q : E) ^ cc = (q : E) ^ (cc - 3 * M) * (q : E) ^ (2 * M) * (q : E) ^ M := by
          rw [← pow_add, ← pow_add, show cc - 3 * M + 2 * M + M = cc by omega]
        rw [h1]
        field_simp
      rw [e2]
      exact (hqn _).mul (hd.mul hvL)

end Core2

section Core3

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem tlq_core (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {n' N M cc : ℕ} (hN : 1 ≤ N) (hMc : 3 * M + 1 ≤ cc)
    (Φ : HomE E n' ((N - 1) + 0) → K) (hΦs : ∀ x, Φ x ≠ 0 → ∀ s l, IntAt P (x (Pi.single s 1) l))
    (hΦr : ∀ x x', (∀ s l, IntAt P (x (Pi.single s 1) l)) → (∀ s l, IntAt P (x' (Pi.single s 1) l)) → redMQ P x = redMQ P x' → Φ x = Φ x')
    (T : (Sp E n' →ₗ[E] E) → K) (hTs : ∀ η, T η ≠ 0 → ∀ i, IntAt P ((q : E) ^ M * η (Pi.single i 1)))
    (hTp : ∀ η δ, (∀ i, IntAt P (((q : E) ^ (2 * M))⁻¹ * δ (Pi.single i 1))) → T (η + δ) = T η)
    (g : Sp E N ≃ₗ[E] Sp E N) (hg : IsKOneType P q cc g) (hg' : IsKOneType P q cc g.symm)
    (κ : Sp E ((N - 1) + 0) ≃ₗ[E] Sp E ((N - 1) + 0)) (hκ : κ ∈ GLint E ((N - 1) + 0) P)
    (hκr : ∀ v ∈ stdAt E ((N - 1) + 0) P, redV P (κ v) =
      (Matrix.of fun (i j : Fin ((N - 1) + 0)) => redP P (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)).mulVec (redV P v))
    (z : HomE E n' N) :
    Φ (prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) =
      Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) := by
  classical
  have hL : N - 1 < N := by omega
  have hat : ∀ (w : HomE E n' N) (s : Fin n'),
      (atNL E N (N - 1) ∘ₗ w) (Pi.single s 1) = w (Pi.single s 1) ⟨N - 1, hL⟩ := by
    intro w s; simp [atNL, hL]
  have transfer : ∀ (h : Sp E N ≃ₗ[E] Sp E N), IsKOneType P q cc h → ∀ w : HomE E n' N,
      (∀ (s : Fin n') (i : Fin N), i.1 < N - 1 → IntAt P (w (Pi.single s 1) i)) →
      (∀ s, IntAt P ((q : E) ^ M * w (Pi.single s 1) ⟨N - 1, hL⟩)) →
      (∀ (s : Fin n') (i : Fin N), i.1 < N - 1 → IntAt P (h (w (Pi.single s 1)) i) ∧
          redP P (h (w (Pi.single s 1)) i) = ∑ j : Fin (N - 1),
            redP P (h (Pi.single ⟨j.1, by omega⟩ 1) i) * redP P (w (Pi.single s 1) ⟨j.1, by omega⟩)) ∧
      (∀ s, IntAt P ((q : E) ^ M * h (w (Pi.single s 1)) ⟨N - 1, hL⟩)) := by
    intro h hh w hw1 hw2
    refine ⟨fun s i hi => (tlq_vec hq hq0 hN hMc hh (w (Pi.single s 1)) (hw1 s) (hw2 s)).1 i hi, fun s => ?_⟩
    have hb := (tlq_vec hq hq0 hN hMc hh (w (Pi.single s 1)) (hw1 s) (hw2 s)).2
    have h2 : (q : E) ^ (2 * M) ≠ 0 := pow_ne_zero _ hq0
    have e : (q : E) ^ M * h (w (Pi.single s 1)) ⟨N - 1, hL⟩ = (q : E) ^ M * w (Pi.single s 1) ⟨N - 1, hL⟩ +
        (q : E) ^ (3 * M) * (((q : E) ^ (2 * M))⁻¹ *
          (h (w (Pi.single s 1)) ⟨N - 1, hL⟩ - w (Pi.single s 1) ⟨N - 1, hL⟩)) := by
      rw [show 3 * M = M + 2 * M by ring, pow_add]
      calc _ = (q : E) ^ M * w (Pi.single s 1) ⟨N - 1, hL⟩ + (q : E) ^ M * ((q : E) ^ (2 * M) * ((q : E) ^ (2 * M))⁻¹) *
            (h (w (Pi.single s 1)) ⟨N - 1, hL⟩ - w (Pi.single s 1) ⟨N - 1, hL⟩) := by
            rw [mul_inv_cancel₀ h2]; ring
        _ = _ := by ring
    rw [e]
    exact IntAt.add (hw2 s) (IntAt.mul (intAt_q_pow _) hb)
  by_cases hgood : (∀ (s : Fin n') (i : Fin N), i.1 < N - 1 → IntAt P (z (Pi.single s 1) i)) ∧
      ∀ s, IntAt P ((q : E) ^ M * z (Pi.single s 1) ⟨N - 1, hL⟩)
  · obtain ⟨hz1, hz2⟩ := hgood
    have htr := transfer g hg z hz1 hz2
    have hxs : ∀ s, prXpG E N (z (Pi.single s 1)) ∈ stdAt E ((N - 1) + 0) P := by
      intro s
      rw [ciMem_stdAt]
      intro l'
      exact hz1 s ⟨l'.1, by omega⟩ (by show l'.1 < N - 1; omega)
    have hT : T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) = T (atNL E N (N - 1) ∘ₗ z) := by
      have hδ : ∀ i, IntAt P (((q : E) ^ (2 * M))⁻¹ *
          (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z - atNL E N (N - 1) ∘ₗ z) (Pi.single i 1)) := by
        intro i
        rw [LinearMap.sub_apply, hat, hat]
        exact (tlq_vec hq hq0 hN hMc hg (z (Pi.single i 1)) (hz1 i) (hz2 i)).2
      have h3 := hTp (atNL E N (N - 1) ∘ₗ z) _ hδ
      rw [show atNL E N (N - 1) ∘ₗ z + (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z - atNL E N (N - 1) ∘ₗ z) =
        atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z by abel] at h3
      exact h3
    have hΦ : Φ (prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) = Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) := by
      apply hΦr
      · intro s l
        exact (htr.1 s ⟨l.1, by omega⟩ (by show l.1 < N - 1; omega)).1
      · intro s l
        exact (ciMem_stdAt P _).mp ((hκ _).mpr (hxs s)) l
      · ext l s
        have h1 := (htr.1 s ⟨l.1, by omega⟩ (by show l.1 < N - 1; omega)).2
        have h2 := congrFun (hκr _ (hxs s)) l
        exact h1.trans h2.symm
    rw [hΦ, hT]
  · have hR : Φ (κ.toLinearMap ∘ₗ prXpG E N ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ z) = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
      apply hgood
      refine ⟨fun s i hi => ?_, fun s => ?_⟩
      · have hint := hΦs _ h1 s
        have hk : κ (prXpG E N (z (Pi.single s 1))) ∈ stdAt E ((N - 1) + 0) P := (ciMem_stdAt P _).mpr hint
        exact (ciMem_stdAt P _).mp ((hκ _).mp hk) ⟨i.1, by omega⟩
      · have h4 := hTs _ h2 s
        rw [hat] at h4
        exact h4
    have hLz : Φ (prXpG E N ∘ₗ g.toLinearMap ∘ₗ z) * T (atNL E N (N - 1) ∘ₗ g.toLinearMap ∘ₗ z) = 0 := by
      by_contra hne
      obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hne
      apply hgood
      have hw1 : ∀ (s : Fin n') (i : Fin N), i.1 < N - 1 → IntAt P ((g.toLinearMap ∘ₗ z) (Pi.single s 1) i) := by
        intro s i hi
        exact hΦs _ h1 s ⟨i.1, by omega⟩
      have hw2 : ∀ s, IntAt P ((q : E) ^ M * (g.toLinearMap ∘ₗ z) (Pi.single s 1) ⟨N - 1, hL⟩) := by
        intro s
        have h4 := hTs _ h2 s
        rw [hat] at h4
        exact h4
      have htr := transfer g.symm hg' (g.toLinearMap ∘ₗ z) hw1 hw2
      refine ⟨fun s i hi => ?_, fun s => ?_⟩
      · have h5 := (htr.1 s i hi).1
        simpa using h5
      · have h5 := htr.2 s
        simpa using h5
    rw [hR, hLz]

end Core3

section K1

open Classical

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem tlq_single_mem {n : ℕ} (e : ℕ → ℤ) (j : Fin n) (hj : e j.1 = 0) : (Pi.single j 1 : Sp E n) ∈ LocE.sclLat P (qOf P) n e := by
  rw [ciMem_sclLat]
  intro l
  by_cases hl : l = j
  · subst hl
    simp only [Pi.single_eq_same, hj, zpow_zero, inv_one, one_mul]
    exact ⟨1, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩
  · simp only [Pi.single_eq_of_ne hl, mul_zero]
    exact ⟨0, 1, (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top, by simp⟩

theorem isKOneType_of_mem_kOne {n r c : ℕ} (g : ↥(GLint E n P)) (hg : g ∈ twK1H P n r c) : IsKOneType P (qOf P) c (g : Sp E n ≃ₗ[E] Sp E n) := by
  obtain ⟨_, hL, _, hX⟩ := hg
  refine ⟨g.2, ?_, ?_⟩
  · intro i j hij
    by_cases hj : j.1 + 1 = n
    · have hi : ¬ i.1 + 1 = n := fun hi => (hij.mp hi) hj
      have hij' : i ≠ j := fun h => hi (by rw [h]; exact hj)
      have h1 := hX (Pi.single j 1) (tlq_single_mem P (twistedLevelExponent n c) j (by simp [twistedLevelExponent, hj]))
      rw [ciMem_sclLat] at h1
      have h2 := h1 i
      simpa [Pi.single_apply, hij'] using h2
    · have hi : i.1 + 1 = n := hij.mpr hj
      have h1 := ((hL (Pi.single j 1)).mpr (tlq_single_mem P (kOneLastExponents n c) j (by simp [kOneLastExponents, hj])))
      rw [ciMem_sclLat] at h1
      have h2 := h1 i
      simpa [kOneLastExponents, hi] using h2
  · intro i hi
    have h1 := hX (Pi.single i 1) (tlq_single_mem P (twistedLevelExponent n c) i (by simp [twistedLevelExponent, hi]))
    rw [ciMem_sclLat] at h1
    simpa using h1 i

theorem isKOneType_symm_of_mem_kOne {n r c : ℕ} (g : ↥(GLint E n P)) (hg : g ∈ twK1H P n r c) :
    IsKOneType P (qOf P) c (g : Sp E n ≃ₗ[E] Sp E n).symm := by
  exact isKOneType_of_mem_kOne P (g⁻¹) (inv_mem hg)

end K1

section GlobalTheory

variable {κ : Type} [CommRing κ]

def LastRowColIdentity {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ) : Prop :=
  (∀ j : Fin n, M (Fin.last n) (Fin.castSucc j) = 0) ∧ (∀ i : Fin n, M (Fin.castSucc i) (Fin.last n) = 0) ∧
    M (Fin.last n) (Fin.last n) = 1

theorem blk_det {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ) (hM : LastRowColIdentity M) :
    M.det = (M.submatrix Fin.castSucc Fin.castSucc).det := by
  have hpow : ((-1 : κ)) ^ (n + n) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [Matrix.det_succ_row M (Fin.last n), Fin.sum_univ_castSucc]
  simp [hM.1, hM.2.2, Fin.succAbove_last, hpow]

theorem blk_inv {n : ℕ} (M M' : Matrix (Fin (n + 1)) (Fin (n + 1)) κ) (hM' : LastRowColIdentity M') (h : M' * M = 1) :
    M'.submatrix Fin.castSucc Fin.castSucc * M.submatrix Fin.castSucc Fin.castSucc = 1 := by
  ext i j
  have h1 := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hM'.2.1 i, zero_mul, add_zero] at h1
  simpa [Matrix.mul_apply, Matrix.one_apply, Fin.castSucc_inj] using h1

theorem blk_D {n r d : ℕ} (hn : n = r + d) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) κ) (hM : LastRowColIdentity M) :
    (M.submatrix (brI (show n + 1 = r + (d + 1) by omega)) (brI (show n + 1 = r + (d + 1) by omega))).det =
      ((M.submatrix Fin.castSucc Fin.castSucc).submatrix (brI hn) (brI hn)).det := by
  have hB : LastRowColIdentity (M.submatrix (brI (show n + 1 = r + (d + 1) by omega))
      (brI (show n + 1 = r + (d + 1) by omega))) := by
    have e1 : brI (show n + 1 = r + (d + 1) by omega) (Fin.last d) = Fin.last n :=
      Fin.ext (by simp only [brI, Fin.val_last]; omega)
    refine ⟨fun j => ?_, fun i => ?_, ?_⟩
    · have e2 : brI (show n + 1 = r + (d + 1) by omega) (Fin.castSucc j) =
          Fin.castSucc (⟨r + j.1, by have := j.2; omega⟩ : Fin n) :=
        Fin.ext (by simp only [brI, Fin.coe_castSucc])
      simp only [Matrix.submatrix_apply, e1, e2]
      exact hM.1 _
    · have e2 : brI (show n + 1 = r + (d + 1) by omega) (Fin.castSucc i) =
          Fin.castSucc (⟨r + i.1, by have := i.2; omega⟩ : Fin n) :=
        Fin.ext (by simp only [brI, Fin.coe_castSucc])
      simp only [Matrix.submatrix_apply, e1, e2]
      exact hM.2.1 _
    · simp only [Matrix.submatrix_apply, e1]
      exact hM.2.2
  rw [blk_det _ hB]
  rfl

end GlobalTheory

section RedBlk

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem reduction_zero_of_high_divisibility (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {cc : ℕ} (hcc : 1 ≤ cc) {x : E}
    (h : IntAt P (((q : E) ^ cc)⁻¹ * x)) : redP P x = 0 := by
  classical
  haveI := P.isPrime
  obtain ⟨r', s', hs', hr'⟩ := h
  have hq0' : ((q : E) ^ cc) ≠ 0 := pow_ne_zero _ hq0
  have h1 : algebraMap (𝓞 E) E s' * x = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ cc * r') := by
    rw [map_mul, map_pow, map_natCast, ← hr']
    calc algebraMap (𝓞 E) E s' * x
        = ((q : E) ^ cc * ((q : E) ^ cc)⁻¹) * (algebraMap (𝓞 E) E s' * x) := by
          rw [mul_inv_cancel₀ hq0', one_mul]
      _ = _ := by ring
  have hmem : ((q : ℕ) : 𝓞 E) ^ cc * r' ∈ P.asIdeal :=
    P.asIdeal.mul_mem_right _ (P.asIdeal.pow_mem_of_mem hq cc (by omega))
  simp only [redP]
  split_ifs with hex
  · obtain ⟨r, s, hs, hsx, hc⟩ := hex.choose_spec
    have h2 : algebraMap (𝓞 E) E (s' * r) = algebraMap (𝓞 E) E (s * (((q : ℕ) : 𝓞 E) ^ cc * r')) := by
      rw [map_mul, ← hsx, map_mul, ← h1]; ring
    have h2' := IsFractionRing.injective (𝓞 E) E h2
    have hr : r ∈ P.asIdeal := by
      have : s' * r ∈ P.asIdeal := by rw [h2']; exact P.asIdeal.mul_mem_left _ hmem
      exact (P.isPrime.mem_or_mem this).resolve_left hs'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr] at hc
    have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact (mul_eq_zero.mp hc).resolve_left hs0
  · rfl

private theorem redP_eq_one_of_intAt_q_pow_inv_mul_sub_one (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {cc : ℕ} (hcc : 1 ≤ cc)
    {x : E} (h : IntAt P (((q : E) ^ cc)⁻¹ * (x - 1))) : redP P x = 1 := by
  haveI := P.isPrime
  obtain ⟨r', s', hs', hr'⟩ := h
  have hq0' : ((q : E) ^ cc) ≠ 0 := pow_ne_zero _ hq0
  have h1 : algebraMap (𝓞 E) E s' * x = algebraMap (𝓞 E) E (s' + ((q : ℕ) : 𝓞 E) ^ cc * r') := by
    rw [map_add, map_mul, map_pow, map_natCast, ← hr']
    calc algebraMap (𝓞 E) E s' * x
        = algebraMap (𝓞 E) E s' + ((q : E) ^ cc * ((q : E) ^ cc)⁻¹) * (algebraMap (𝓞 E) E s' * (x - 1)) := by
          rw [mul_inv_cancel₀ hq0', one_mul]; ring
      _ = _ := by ring
  have hmem : ((q : ℕ) : 𝓞 E) ^ cc * r' ∈ P.asIdeal :=
    P.asIdeal.mul_mem_right _ (P.asIdeal.pow_mem_of_mem hq cc (by omega))
  have h2 := reduction_spec P hs' h1
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, add_zero] at h2
  have hs0 : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Ideal.Quotient.mk P.asIdeal s' * (redP P x - 1) = 0 := by
    rw [mul_sub, h2, mul_one, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hs0)

theorem tlq_red_blk (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {n cc : ℕ} (hcc : 1 ≤ cc)
    {g : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1)} (hg : IsKOneType P q cc g) : LastRowColIdentity (redMQ P g.toLinearMap) := by
  refine ⟨fun j => ?_, fun i => ?_, ?_⟩
  · simp only [redMQ, Matrix.of_apply]
    exact reduction_zero_of_high_divisibility hq hq0 hcc (hg.2.1 (Fin.last n) (Fin.castSucc j)
      (Iff.intro (fun _ h => by have := j.isLt; simp at h; omega) (fun _ => rfl)))
  · simp only [redMQ, Matrix.of_apply]
    exact reduction_zero_of_high_divisibility hq hq0 hcc (hg.2.1 (Fin.castSucc i) (Fin.last n)
      (Iff.intro (fun h _ => by have := i.isLt; simp at h; omega) (fun h => (h rfl).elim)))
  · simp only [redMQ, Matrix.of_apply]
    exact redP_eq_one_of_intAt_q_pow_inv_mul_sub_one hq hq0 hcc (hg.2.2 (Fin.last n) (by simp))

end RedBlk

section Gen2

open Classical

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem kOneType_block_matrix (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {N n cc : ℕ} (hN : N = n + 1) (hcc : 1 ≤ cc)
    (g : Sp E N ≃ₗ[E] Sp E N) (hg : IsKOneType P q cc g) (hg' : IsKOneType P q cc g.symm) :
    let A : Matrix (Fin (N - 1 + 0)) (Fin (N - 1 + 0)) (𝓞 E ⧸ P.asIdeal) :=
      Matrix.of fun i j => redP P (g (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)
    let Ai : Matrix (Fin (N - 1 + 0)) (Fin (N - 1 + 0)) (𝓞 E ⧸ P.asIdeal) :=
      Matrix.of fun i j => redP P (g.symm (Pi.single ⟨j.1, by omega⟩ 1) ⟨i.1, by omega⟩)
    (Ai * A = 1 ∧ A * Ai = 1) ∧ ((redMQ P g.toLinearMap).det = A.det ∧ (redMQ P g.symm.toLinearMap).det = Ai.det) ∧
      ∀ (r d : ℕ) (hnd : N - 1 + 0 = r + d),
        ((redMQ P g.toLinearMap).submatrix (brI (show N = r + (d + 1) by omega)) (brI (show N = r + (d + 1) by omega))).det =
          (A.submatrix (brI hnd) (brI hnd)).det := by
  subst hN
  intro A Ai
  have hB := tlq_red_blk hq hq0 hcc hg
  have hB' := tlq_red_blk hq hq0 hcc hg'
  have hAe : A = (redMQ P g.toLinearMap).submatrix Fin.castSucc Fin.castSucc := by
    ext i j; rfl
  have hAie : Ai = (redMQ P g.symm.toLinearMap).submatrix Fin.castSucc Fin.castSucc := by
    ext i j; rfl
  have h1 : redMQ P g.toLinearMap * redMQ P g.symm.toLinearMap = 1 := redMQ_inv_mul hg.1
  have h2 : redMQ P g.symm.toLinearMap * redMQ P g.toLinearMap = 1 := redMQ_inv_mul hg'.1
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun r d hnd => ?_⟩
  · rw [hAe, hAie]; exact blk_inv _ _ hB' h2
  · rw [hAe, hAie]; exact blk_inv _ _ hB h1
  · rw [hAe]; exact blk_det _ hB
  · rw [hAie]; exact blk_det _ hB'
  · have hn : n = r + d := by omega
    rw [hAe]; exact blk_D hn _ hB

theorem tlq_phiQ_supp (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ r c' n' n : ℕ} (hc' : c' = 0) (hn' : r ≤ n') (hn : r ≤ n) (x : HomE E n' (n + 0)) :
    LocE.PhiQ q ξ k₀ r c' n' 0 n (x ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) ≠ 0 → ∀ s l, IntAt P (x (Pi.single s 1) l) := by
  subst hc'
  intro hne s l
  have h := phiQ_suppB q ξ k₀ r 0 n' n rfl _ hne (Fin.castAdd 0 s) l
  have e : (LinearMap.funLeft E E (Fin.castAdd 0) (Pi.single (Fin.castAdd 0 s) (1 : E)) : Sp E n') =
      Pi.single s 1 := by
    ext t; simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
  rw [LinearMap.comp_apply, e] at h
  exact h

private theorem intAt_q_inv_mul_sub_of_redP_eq (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a b : E}
    (ha : IntAt P a) (hb : IntAt P b) (hab : redP P a = redP P b) : IntAt P ((q : E)⁻¹ * (b - a)) := by
  classical
  haveI := P.isPrime
  have hqn : q ≠ 0 := by rintro rfl; exact hu (by simp)
  have hq0 : (q : E) ≠ 0 := Nat.cast_ne_zero.mpr hqn
  obtain ⟨ra, sa, hsa, hra⟩ := ha
  obtain ⟨rb, sb, hsb, hrb⟩ := hb
  have h1 := reduction_spec P hsa hra
  have h2 := reduction_spec P hsb hrb
  have ht : sa * rb - sb * ra ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, ← h1, ← h2, hab]; ring
  have hle : Ideal.span {((q : ℕ) : 𝓞 E)} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hq
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hu
    have h3 : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal * J := by rw [← hJ]; exact Ideal.mem_span_singleton_self _
    rw [pow_two]; exact Ideal.mul_mono_right hJ' h3
  obtain ⟨u, huJ, huP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hut : u * (sa * rb - sb * ra) ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
    rw [hJ, mul_comm u]; exact Ideal.mul_mem_mul ht huJ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hut
  have hw' := congrArg (algebraMap (𝓞 E) E) hw
  simp only [map_mul, map_sub, map_natCast] at hw'
  rw [← hra, ← hrb] at hw'
  refine ⟨w, u * (sa * sb), ?_, ?_⟩
  · intro h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact huP h
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact hsa h
      · exact hsb h
  · calc algebraMap (𝓞 E) E (u * (sa * sb)) * ((q : E)⁻¹ * (b - a))
        = (q : E)⁻¹ * (algebraMap (𝓞 E) E u * (algebraMap (𝓞 E) E sa * (algebraMap (𝓞 E) E sb * b) -
            algebraMap (𝓞 E) E sb * (algebraMap (𝓞 E) E sa * a))) := by
          rw [map_mul, map_mul]; ring
      _ = (q : E)⁻¹ * (algebraMap (𝓞 E) E w * (q : E)) := by rw [← hw']
      _ = algebraMap (𝓞 E) E w := by
          rw [mul_comm, mul_assoc, mul_inv_cancel₀ hq0, mul_one]

theorem tlq_phiQ_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ r c' n' n : ℕ} (hc' : c' = 0) (hn' : r ≤ n') (hn : r ≤ n) (x x' : HomE E n' (n + 0))
    (hx : ∀ s l, IntAt P (x (Pi.single s 1) l)) (hx' : ∀ s l, IntAt P (x' (Pi.single s 1) l)) (hred : redMQ P x = redMQ P x') :
    LocE.PhiQ q ξ k₀ r c' n' 0 n (x ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) =
      LocE.PhiQ q ξ k₀ r c' n' 0 n (x' ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) := by
  subst hc'
  have hqn : q ≠ 0 := by rintro rfl; exact hu (by simp)
  generalize hy : x ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0) = y
  generalize hy' : x' ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0) = y'
  have hz : ∀ s l, IntAt P ((q : E)⁻¹ * (y' - y) (Pi.single s 1) l) := by
    intro s l
    subst hy hy'
    have e : (LinearMap.funLeft E E (Fin.castAdd 0) (Pi.single s (1 : E)) : Sp E n') =
        Pi.single (⟨s.1, by have := s.2; omega⟩ : Fin n') 1 := by
      ext t; simp [LinearMap.funLeft_apply, Pi.single_apply, Fin.ext_iff]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Pi.sub_apply, e]
    refine intAt_q_inv_mul_sub_of_redP_eq hq hu (hx _ l) (hx' _ l) ?_
    have h5 := congrFun (congrFun hred l) (⟨s.1, by have := s.2; omega⟩ : Fin n')
    simpa [redMQ] using h5
  have key := phiQ_invB hqn hq ξ k₀ r 0 n' n rfl y (y' - y) hz
  rw [show y + (y' - y) = y' by abel] at key
  exact key.symm

theorem tlq_inX_zero {N : ℕ} (x : Sp E N) : Loc.inX E N 0 x = x := by
  funext l
  simp [Loc.inX, l.isLt]

end Gen2

end Formalism.L2.Col
