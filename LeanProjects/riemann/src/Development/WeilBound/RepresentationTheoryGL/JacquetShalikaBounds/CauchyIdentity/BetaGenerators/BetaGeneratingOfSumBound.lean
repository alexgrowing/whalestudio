import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.SchurJT
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.StaircaseDeterminants.AlternatingJacobiTrudiOfRelation
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.CauchyIdentity.ProductCoefficients.ElementaryRelationOfGenerating
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CauchyBinet

noncomputable section

open Finset Matrix Filter Topology GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace PositivityTheory.RgJS

namespace BetaGeneratingBounds

variable {m k : ℕ}

theorem hZ_neg' (α : Fin m → ℂ) {z : ℤ} (hz : z < 0) : hZ z α = 0 := by
  simp [hZ, hz]

theorem hZ_nat (α : Fin m → ℂ) (p : ℕ) : hZ (p : ℤ) α = hN p α := by
  simp [hZ]

def cE (α : Fin m → ℂ) (X : ℂ) (k : ℕ) (n : ℕ) (c : Fin k) : ℂ :=
  hZ ((n : ℤ) - (stair k c : ℕ)) α * X ^ (n - stair k c)

def ML (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i c => ∑ n ∈ range L, b i ^ n * cE α X k n c

def KL (k L : ℕ) : Finset (Fin k → ℕ) := (Fintype.piFinset fun _ => range L).filter fun l => ∀ t, l t + stair k t < L

def gF (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (l : Fin k → ℕ) : ℂ :=
  if Antitone l then jt α l * jt b l * X ^ (∑ j, l j) else 0

theorem stair_lt (t : Fin k) : stair k t < k := by
  unfold stair; omega

theorem stair_int (t : Fin k) : ((stair k t : ℕ) : ℤ) = (k : ℤ) - 1 - t := by
  unfold stair; have := t.2; omega

theorem detC (α : Fin m → ℂ) (X : ℂ) (l : Fin k → ℕ) :
    (Matrix.of fun t c : Fin k => cE α X k (l t + stair k t) c).det = X ^ (∑ j, l j) * jt α l := by
  rw [← det_transpose, jt, det_apply, det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_comm (X ^ _), smul_mul_assoc]
  congr 1
  simp only [transpose_apply, of_apply, cE]
  by_cases h : ∀ i, 0 ≤ (l i : ℤ) - i + σ i
  · have he : ∀ i : Fin k, (l i + stair k i - stair k (σ i)) = ((l i : ℤ) - i + σ i).toNat := by
      intro i
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      have hi := h i
      omega
    have hz : ∀ i : Fin k, ((l i + stair k i : ℕ) : ℤ) - (stair k (σ i) : ℕ) = (l i : ℤ) - i + σ i := by
      intro i
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      push_cast
      omega
    simp only [hz, he, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hs : ∑ i : Fin k, ((l i : ℤ) - i + σ i).toNat = ∑ i, l i := by
      have h3 : ∀ i : Fin k, (((l i : ℤ) - i + σ i).toNat : ℤ) = (l i : ℤ) - i + σ i := fun i => Int.toNat_of_nonneg (h i)
      have h4 : ((∑ i : Fin k, ((l i : ℤ) - i + σ i).toNat : ℕ) : ℤ) = ∑ i : Fin k, (l i : ℤ) := by
        push_cast
        simp only [h3, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have h5 : ∑ i : Fin k, ((σ i : ℕ) : ℤ) = ∑ i : Fin k, ((i : ℕ) : ℤ) :=
          Equiv.sum_comp σ (fun i : Fin k => ((i : ℕ) : ℤ))
        rw [h5]; ring
      exact_mod_cast h4
    rw [hs]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hz : ((l i + stair k i : ℕ) : ℤ) - (stair k (σ i) : ℕ) = (l i : ℤ) - i + σ i := by
      have h1 := stair_int i
      have h2 := stair_int (σ i)
      push_cast
      omega
    have h0 : ∏ x : Fin k, hZ ((l x : ℤ) - x + σ x) α = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hZ_neg' α hi)
    have h0' : ∏ x : Fin k, hZ (((l x + stair k x : ℕ) : ℤ) - (stair k (σ x) : ℕ)) α * X ^ (l x + stair k x - stair k (σ x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz, hZ_neg' α hi, zero_mul])
    rw [h0', h0, zero_mul]

theorem ML_eq (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) :
    ML α b X L = (Matrix.of fun i (n : Fin L) => b i ^ (n : ℕ)) * (Matrix.of fun (n : Fin L) c => cE α X k n c) := by
  ext i c
  simp only [ML, of_apply, mul_apply]
  exact (Fin.sum_univ_eq_sum_range (fun n => b i ^ n * cE α X k n c) L).symm

theorem gap {f : Fin k → ℕ} (hf : StrictMono f) : ∀ (d : ℕ) (s t : Fin k), (t : ℕ) = s + d → f s + d ≤ f t := by
  intro d
  induction d with
  | zero =>
    intro s t h
    have : s = t := Fin.ext (by omega)
    subst this; simp
  | succ d ih =>
    intro s t h
    have h1 := ih s ⟨s + d, by omega⟩ rfl
    have h2 : f ⟨s + d, by omega⟩ < f t := hf (Fin.lt_def.2 (by simp only; omega))
    omega

theorem cb_facts {L : ℕ} (C : Fin k → Fin L) (hC : StrictMono fun t => L - 1 - (C t : ℕ)) :
    (∀ t, stair k t ≤ C t) ∧ Antitone fun t => (C t : ℕ) - stair k t := by
  have hlast : ∀ t : Fin k, stair k t ≤ C t := by
    intro t
    have hk : k - 1 < k := by have := t.2; omega
    have h := gap hC (k - 1 - t) t ⟨k - 1, hk⟩ (by simp only; omega)
    have h1 := (C t).2
    have h2 := (C ⟨k - 1, hk⟩).2
    unfold stair
    omega
  refine ⟨hlast, fun s t hst => ?_⟩
  have h := gap hC ((t : ℕ) - s) s t (by have := Fin.le_def.1 hst; omega)
  have h1 := (C t).2
  have h2 := (C s).2
  have h3 := hlast s
  have h4 := hlast t
  have h5 := Fin.le_def.1 hst
  unfold stair at *
  simp only at h ⊢
  omega

theorem finite_id (hA : AltJT) (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (L : ℕ) :
    (ML α b X L).det = altN b (stair k) * ∑ l ∈ KL k L, gF α b X l := by
  classical
  rw [ML_eq, AAInvW.cauchyBinet (fun n : Fin L => L - 1 - (n : ℕ)) (by
    intro x y h
    have := x.2; have := y.2
    exact Fin.ext (by simp only at h; omega))]
  rw [← Finset.sum_filter]
  unfold gF
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij' (fun C _ => fun t => (C t : ℕ) - stair k t)
    (fun l hl => fun t => (⟨l t + stair k t, ((Finset.mem_filter.1 (Finset.mem_filter.1 hl).1).2 t)⟩ : Fin L))
    ?_ ?_ ?_ ?_ ?_
  · intro C hC
    have hC' := (Finset.mem_filter.1 hC).2
    obtain ⟨h1, h2⟩ := cb_facts C hC'
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => ?_⟩, h2⟩
    · have := (C t).2; exact Finset.mem_range.2 (by omega)
    · show (C t : ℕ) - stair k t + stair k t < L
      have := (C t).2; have := h1 t; omega
  · intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    obtain ⟨-, hl3⟩ := Finset.mem_filter.1 hl1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun s t hst => ?_⟩
    have h1 := hl2 (le_of_lt hst)
    have h2 := hl3 s
    have h3 := hl3 t
    have h4 := Fin.lt_def.1 hst
    simp only
    unfold stair at *
    omega
  · intro C hC
    obtain ⟨h1, -⟩ := cb_facts C (Finset.mem_filter.1 hC).2
    funext t
    exact Fin.ext (by simp only; have := h1 t; omega)
  · intro l hl
    funext t
    simp
  · intro C hC
    obtain ⟨h1, -⟩ := cb_facts C (Finset.mem_filter.1 hC).2
    set l : Fin k → ℕ := fun t => (C t : ℕ) - stair k t with hl
    have hCl : ∀ t, (C t : ℕ) = l t + stair k t := fun t => by simp only [hl]; have := h1 t; omega
    have eA : (Matrix.of fun a t => (Matrix.of fun i (n : Fin L) => b i ^ (n : ℕ)) a (C t)) =
        Matrix.of fun i j => b i ^ (l + stair k) j := by
      ext i j; simp only [of_apply, Pi.add_apply, hCl]
    have eB : (Matrix.of fun i t => (Matrix.of fun (n : Fin L) c => cE α X k n c) (C i) t) =
        Matrix.of fun t c : Fin k => cE α X k (l t + stair k t) c := by
      ext i j; simp only [of_apply, hCl]
    rw [eA, eB, detC]
    have hAl := hA k b l
    simp only [altN] at hAl ⊢
    rw [hAl]
    ring

theorem KL_mono : Monotone (KL k) := by
  intro L L' h l hl
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hl
  refine Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => by have := h2 t; omega⟩
  have := Finset.mem_range.1 (Fintype.mem_piFinset.1 h1 t)
  exact Finset.mem_range.2 (by omega)

theorem KL_exh (l : Fin k → ℕ) : ∃ L, l ∈ KL k L := by
  refine ⟨∑ t, l t + k + 1, Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun t => ?_, fun t => ?_⟩⟩
  · have := Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    exact Finset.mem_range.2 (by omega)
  · have := Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have := stair_lt t
    omega

theorem entry_lim (α : Fin m → ℂ) (b : Fin k → ℂ) (X : ℂ) (i c : Fin k) {H : ℂ}
    (hH : HasSum (fun p => hN p α * (b i * X) ^ p) H) :
    Tendsto (fun L => ML α b X L i c) atTop (𝓝 (H * b i ^ stair k c)) := by
  set s := stair k c with hs
  have e : ∀ L, s ≤ L → ML α b X L i c = (∑ p ∈ range (L - s), hN p α * (b i * X) ^ p) * b i ^ s := by
    intro L hL
    simp only [ML, of_apply]
    rw [show L = s + (L - s) by omega, Finset.sum_range_add, Nat.add_sub_cancel_left]
    have h0 : ∑ n ∈ range s, b i ^ n * cE α X k n c = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have := Finset.mem_range.1 hn
      rw [cE, hZ_neg' α (by rw [← hs]; omega), zero_mul, mul_zero]
    rw [h0, zero_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cE, ← hs, show ((s + p : ℕ) : ℤ) - (s : ℕ) = (p : ℤ) by push_cast; ring, hZ_nat,
      show s + p - s = p by omega, pow_add, mul_pow]
    ring
  have h1 : Tendsto (fun L => (∑ p ∈ range (L - s), hN p α * (b i * X) ^ p) * b i ^ s) atTop (𝓝 (H * b i ^ s)) :=
    ((hH.tendsto_sum_nat).comp (tendsto_sub_atTop_nat s)).mul_const _
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop s] with L hL
  exact (e L hL).symm

theorem altN_ne {b : Fin k → ℂ} (hb : Function.Injective b) : altN b (stair k) ≠ 0 := by
  have e : (Matrix.of fun i j => b i ^ stair k j) = (Matrix.vandermonde b).submatrix id Fin.revPerm := by
    ext i j
    simp only [of_apply, submatrix_apply, id_eq, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev, stair]
    congr 1
    omega
  simp only [altN]
  rw [e, det_permute']
  exact mul_ne_zero (by simp) (Matrix.det_vandermonde_ne_zero_iff.2 hb)

end BetaGeneratingBounds

open BetaGeneratingBounds in
theorem beta_generating_of_sum_bound : HGen → SumBd → SchurJT → BetaGen := by
  intro hG hS hJ m k α β X A B hA hB hα hβ hX hd
  have hAlt : AltJT := alternating_jacobi_trudi_of_relation (elementary_relation_of_generating hG)
  set b : Fin k → ℂ := fun j => (β j : ℂ) with hb
  have hbinj : Function.Injective b := fun j j' h => by
    by_contra hne
    exact hd hne h
  have hterm : ∀ l : {l : Fin k → ℕ // Antitone l},
      jt α l.1 * evalAt β (schur fun j => (l.1 j : ℤ)) * X ^ (∑ j, l.1 j) = gF α b X l.1 := by
    intro l
    rw [gF, if_pos l.2, hJ k β l.1]
  obtain ⟨hsum, hbdα⟩ := hS m k A B ‖X‖ hA hB (norm_nonneg _) hX
  have hbdβ := (hS k k B B 0 hB hB le_rfl (by simp)).2 b hβ
  have hsumF : Summable (fun l : {l : Fin k → ℕ // Antitone l} => gF α b X l.1) := by
    refine Summable.of_norm_bounded hsum fun l => ?_
    rw [gF, if_pos l.2, norm_mul, norm_mul, norm_pow]
    have h1 := hbdα α hα l.1
    have h2 := hbdβ l.1
    have h0 : 0 ≤ cjt m A l.1 := (norm_nonneg _).trans h1
    have h0' : 0 ≤ cjt k B l.1 := (norm_nonneg _).trans h2
    gcongr
  have hind : {l : Fin k → ℕ | Antitone l}.indicator (gF α b X) = gF α b X := by
    funext l
    by_cases h : Antitone l
    · simp [Set.indicator, h]
    · simp [Set.indicator, h, gF]
  have hsumAll : Summable (gF α b X) := by
    rw [← hind, ← summable_subtype_iff_indicator]
    exact hsumF
  set Hs : Fin k → ℂ := fun i => ∏ a, (1 - α a * (b i * X))⁻¹ with hHs
  have hH : ∀ i, HasSum (fun p => hN p α * (b i * X) ^ p) (Hs i) := by
    intro i
    refine (hG m α (b i * X) A hA.le hα ?_).1
    rw [norm_mul]
    have h1 : ‖b i‖ ≤ B := hβ i
    calc A * (‖b i‖ * ‖X‖) ≤ A * (B * ‖X‖) := by gcongr
      _ = ‖X‖ * A * B := by ring
      _ < 1 := hX
  have hlimM : Tendsto (fun L => ML α b X L) atTop (𝓝 (Matrix.of fun i c => Hs i * b i ^ stair k c)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun c => entry_lim α b X i c (hH i)
  have hlim1 : Tendsto (fun L => (ML α b X L).det) atTop (𝓝 (Matrix.of fun i c => Hs i * b i ^ stair k c).det) :=
    ((continuous_id.matrix_det).tendsto _).comp hlimM
  have hdet : (Matrix.of fun i c => Hs i * b i ^ stair k c).det = (∏ i, Hs i) * altN b (stair k) := by
    have := det_mul_column Hs (Matrix.of fun i c => b i ^ stair k c)
    simp only [of_apply] at this
    rw [this]
    rfl
  rw [hdet] at hlim1
  have hlim2 : Tendsto (fun L => altN b (stair k) * ∑ l ∈ KL k L, gF α b X l) atTop
      (𝓝 (altN b (stair k) * ∑' l, gF α b X l)) :=
    (hsumAll.hasSum.comp (tendsto_atTop_finset_of_monotone KL_mono KL_exh)).const_mul _
  have hlim1' : Tendsto (fun L => altN b (stair k) * ∑ l ∈ KL k L, gF α b X l) atTop
      (𝓝 ((∏ i, Hs i) * altN b (stair k))) := by
    refine hlim1.congr fun L => ?_
    exact finite_id hAlt α b X L
  have heq := tendsto_nhds_unique hlim2 hlim1'
  have htsum : ∑' l, gF α b X l = ∏ i, Hs i := by
    have hne := altN_ne hbinj
    apply mul_left_cancel₀ hne
    rw [heq, mul_comm]
  have hall : HasSum (gF α b X) (∏ i, Hs i) := htsum ▸ hsumAll.hasSum
  rw [← hind] at hall
  have hsub : HasSum (fun l : {l : Fin k → ℕ // Antitone l} => gF α b X l.1) (∏ i, Hs i) :=
    (hasSum_subtype_iff_indicator).2 hall
  have e2 : (∏ i, Hs i) = ∏ i, ∏ j, (1 - α i * β j * X)⁻¹ := by
    simp only [hHs, hb]
    rw [Finset.prod_comm]
    simp only [mul_assoc]
  rw [← e2]
  convert hsub using 1
  funext l
  exact hterm l

end PositivityTheory.RgJS
