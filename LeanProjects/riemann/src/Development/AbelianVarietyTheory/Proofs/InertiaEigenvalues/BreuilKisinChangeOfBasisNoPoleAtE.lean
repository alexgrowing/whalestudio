import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdealStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.NoPole

theorem mul_eq_smul_one_comm {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (X X' : Matrix (Fin d) (Fin d) R) (c : R) (hc : c ≠ 0)
    (h : X * X' = c • (1 : Matrix (Fin d) (Fin d) R)) : X' * X = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det * X'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : X.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; exact pow_ne_zero _ hc hdet.symm
  have key : X.det • (X' * X) = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc X.det • (X' * X) = (X.adjugate * X) * (X' * X) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = X.adjugate * (X * X') * X := by simp only [Matrix.mul_assoc]
      _ = c • (X.adjugate * X) := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
          rw [Matrix.adjugate_mul, smul_comm]
  ext i j
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hX this

theorem map_smul_ring {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (F : R →+* S) (c : R)
    (M : Matrix a b R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

end GlobalTheory.NoPole

namespace GlobalTheory.NoPole

theorem core {S B : Type*} [CommRing S] [CommRing B] {d m : ℕ} (F G : S →+* B) (E : S) (v : B)
    (ℓ N c₂ k₀ : ℕ) (s : Matrix (Fin d) (Fin m) S) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) S)
    (Q : Matrix (Fin m) (Fin d) S) (Q' : Matrix (Fin d) (Fin m) S)
    (hs : ∀ r i, F E ^ (2 * N) ∣ (ℓ : B) ^ k₀ * (F (s r i) - G (s r i)))
    (hv : v * F E = G E)
    (hX'X : X' * X = ((ℓ : S) ^ c₂ * E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) S))
    (hX : X = (s * Matrix.diagonal fun i => E ^ n i) * Q + E ^ (2 * N) • R)
    (hQ' : (ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i) = X * Q') :
    ∀ i j, F E ^ (2 * N) ∣ (ℓ : B) ^ (k₀ + c₂) * (X'.map F * X.map G) i j := by
  classical
  let π := Ideal.Quotient.mk (Ideal.span {F E ^ (2 * N)})
  let F' := π.comp F
  let G' := π.comp G
  have hFE : F' E ^ (2 * N) = 0 := by
    have h0 : π (F E ^ (2 * N)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simpa only [F', RingHom.comp_apply, map_pow] using h0
  have hGE : G' E = π v * F' E := by
    simp only [G', F', RingHom.comp_apply]; rw [← map_mul, hv]
  have hGE0 : G' E ^ (2 * N) = 0 := by rw [hGE, mul_pow, hFE, mul_zero]
  have e2 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map G' = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map F' := by
    ext r i
    have h : π ((ℓ : B) ^ k₀ * (F (s r i) - G (s r i))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hs r i))
    simp only [map_mul, map_sub, map_pow, map_natCast] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, F', G', RingHom.comp_apply]
    linear_combination (-1 : B ⧸ Ideal.span {F E ^ (2 * N)}) * h
  have hd : (Matrix.diagonal fun i => G' (E ^ n i)) =
      Matrix.diagonal (fun i => F' E ^ n i) * Matrix.diagonal (fun i => π v ^ n i) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; rw [map_pow, hGE, mul_pow]; ring
  have e1 : X.map G' = (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
      (Matrix.diagonal (fun i => π v ^ n i) * Q.map G') := by
    rw [hX, Matrix.map_add _ (map_add G'), map_smul_ring, map_pow, hGE0, zero_smul, add_zero, Matrix.map_mul, Matrix.map_mul,
      Matrix.diagonal_map (map_zero _), hd]
    simp only [Matrix.mul_assoc]
  have e3 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) = X.map F' * Q'.map F' := by
    have : ((ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i)).map F' = (X * Q').map F' := by rw [hQ']
    rw [map_smul_ring, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), map_pow, map_natCast]
      at this
    simpa only [map_pow] using this
  have e4 : X'.map F' * X.map F' = 0 := by
    rw [← Matrix.map_mul, hX'X, map_smul_ring, map_mul, map_pow F' E, hFE, mul_zero, zero_smul]
  have hsuff : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * X.map G') = 0 := by
    have e2' : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) =
        ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) := by
      rw [← Matrix.smul_mul, e2, Matrix.smul_mul]
    rw [e1]
    calc ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * ((s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G')))
        = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by rw [e2']
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = 0 := by
          rw [e3]; simp only [← Matrix.mul_assoc, e4, Matrix.zero_mul, smul_zero]
  intro i j
  have := congrFun (congrFun hsuff i) j
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  simpa [Matrix.mul_apply, map_sum, F', G', π] using this

end GlobalTheory.NoPole

open GlobalTheory.NoPole in

theorem GlobalTheory.seed_nopole : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m N c₂ : ℕ) (s : Matrix (Fin d) (Fin m) (bk.S)) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), (∀ r i, (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)))) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → X = (s * Matrix.diagonal fun i => bk.E ^ n i) * Q + bk.E ^ (2 * N) • R → (l : bk.S) ^ c₂ • (s * Matrix.diagonal fun i => bk.E ^ n i) = X * Q' → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) := by
  intro l _ K bk d m N c₂ s n X X' R Q Q' hs hXX' hX hQ' B f g
  classical
  have hl0 : (l : bk.S) ≠ 0 := by
    intro h0
    have h1 : bk.str.symm (Ideal.Quotient.mk _ (l : bk.S)) = 0 := by rw [h0, map_zero, map_zero]
    rw [map_natCast, map_natCast] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hc : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
  have hX'X := mul_eq_smul_one_comm X X' _ hc hXX'
  choose k hk using fun (p : Fin d × Fin m) => hs p.1 p.2 B f g
  obtain ⟨v, hv⟩ : ∃ v, v * BK.hf f bk.E = BK.hf g bk.E := by
    have h1 := (GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B f g).2.2
    have h2 := (GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal l K bk B g f).2.2
    have : BK.hf g bk.E ∈ B.I := by rw [h2]; exact Ideal.mem_span_singleton_self _
    rw [h1] at this
    exact Ideal.mem_span_singleton'.1 this
  refine ⟨Finset.univ.sup k + c₂, GlobalTheory.NoPole.core (BK.hf f) (BK.hf g) bk.E v l N c₂ _ s n X X' R Q Q' ?_ hv
    hX'X hX hQ'⟩
  intro r i
  have hle : k (r, i) ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (hk (r, i)) _
