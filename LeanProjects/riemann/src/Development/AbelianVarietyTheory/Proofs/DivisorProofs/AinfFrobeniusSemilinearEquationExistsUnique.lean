import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionExistsUniqueSubMatrixFrobeniusEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorExistsUniqueSubMatrixFrobeniusEqStatement

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WSolve

theorem nilp_mod_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)], v.Integers O → ∀ x : O, ¬IsUnit x → IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) x) := by
  intro p _ C _ _ v O _ _ hp hv x hx
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) (fun h => hx (hv.isUnit_iff_valuation_eq_one.2 h))
  have hp0 : 0 < v (algebraMap O C (p : O)) := by
    rw [map_natCast]
    exact (Valuation.pos_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hp0 hx1
  refine ⟨k, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [hv.dvd_iff_le, map_pow, map_pow]
  exact hk.le

theorem semilin_nil : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent

theorem perf_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq

theorem witt_solve : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq

theorem iter_map {T T' : Type} [CommRing T] [CommRing T'] {ι : Type} [Fintype ι] (f : T →+* T')
    (σ : T →+* T) (σ' : T' →+* T') (hf : ∀ x, f (σ x) = σ' (f x)) (M : Matrix ι ι T) (k : ℕ)
    (w : ι → T) :
    (fun u : ι → T' => (M.map f).mulVec fun j => σ' (u j))^[k] (fun j => f (w j)) =
      fun i => f ((fun u : ι → T => M.mulVec fun j => σ (u j))^[k] w i) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    funext i
    simp only [← hf]
    exact (RingHom.map_mulVec f M _ i).symm

theorem coeff_nil {S : Type} [CommRing S] {p : ℕ} [Fact p.Prime] [CharP S p] (y : Perfection S p)
    (h : IsNilpotent (Perfection.coeff S p 0 y)) (n : ℕ) : IsNilpotent (Perfection.coeff S p n y) := by
  have e : ∀ n, Perfection.coeff S p n y ^ (p ^ n) = Perfection.coeff S p 0 y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, Perfection.coeff_pow_p', ih]
  exact IsNilpotent.of_pow (m := p ^ n) (by rw [e]; exact h)

theorem key (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Ainf p O)) (N : ℕ)
    (hN : ∀ j i, IsNilpotent (Ideal.Quotient.mk (Ideal.span {(p : O)}) (WittVector.fontaineTheta O p
      ((fun w : ι → Ainf p O => M.mulVec fun k => WittVector.frobenius (w k))^[N] (Pi.single j 1) i)))) :
    ∀ c : ι → Ainf p O, ∃! v : ι → Ainf p O, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  apply witt_solve p (PreTilt O p) ι M
  apply perf_solve p (ModP O p) ι (M.map WittVector.constantCoeff)
  intro n
  apply semilin_nil p (ModP O p) ι _ N
  intro j i
  have e1 : (Pi.single j 1 : ι → ModP O p) =
      fun k => Perfection.coeff (ModP O p) p n ((Pi.single j 1 : ι → PreTilt O p) k) := by
    funext k; by_cases h : k = j
    · subst h; simp only [Pi.single_eq_same]; exact (map_one _).symm
    · simp only [Pi.single_eq_of_ne h]; exact (map_zero _).symm
  have e2 : (Pi.single j 1 : ι → PreTilt O p) =
      fun k => WittVector.constantCoeff ((Pi.single j 1 : ι → Ainf p O) k) := by
    funext k; by_cases h : k = j
    · subst h; simp
    · simp [h]
  have h1 := congrFun (iter_map (T := PreTilt O p) (Perfection.coeff (ModP O p) p n)
    (frobenius (PreTilt O p) p) (frobenius (ModP O p) p) (fun x => by rw [frobenius_def, frobenius_def]; exact map_pow (Perfection.coeff (ModP O p) p n) x p)
    (M.map WittVector.constantCoeff) N (Pi.single j 1)) i
  have h2 := iter_map WittVector.constantCoeff WittVector.frobenius
    (frobenius (PreTilt O p) p) (fun x => by simp [frobenius_def, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP]) M N (Pi.single j 1)
  rw [e1]
  erw [h1]
  rw [e2, h2]
  apply coeff_nil
  have := hN j i
  rw [WittVector.mk_fontaineTheta] at this
  exact this

theorem frobenius_mu_eq (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) =
      (∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i) * Sandwich.mu ε := by
  have h : WittVector.frobenius (WittVector.teichmuller p ε) = (WittVector.teichmuller p ε) ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [Sandwich.mu, map_sub, map_one, h, geom_sum_mul]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (M : Matrix ι ι (Ainf p O)), IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) M → (∀ c : ι → Ainf p O, ∃ v : ι → Ainf p O, ∀ i, v i - M.mulVec (fun j => WittVector.frobenius (v j)) i = c i) ∧ ∀ v : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ v i - M.mulVec (fun j => WittVector.frobenius (v j)) i) → ∀ i, Sandwich.mu ε ∣ v i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ M hM
  classical
  obtain ⟨N, hN⟩ := hM
  have hK := key p O ι M N (fun j i => nilp_mod_p p C v O hv _ (hN _ i))
  refine ⟨fun c => ?_, ?_⟩
  · obtain ⟨x, hx, -⟩ := hK c
    exact ⟨x, fun i => congrFun hx i⟩
  intro w hw
  choose u hu using hw
  have hφμ := frobenius_mu_eq p O ε
  set s : Ainf p O := ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε) ^ i with hs
  have h1 : ε.untilt = 1 := by simpa [zeta] using hε.zeta_zero
  have hθs : WittVector.fontaineTheta O p s = p := by
    simp [hs, map_sum, map_pow, WittVector.fontaineTheta_teichmuller, h1]
  have hK' := key p O ι (s • M) 1 (fun j i => by
    have e : (fun k => WittVector.frobenius ((Pi.single j 1 : ι → Ainf p O) k)) = Pi.single j 1 := by
      funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [Function.iterate_one, e, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.smul_apply, smul_eq_mul, map_mul, hθs]
    rw [← map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))]
    exact IsNilpotent.zero)
  obtain ⟨w', hw', -⟩ := hK' u
  have hz : (w - Sandwich.mu ε • w') - M.mulVec (fun k => WittVector.frobenius ((w - Sandwich.mu ε • w') k)) = 0 := by
    funext i
    have a := hu i
    have b := congrFun hw' i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      map_sub, map_mul, hφμ, Pi.zero_apply] at a b ⊢
    have hsum : ∑ x, M i x * (WittVector.frobenius (w x) - s * Sandwich.mu ε * WittVector.frobenius (w' x)) =
        ∑ x, M i x * WittVector.frobenius (w x) - Sandwich.mu ε * ∑ x, s * M i x * WittVector.frobenius (w' x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsum]
    linear_combination a - Sandwich.mu ε * b
  have h0 : (0 : ι → Ainf p O) - M.mulVec (fun k => WittVector.frobenius ((0 : ι → Ainf p O) k)) = 0 := by
    funext i; simp [Matrix.mulVec, dotProduct]
  have := (hK 0).unique hz h0
  intro i
  refine ⟨w' i, ?_⟩
  have := congrFun this i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.WSolve
