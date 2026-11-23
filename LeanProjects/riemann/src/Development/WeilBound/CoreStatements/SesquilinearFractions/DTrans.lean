import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
import Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsNsmulMemSpanFullFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem sesq_zero_left' (y : D.La) : sesq D 0 y = 0 := by
  have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem sesq_sum_smul_left {I : Type} [Fintype I] (c : I → 𝓞 E) (e : I → D.La) (y : D.La) :
    sesq D (∑ i, c i • e i) y = ∑ i, (c i : E) * sesq D (e i) y := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [sesq_zero_left']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.1, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1, ih]

theorem sesq_zero_right' (x : D.La) : sesq D x 0 = 0 := by
  have h := (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1 x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem sesq_sum_smul_right {I : Type} [Fintype I] (c : I → 𝓞 E) (e : I → D.La) (x : D.La) :
    sesq D x (∑ i, c i • e i) = ∑ i, IsCMField.complexConj E (c i : E) * sesq D x (e i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [sesq_zero_right']
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.1, (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1, ih]

end

theorem exists_transition_matrix_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (x e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → ∃ T : Matrix I I E, IsTransition D x e T ∧ gramE D x = T * gramE D e * (T.map (IsCMField.complexConj E)).transpose ∧ (LinearIndependent (𝓞 E) x → T.det ≠ 0) ∧ ∃ (n : ℕ) (S : Matrix I I (𝓞 E)), 0 < n ∧ (∀ a, n • x a = ∑ b, S a b • e b) ∧ ∀ a b, (S a b : E) = n * T a b := by
  intro E _ _ _ H D I _ _ x e hcard he
  classical
  have := D.fin
  have := D.proj
  obtain ⟨n, hn, hsp⟩ := exists_nsmul_mem_span_full_family e (hcard.trans D.rank.symm) he
  have hS : ∀ a, ∃ c : I → 𝓞 E, ∑ b, c b • e b = n • x a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hsp (x a))
  choose S hSx using hS
  have hn0 : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  set T : Matrix I I E := Matrix.of fun a b => (S a b : E) / n with hT
  have hST : ∀ a b, (S a b : E) = n * T a b := fun a b => by
    simp only [hT, Matrix.of_apply]; field_simp
  have hsn : ∀ (z y : D.La), sesq D (n • z) y = (n : E) * sesq D z y := fun z y => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.1]; simp
  have hsn' : ∀ (z y : D.La), sesq D z (n • y) = (n : E) * sesq D z y := fun z y => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]; simp
  have htrans : IsTransition D x e T := by
    intro m y
    have h := congrArg (fun z => sesq D z y) (hSx m)
    rw [sesq_sum_smul_left, hsn] at h
    apply mul_left_cancel₀ hn0
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hST]; ring
  have hcol : ∀ i k, sesq D (e i) (x k) = ∑ j, IsCMField.complexConj E (T k j) * sesq D (e i) (e j) := by
    intro i k
    have h := congrArg (fun z => sesq D (e i) z) (hSx k)
    rw [sesq_sum_smul_right, hsn'] at h
    apply mul_left_cancel₀ hn0
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hST, map_mul, map_natCast]; ring
  refine ⟨T, htrans, ?_, ?_, n, S, hn, fun a => (hSx a).symm, hST⟩
  · ext m k
    simp only [gramE, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [htrans m (x k)]
    simp_rw [hcol, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro hx hdet
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image v)
    choose w hw using fun m => hc (v m) (Finset.mem_image_of_mem v (Finset.mem_univ m))
    have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by
      exact_mod_cast nonZeroDivisors.coe_ne_zero c
    have hwv : ∀ m, (w m : E) = (c : 𝓞 E) * v m := fun m => by
      rw [show ((w m : 𝓞 E) : E) = algebraMap (𝓞 E) E (w m) from rfl, hw m, Algebra.smul_def]
    have hsum : ∑ m, (w m * (n : 𝓞 E)) • x m = 0 := by
      have e1 : ∑ m, (w m * (n : 𝓞 E)) • x m = ∑ b, (∑ m, w m * S m b) • e b := by
        simp_rw [mul_smul, Nat.cast_smul_eq_nsmul, ← hSx, Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
      rw [e1]
      refine Finset.sum_eq_zero fun b _ => ?_
      have : (∑ m, w m * S m b : 𝓞 E) = 0 := by
        apply RingOfIntegers.coe_injective (K := E)
        push_cast
        simp_rw [hwv, hST]
        have hvb := congrFun hv b
        simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hvb
        calc ∑ m, (c : 𝓞 E) * v m * (n * T m b) = (c : 𝓞 E) * n * ∑ m, v m * T m b := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
          _ = 0 := by rw [hvb, mul_zero]
          _ = ((0 : 𝓞 E) : E) := by simp
      rw [this, zero_smul]
    have hz := (Fintype.linearIndependent_iff.1 hx) _ hsum
    apply hv0
    funext m
    have hm := hz m
    have hw0 : w m = 0 := by
      rcases mul_eq_zero.1 hm with h | h
      · exact h
      · exact absurd h (by exact_mod_cast hn.ne')
    have : (c : 𝓞 E) * v m = 0 := by rw [← hwv, hw0]; simp
    simpa [hc0] using this

end PositivityTheory.Xgf
