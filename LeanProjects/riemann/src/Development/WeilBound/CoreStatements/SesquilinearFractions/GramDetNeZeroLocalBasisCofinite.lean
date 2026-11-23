import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqSesquilinearSkewHermitianStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SesqUnimodularDualStatement
import Development.WeilBound.CoreStatements.SesquilinearFractions.DTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem gram_det_ne_zero_local_basis_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (I : Type) [Fintype I] [DecidableEq I] (e : I → D.La), Fintype.card I = D.p + D.q → LinearIndependent (𝓞 E) e → (gramE D e).det ≠ 0 ∧ {ℓ : Nat.Primes | ¬ IsLocBasis (𝓞 E) ℓ e}.Finite := by
  intro E _ _ _ H D I _ _ e hcard he
  classical
  have := D.fin
  have := D.proj
  obtain ⟨n, hn, hsp⟩ := exists_nsmul_mem_span_full_family e (hcard.trans D.rank.symm) he
  refine ⟨fun hdet => ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (Finset.univ.image v)
    choose u hu using fun m => hc (v m) (Finset.mem_image_of_mem v (Finset.mem_univ m))
    have hc0 : ((c : 𝓞 E) : E) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero c
    have huv : ∀ m, (u m : E) = (c : 𝓞 E) * v m := fun m => by
      rw [show ((u m : 𝓞 E) : E) = algebraMap (𝓞 E) E (u m) from rfl, hu m, Algebra.smul_def]
    set z : D.La := ∑ i, u i • e i with hz

    have hzj : ∀ j, sesq D z (e j) = 0 := by
      intro j
      rw [hz, sesq_sum_smul_left]
      have hvj := congrFun hv j
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, gramE, Matrix.of_apply] at hvj
      simp_rw [huv]
      calc ∑ i, (c : 𝓞 E) * v i * sesq D (e i) (e j) = (c : 𝓞 E) * ∑ i, v i * sesq D (e i) (e j) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [hvj, mul_zero]
    have hz0 : ∀ x, sesq D x z = 0 := by
      intro x
      obtain ⟨S, hS⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hsp x)
      have h1 : sesq D z (n • x) = (n : E) * sesq D z x := by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E), (GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.1]; simp
      have h2 : sesq D z (n • x) = 0 := by
        rw [← hS, sesq_sum_smul_right]
        exact Finset.sum_eq_zero fun j _ => by rw [hzj j, mul_zero]
      have h3 : sesq D z x = 0 := by
        rw [h2] at h1
        exact (mul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast hn.ne')
      rw [(GlobalTheory.T.sesq_sesquilinear_skew_hermitian E H D).2.2.2.2.2.1 z x, h3, map_zero, neg_zero]
    have hzz : z = 0 := (GlobalTheory.T.sesq_unimodular_dual E H D).1 z hz0
    have hu0 := (Fintype.linearIndependent_iff.1 he) u (by rw [← hz]; exact hzz)
    apply hv0
    funext m
    have : (c : 𝓞 E) * v m = 0 := by rw [← huv, hu0 m]; simp
    simpa [hc0] using this
  · refine (Set.finite_le_nat n).preimage (f := fun ℓ : Nat.Primes => (ℓ : ℕ))
      (fun a _ b _ h => Subtype.ext h) |>.subset ?_
    intro ℓ hℓ
    simp only [Set.mem_setOf_eq] at hℓ ⊢
    by_contra hlt
    apply hℓ
    refine ⟨he, n, fun hd => hlt ?_, hsp⟩
    exact Nat.le_of_dvd hn hd

end PositivityTheory.Xgf
