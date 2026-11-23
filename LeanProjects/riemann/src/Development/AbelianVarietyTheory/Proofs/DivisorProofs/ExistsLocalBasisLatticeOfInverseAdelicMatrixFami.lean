import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatBasis

variable {K : Type} [Field K] [NumberField K]

theorem exists_notMem_mul_le (P u : HeightOneSpectrum (𝓞 K)) (y : K) (h : u ≠ P ∨ u.valuation K y ≤ 1) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ u.valuation K ((s : K) * y) ≤ 1 := by
  have h1 : (1 : 𝓞 K) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  by_cases hy : u.valuation K y ≤ 1
  · exact ⟨1, h1, by simpa using hy⟩
  have hne : u ≠ P := h.resolve_right hy
  have hy0 : u.valuation K y ≠ 0 := fun h0 => hy (by rw [h0]; exact zero_le_one)
  have hnle : ¬ u.asIdeal ≤ P.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
  obtain ⟨π, hπu, hπP⟩ := SetLike.not_le_iff_exists.1 hnle
  have hlt : u.valuation K (π : K) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem u π).2 hπu
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hy0)⁻¹
  refine ⟨π ^ N, fun hm => hπP (P.isPrime.mem_of_pow_mem N hm), ?_⟩
  have e : ((π ^ N : 𝓞 K) : K) = (π : K) ^ N := by simp
  rw [e, map_mul, map_pow]
  have hN' : u.valuation K (π : K) ^ N ≤ (u.valuation K y)⁻¹ := by simpa using hN.le
  calc _ ≤ (u.valuation K y)⁻¹ * u.valuation K y := by gcongr
    _ = 1 := inv_mul_cancel₀ hy0

theorem exists_denom_notMem {ι : Type} [Fintype ι] (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (h : {w | ¬ IntAt w (B w)}.Finite) (P : HeightOneSpectrum (𝓞 K)) (hP : IntAt P (B P)) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ ∀ w, IntAt w ((s : K) • B w) := by
  classical
  haveI : Fintype {w | ¬ IntAt w (B w)} := h.fintype
  have hex : ∀ p : {w | ¬ IntAt w (B w)} × ι × ι, ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      p.1.1.valuation K ((s : K) * B p.1.1 p.2.1 p.2.2) ≤ 1 := fun p =>
    exists_notMem_mul_le P _ _ (Or.inl fun e => p.1.2 (by rw [e]; exact hP))
  choose s hs hv using hex
  refine ⟨∏ p, s p, fun hm => ?_, fun w i j => ?_⟩
  · obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact hs p hp
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hw i j)
  · rw [Matrix.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨w, hw⟩, i, j))]
    have e : ∀ a b : 𝓞 K, ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := fun a b => by simp
    rw [e, mul_assoc, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hv (⟨w, hw⟩, i, j))

theorem intAt_mul {ι : Type} [Fintype ι] {w : HeightOneSpectrum (𝓞 K)} {M N : Matrix ι ι K}
    (hM : IntAt w M) (hN : IntAt w N) : IntAt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i k) (hN k j)

theorem finite_not_intAt {ι : Type} [Fintype ι] (M : Matrix ι ι K) :
    {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w M}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => HeightOneSpectrum.Support.finite (𝓞 K) (M p.1 p.2)).subset ?_
  intro w hw
  simp only [IntAt, Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨i, j, hij⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), hij⟩

theorem exists_locBasis_inv : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  intro K _ _ n A hA P
  classical
  obtain ⟨hdet, hfin⟩ := hA
  have hu : IsUnit (A P).det := isUnit_iff_ne_zero.2 (hdet P)
  have hone : ∀ (w : HeightOneSpectrum (𝓞 K)) (j k : Fin n), w.valuation K ((Pi.single j 1 : Fin n → K) k) ≤ 1 :=
    fun w j k => by by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  obtain ⟨s, hs, hint⟩ := exists_denom_notMem (fun w => A w * (A P)⁻¹)
    ((hfin.union (finite_not_intAt (A P)⁻¹)).subset fun w hw => by
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
      exact hw (intAt_mul hn.1.1 hn.2)) P (by
      intro i j
      rw [Matrix.mul_nonsing_inv _ hu]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  have hs0 : (s : K) ≠ 0 := fun h0 => hs (by
    have : s = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem)
  refine ⟨s, hs, fun j w i => ?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    exact GlobalTheory.LocMatLat.mulVec_le w (hint w) (hone w j) i
  · have h1 : LinearIndependent K (A P)⁻¹.col :=
      Matrix.linearIndependent_cols_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))
    have h2 : LinearIndependent K (fun j => (s : K) • (A P)⁻¹.col j) :=
      h1.units_smul fun _ => Units.mk0 (s : K) hs0
    convert h2 using 3 with j
    simp
  · have hex := fun j => P.exists_primeCompl_mul_eq_of_integer _ (hx P j)
    choose c d hcd using hex
    have hd : (∏ j, (d j : 𝓞 K)) ∉ P.asIdeal := fun hm => by
      obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact (d p).2 hp
    refine ⟨(∏ j, (d j : 𝓞 K)) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hd hs, ?_⟩
    have hx' : x = ∑ j, (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) := by
      simp_rw [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec]
    rw [hx', Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have e : ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * (d j : 𝓞 K) * s) •
        (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) =
        ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * c j) •
          ((s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
      rw [← algebraMap_smul K, ← algebraMap_smul K (_ * c j), smul_smul, smul_smul, map_mul, map_mul, map_mul,
        ← hcd j]
      congr 1
      change _ = _ * algebraMap (𝓞 K) K s
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.LocMatBasis
