import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.GaloisClause
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CuspTwist

open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES PI.GreenLabelMapW IntermediateField

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem algebraMap_det_eq_pow {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (γ : Matrix ι ι K).charpoly) {z : AlgebraicClosure K}
    (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) :
    algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) =
      z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmin : (γ : Matrix ι ι K).charpoly = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hdeg : (minpoly K z).natDegree = Fintype.card ι := by
    rw [← hmin, Matrix.charpoly_natDegree_eq_dim]
  let pb := IntermediateField.adjoin.powerBasis hint
  have hnorm : Algebra.norm K pb.gen = Matrix.det (γ : Matrix ι ι K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, Matrix.det_eq_sign_charpoly_coeff, hmin]
    have h1 : pb.dim = Fintype.card ι := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have h2 : pb.gen = IntermediateField.AdjoinSimple.gen K z := IntermediateField.adjoin.powerBasis_gen hint
    rw [h1, h2, IntermediateField.minpoly_gen]
  haveI : FiniteDimensional K K⟮z⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮z⟯ := Module.finite_of_finite K
  have hfr : Module.finrank K K⟮z⟯ = Fintype.card ι := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have h3 := FiniteField.algebraMap_norm_eq_pow_sum (K := K) (L := K⟮z⟯) (x := pb.gen)
  rw [hnorm, hfr, Nat.card_eq_fintype_card] at h3
  have h5 : ((pb.gen ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i : K⟮z⟯) :
      AlgebraicClosure K) = z ^ ∑ i ∈ Finset.range (Fintype.card ι), Fintype.card K ^ i := by
    rw [IntermediateField.coe_pow, IntermediateField.adjoin.powerBasis_gen hint,
      IntermediateField.AdjoinSimple.coe_gen]
  rw [← h5, ← h3]
  rfl

theorem gen_one_pow_eq_det (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 1 ≤ Fintype.card ι) (γ : GL ι K) (hγ : Irreducible (γ : Matrix ι ι K).charpoly)
    {z : AlgebraicClosure K} (hz : aeval z (γ : Matrix ι ι K).charpoly = 0) {m : ℕ}
    (hm : Cv.gen (Fintype.card ι) ^ m = z) :
    Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix ι ι K)) := by
  have hn := Cv.gen_norm 1 (Fintype.card ι) le_rfl hι
  rw [one_mul, pow_one] at hn
  rw [algebraMap_det_eq_pow γ hγ hz, ← hn, ← hm, ← pow_mul, ← pow_mul,
    Nat.geomSum_eq Fintype.one_lt_card, mul_comm]

theorem twist_clause (Cv : LabelConv K) (hC : CuspParam K Cv) (d : ℕ)
    (τ τ' : FDRep ℂ (GL (Fin d) K)) (x : K) (hd : 1 ≤ d) (hx : x ≠ 0) (hs : Simple τ)
    (hc : IsCuspidal K τ) (hs' : Simple τ') (hc' : IsCuspidal K τ')
    (htr : ∀ (γ : GL (Fin d) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin d) (Fin d) K)) →
      LinearMap.trace ℂ τ' (τ'.ρ γ) =
        Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m * LinearMap.trace ℂ τ (τ.ρ γ)) :
    rootsBar K (greenLab Cv d τ') =
      (rootsBar K (greenLab Cv d τ)).map (· * algebraMap K (AlgebraicClosure K) x) := by
  set xb := algebraMap K (AlgebraicClosure K) x with hxb
  have hxb0 : xb ≠ 0 := by
    rw [hxb]; exact (map_ne_zero_iff _ (algebraMap K (AlgebraicClosure K)).injective).2 hx
  obtain ⟨hm, hi, hX, hdeg, hval⟩ := greenLab_spec Cv hC hd hs hc
  have hdeg' : (greenLab Cv d τ).natDegree = d := by rw [hdeg, Fintype.card_fin]
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) (greenLab Cv d τ)
    (by rw [degree_eq_natDegree hm.ne_zero, hdeg']; exact_mod_cast (show d ≠ 0 by omega))
  have hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : AlgebraicClosure K),
      σ y * xb = σ (y * xb) := fun σ y => by rw [map_mul, hxb, AlgEquiv.commutes]
  have hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ (greenLab Cv d τ) = 0 →
      aeval r₂ (greenLab Cv d τ) = 0 → r₁ * xb = r₂ * xb → r₁ = r₂ :=
    fun _ _ _ _ h => mul_right_cancel₀ hxb0 h
  have hint : IsIntegral K (w * xb) := Algebra.IsIntegral.isIntegral _
  have hxq : ∀ i : ℕ, xb ^ (Fintype.card K ^ i) = xb := fun i => by
    rw [hxb, ← map_pow, FiniteField.pow_card_pow]
  have hlab : HasCuspLabel Cv τ' (minpoly K (w * xb)) := by
    refine ⟨minpoly.monic hint, minpoly.irreducible hint, ?_, ?_, ?_⟩
    · intro h
      have h0 := minpoly.aeval K (w * xb)
      rw [h, aeval_X] at h0
      exact mul_ne_zero (root_ne_zero hm hi hX hw) hxb0 h0
    · rw [natDegree_minpoly_eq hm hi hw (fun y => y * xb) hf hinj, hdeg]
    · intro y hy γ hγ z hz m hm'
      obtain ⟨r, hr, rfl⟩ := (conj_roots hm hi hw (fun y => y * xb) hf y).1 hy
      have hι : 1 ≤ Fintype.card (Fin d) := by rw [Fintype.card_fin]; exact hd
      rw [htr γ m (gen_one_pow_eq_det Cv hι γ hγ hz hm'), hval r hr γ hγ z hz m hm',
        mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have e : Cv.ι xb ^ (m * Fintype.card K ^ i) = Cv.ι xb ^ m := by
        rw [mul_comm, pow_mul, ← map_pow, hxq i]
      rw [map_mul, mul_pow, e, mul_comm]
  rw [greenLab_eq Cv hC hd hs' hc' hlab]
  exact aroots_eq_map hm hi hw (fun y => y * xb) hf hinj

theorem exists_labelMap_twist_cuspLabel :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv K),
      Formalism.IrreducibleCountingLemmas.TYPES.CuspParam K C → ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap K C,
        Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
          ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ d → CategoryTheory.Simple τ →
            Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel C τ (O.lab d τ) := by
  intro K _ _ _ Cv hC
  let O : LabelMap K Cv :=
    { lab := greenLab Cv
      lab_iso := greenLab_iso Cv
      lab_spec := fun d τ hd hs hc => by
        obtain ⟨h1, h2, h3, h4, -⟩ := greenLab_spec Cv hC hd hs hc
        exact ⟨h1, h2, h3, by rw [h4, Fintype.card_fin]⟩
      lab_inj := fun d τ τ' hd hs hc hs' hc' h =>
        (hC d hd).2.2 τ τ' (greenLab Cv d τ) hs hc hs' hc' (greenLab_spec Cv hC hd hs hc)
          (by rw [h]; exact greenLab_spec Cv hC hd hs' hc')
      lab_one := fun τ x hs hx htr => greenLab_one Cv hC τ x hs hx htr }
  refine ⟨O, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro d α a hα τ τ' hd hs hc hs' hc' htr
    exact galois_clause Cv hC d α a hα τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' hd hs hc hs' hc' htr
    exact dual_clause Cv hC d τ τ' hd hs hc hs' hc' htr
  · intro d τ τ' x hd hx hs hc hs' hc' htr
    exact twist_clause Cv hC d τ τ' x hd hx hs hc hs' hc' htr
  · intro d τ hd hs hc
    exact greenLab_spec Cv hC hd hs hc

end GlobalTheory.CuspTwist
