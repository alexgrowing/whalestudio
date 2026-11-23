import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.RootPowCard

open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace PI.GreenLabelMapW

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem hasCuspLabel_of_trace (Cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ τ' : FDRep ℂ (GL ι K)}
    (h : ∀ γ, LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ))
    {P : K[X]} (hP : HasCuspLabel Cv τ P) : HasCuspLabel Cv τ' P := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  exact ⟨h1, h2, h3, h4, fun x hx γ hγ z hz m hm => (h γ).trans (h5 x hx γ hγ z hz m hm)⟩

theorem trace_of_iso {ι : Type} [Fintype ι] [DecidableEq ι] {τ τ' : FDRep ℂ (GL ι K)}
    (e : τ ≅ τ') (γ : GL ι K) :
    LinearMap.trace ℂ τ' (τ'.ρ γ) = LinearMap.trace ℂ τ (τ.ρ γ) := by
  rw [FDRep.Iso.conj_ρ e γ, LinearMap.trace_conj']

def greenLab (Cv : LabelConv K) (d : ℕ) (τ : FDRep ℂ (GL (Fin d) K)) : K[X] :=
  Classical.epsilon (fun P => HasCuspLabel Cv τ P)

theorem greenLab_iso (Cv : LabelConv K) (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K))
    (h : Nonempty (τ ≅ τ')) : greenLab Cv d τ = greenLab Cv d τ' := by
  obtain ⟨e⟩ := h
  unfold greenLab
  congr 1
  funext P
  exact propext ⟨hasCuspLabel_of_trace Cv (trace_of_iso e),
    hasCuspLabel_of_trace Cv (fun γ => (trace_of_iso e γ).symm)⟩

theorem greenLab_spec (Cv : LabelConv K) (hC : CuspParam K Cv) {d : ℕ} (hd : 1 ≤ d)
    {τ : FDRep ℂ (GL (Fin d) K)} (hs : Simple τ) (hc : IsCuspidal K τ) :
    HasCuspLabel Cv τ (greenLab Cv d τ) := by
  unfold greenLab
  exact Classical.epsilon_spec (((hC d hd).1 τ hs hc).1.exists)

theorem greenLab_eq (Cv : LabelConv K) (hC : CuspParam K Cv) {d : ℕ} (hd : 1 ≤ d)
    {τ : FDRep ℂ (GL (Fin d) K)} (hs : Simple τ) (hc : IsCuspidal K τ) {P : K[X]}
    (hP : HasCuspLabel Cv τ P) : greenLab Cv d τ = P := by
  exact ((hC d hd).1 τ hs hc).1.unique (greenLab_spec Cv hC hd hs hc) hP

theorem isCuspidal_fin_one (τ : FDRep ℂ (GL (Fin 1) K)) : IsCuspidal K τ := by
  intro s b hb hs
  exfalso
  have h := Fintype.card_le_of_surjective b hb
  simp only [Fintype.card_fin] at h
  omega

theorem charpoly_fin_one (A : Matrix (Fin 1) (Fin 1) K) :
    A.charpoly = X - Polynomial.C (A 0 0) := by
  rw [Matrix.charpoly, Matrix.det_unique, Fin.default_eq_zero, Matrix.charmatrix_apply_eq]

theorem greenLab_one (Cv : LabelConv K) (hC : CuspParam K Cv) (τ : FDRep ℂ (GL (Fin 1) K))
    (x : K) (hs : Simple τ) (hx : x ≠ 0)
    (htr : ∀ (γ : GL (Fin 1) K) (m : ℕ),
      Cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = Cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m) :
    greenLab Cv 1 τ = X - Polynomial.C x := by
  apply greenLab_eq Cv hC le_rfl hs (isCuspidal_fin_one τ)
  have hxX : X - Polynomial.C x ≠ X := by
    intro h
    apply hx
    have h' := congrArg (fun P : K[X] => P.coeff 0) h
    simpa using h'
  refine ⟨monic_X_sub_C x, irreducible_X_sub_C x, hxX, by simp, ?_⟩
  intro x' hx' γ _ z hz m hm
  have hx'' : x' = algebraMap K (AlgebraicClosure K) x := by
    simpa [sub_eq_zero] using hx'
  have hz' : z = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) := by
    rw [charpoly_fin_one] at hz
    have hz2 : z = algebraMap K (AlgebraicClosure K) ((γ : Matrix (Fin 1) (Fin 1) K) 0 0) := by
      simpa [sub_eq_zero] using hz
    rw [hz2, Matrix.det_unique, Fin.default_eq_zero]
  simp only [Fintype.card_fin, Nat.sub_self, pow_zero, one_mul, Finset.sum_range_one, mul_one]
  rw [hx'', htr γ m (hm.trans hz')]

theorem gen_pow (Cv : LabelConv K) {d : ℕ} (hd : 1 ≤ d) :
    Cv.gen d ^ (Fintype.card K ^ d - 1) = 1 := by
  rw [← Cv.gen_order d hd]
  exact pow_orderOf_eq_one _

theorem card_pow_sub_one_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Fintype.card K ^ d - 1 := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have h2 : 2 ≤ Fintype.card K ^ d := le_trans hq (Nat.le_self_pow (by omega) _)
  omega

theorem gen_ne_zero (Cv : LabelConv K) {d : ℕ} (hd : 1 ≤ d) : Cv.gen d ≠ 0 := by
  intro h
  have h1 := gen_pow Cv hd
  have h2 := card_pow_sub_one_pos (K := K) hd
  rw [h, zero_pow (by omega)] at h1
  exact zero_ne_one h1

theorem root_inv {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    aeval z⁻¹ (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) = 0 := by
  classical
  have key : ∀ (M : Matrix ι ι K) (w : AlgebraicClosure K),
      aeval w M.charpoly = (Matrix.scalar ι w - M.map (algebraMap K (AlgebraicClosure K))).det := by
    intro M w
    rw [← Polynomial.eval_map_algebraMap, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  have hAB : ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) *
      (γ : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp
  rw [key] at hz ⊢
  have hs : ∀ w : AlgebraicClosure K, Matrix.scalar ι w = w • (1 : Matrix ι ι (AlgebraicClosure K)) := by
    intro w
    simp [Matrix.smul_one_eq_diagonal]
  have hmat : Matrix.scalar ι z⁻¹ - ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) =
      -(z⁻¹ • ((γ⁻¹ : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) *
        (Matrix.scalar ι z - (γ : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) := by
    rw [hs, hs, neg_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hz0, one_smul, Matrix.smul_mul, hAB]
    abel
  rw [hmat, Matrix.det_mul, hz, mul_zero]

theorem irreducible_charpoly_inv {ι : Type} [Fintype ι] [DecidableEq ι] (γ : GL ι K)
    (hγ : Irreducible (Matrix.charpoly (γ : Matrix ι ι K))) {z : AlgebraicClosure K}
    (hz0 : z ≠ 0) (hz : aeval z (Matrix.charpoly (γ : Matrix ι ι K)) = 0) :
    Irreducible (Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K)) := by
  classical
  have hint : ∀ w : AlgebraicClosure K, IsIntegral K w := fun w => Algebra.IsIntegral.isIntegral w
  have h1 : Matrix.charpoly (γ : Matrix ι ι K) = minpoly K z :=
    minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)
  have hadj : IntermediateField.adjoin K {z⁻¹} = IntermediateField.adjoin K {z} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K z)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h2 := inv_mem (IntermediateField.mem_adjoin_simple_self K z⁻¹)
      rwa [inv_inv] at h2
  have hdeg : (minpoly K z⁻¹).natDegree = (minpoly K z).natDegree := by
    rw [← IntermediateField.adjoin.finrank (hint _), ← IntermediateField.adjoin.finrank (hint _), hadj]
  have hdvd : minpoly K z⁻¹ ∣ Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K) :=
    minpoly.dvd K _ (root_inv γ hz0 hz)
  have heq : Matrix.charpoly ((γ⁻¹ : GL ι K) : Matrix ι ι K) = minpoly K z⁻¹ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (hint _)) (Matrix.charpoly_monic _) hdvd
      (by rw [Matrix.charpoly_natDegree_eq_dim, hdeg, ← h1, Matrix.charpoly_natDegree_eq_dim])
  rw [heq]
  exact minpoly.irreducible (hint _)

end PI.GreenLabelMapW
