import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootCharpolyOfIsRootMinpoly

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.GlobEig

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem minpoly_one_tmul {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_tmul K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

theorem mulLeft_one_tmul (k L R : Type) [Field k] [Field L] [Algebra k L] [Ring R] [Algebra k R] (a : R) :
    LinearMap.mulLeft L ((1 : L) ⊗ₜ[k] a) = (LinearMap.mulLeft k a).baseChange L := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c r
  simp [Algebra.TensorProduct.tmul_mul_tmul]

theorem isRoot_minpoly_of_isRoot_charpoly {k A E : Type} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Field E] [Algebra k E] (y : A) (μ : E)
    (h : ((LinearMap.mulLeft k y).charpoly.map (algebraMap k E)).IsRoot μ) :
    ((minpoly k y).map (algebraMap k E)).IsRoot μ := by
  rw [← LinearMap.charpoly_baseChange, ← mulLeft_one_tmul] at h
  have hr := Module.End.isRoot_of_hasEigenvalue ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 h)
  have e : minpoly E (LinearMap.mulLeft E ((1 : E) ⊗ₜ[k] y)) = minpoly E ((1 : E) ⊗ₜ[k] y) :=
    minpoly.algHom_eq (Algebra.lmul E (E ⊗[k] A)) (Algebra.lmul_injective (R := E)) _
  rwa [e, minpoly_one_tmul] at hr

theorem isRoot_charpoly_of_isRoot_minpoly {F C E : Type} [Field F] [Ring C] [Algebra F C]
    [FiniteDimensional F C] [Algebra.IsCentral F C] [IsSimpleRing C] [Field E] (τ : F →+* E) {n : ℕ}
    (hn : 0 < n) (ρ : C →+* Matrix (Fin n) (Fin n) E)
    (hρ : ∀ a, ρ (algebraMap F C a) = Matrix.scalar (Fin n) (τ a))
    (x : C) (μ : E) (hμ : ((minpoly F x).map τ).IsRoot μ) : (ρ x).charpoly.IsRoot μ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9; revert F C E h_3 h_4 h_5 h_6 h_7 h_8 h_9 τ n hn ρ hρ x μ hμ; exact @_root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly)
  | exact @_root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly
  | exact _root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly
  | (apply _root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumScalarVanishing.isRoot_charpoly_of_isRoot_minpoly ..)

theorem exists_emb_isRoot {F C E : Type} [Field F] [NumberField F] [Ring C] [IsDomain C] [Algebra F C]
    [Algebra ℚ C] [IsScalarTower ℚ F C] [FiniteDimensional F C] [Field E] [Algebra ℚ E] [IsAlgClosed E]
    (y : C) (μ : E) (h : ((minpoly ℚ y).map (algebraMap ℚ E)).IsRoot μ) :
    ∃ τ : F →+* E, ((minpoly F y).map τ).IsRoot μ := by
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  haveI : Fact (Irreducible (minpoly F y)) := ⟨minpoly.irreducible hyi⟩
  haveI : FiniteDimensional F (AdjoinRoot (minpoly F y)) :=
    (AdjoinRoot.powerBasis (minpoly.ne_zero hyi)).finite
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly F y)) := Module.Finite.trans F _
  haveI : Algebra.IsAlgebraic ℚ (AdjoinRoot (minpoly F y)) := Algebra.IsAlgebraic.of_finite ℚ _
  set r := AdjoinRoot.root (minpoly F y)
  have hdvd : minpoly ℚ y ∣ minpoly ℚ r := by
    apply minpoly.dvd
    have h1 : minpoly F y ∣ (minpoly ℚ r).map (algebraMap ℚ F) := by
      rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, aeval_map_algebraMap, minpoly.aeval]
    obtain ⟨k, hk⟩ := h1
    rw [← aeval_map_algebraMap F, hk, map_mul, minpoly.aeval, zero_mul]
  have hne : minpoly ℚ r ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral r)
  have hμ' : μ ∈ (minpoly ℚ r).rootSet E := by
    rw [mem_rootSet]
    refine ⟨hne, ?_⟩
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, map_mul, aeval_def, eval₂_eq_eval_map, h.eq_zero, zero_mul]
  rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hμ'
  obtain ⟨ψ, hψ⟩ := hμ'
  refine ⟨(ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _), ?_⟩
  rw [← hψ, IsRoot.def, eval_map]
  change eval₂ ((ψ : AdjoinRoot (minpoly F y) →+* E).comp (algebraMap F _))
    ((ψ : AdjoinRoot (minpoly F y) →+* E) r) (minpoly F y) = 0
  rw [← hom_eval₂, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

end GlobalTheory.GlobEig

namespace GlobalTheory.GlobEig

variable {p : ℕ} [Fact p.Prime]

theorem norm_aut (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

noncomputable def rhoE (G : HTGroup p) (i : Fin G.m) : G.C →+* Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) :=
  (RingHom.mapMatrix (algebraMap (G.Fw i) (PadicAlgCl p))).comp (G.rho i)

theorem rhoE_F (G : HTGroup p) (i : Fin G.m) (a : G.F) :
    rhoE G i (algebraMap G.F G.C a) = Matrix.scalar (Fin G.n) (G.emb i a) := by
  simp only [rhoE, RingHom.comp_apply, G.rho_F, RingHom.mapMatrix_apply]
  ext j k
  simp only [Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · simp

theorem charpoly_rhoE (G : HTGroup p) (i : Fin G.m) (x : G.C) :
    (rhoE G i x).charpoly = (G.rho i x).charpoly.map (algebraMap (G.Fw i) (PadicAlgCl p)) := by
  rw [← Matrix.charpoly_map]
  rfl

theorem exists_root_rho (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) (hτ : LiesOver G.Kq G.u τ)
    (x : G.C) (μ : PadicAlgCl p) (hμ : ((minpoly G.F x).map τ).IsRoot μ) :
    ∃ (i : Fin G.m) (ν : PadicAlgCl p), ‖ν‖ = ‖μ‖ ∧
      ((G.rho i x).charpoly.map (algebraMap (G.Fw i) (PadicAlgCl p))).IsRoot ν := by
  obtain ⟨i, σ, hσ⟩ := G.emb_all τ hτ
  refine ⟨i, σ.symm μ, ?_, ?_⟩
  · rw [← norm_aut σ, AlgEquiv.apply_symm_apply]
  · rw [← charpoly_rhoE]
    refine isRoot_charpoly_of_isRoot_minpoly (G.emb i) G.n_pos (rhoE G i) (rhoE_F G i) x _ ?_
    have key := Polynomial.hom_eval₂ (minpoly G.F x) (G.emb i)
      ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) (σ.symm μ)
    rw [← hσ] at key
    have e : ((σ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) (σ.symm μ) = μ :=
      σ.apply_symm_apply μ
    have hz : eval₂ τ μ (minpoly G.F x) = 0 := by rw [← eval_map]; exact hμ.eq_zero
    rw [e, hz] at key
    rw [IsRoot.def, eval_map]
    exact (map_eq_zero_iff _ σ.injective).1 key

theorem sh_aeval (G : HTGroup p) (x : G.C) (P : G.F[X]) :
    sh G (aeval x P) = aeval (sh G x) (P.map (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.map_add, map_add, map_add, ← hP, ← hQ]
    simp only [sh, map_add, MulOpposite.unop_add]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial]
    simp only [sh, map_mul, MulOpposite.unop_mul, map_pow, MulOpposite.unop_pow]
    rw [G.star_F]
    exact (Algebra.commutes _ _).symm

theorem isRoot_minpoly_sh (G : HTGroup p) (y : G.C) (τ : G.F →+* PadicAlgCl p) (μ : PadicAlgCl p)
    (hμ : ((minpoly G.F y).map τ).IsRoot μ) :
    ((minpoly G.F (sh G y)).map (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F))).IsRoot μ := by
  have hss : sh G (sh G y) = y := G.star_star y
  have h0 : aeval y ((minpoly G.F (sh G y)).map (IsCMField.complexConj G.F : G.F →+* G.F)) = 0 := by
    have h1 := sh_aeval G (sh G y) (minpoly G.F (sh G y))
    rw [hss, minpoly.aeval] at h1
    rw [← h1]
    simp [sh]
  obtain ⟨k, hk⟩ := minpoly.dvd G.F y h0
  rw [← Polynomial.map_map, hk, Polynomial.map_mul, IsRoot.def, eval_mul, hμ.eq_zero, zero_mul]

end GlobalTheory.GlobEig

namespace GlobalTheory.GlobEig

variable {p : ℕ} [Fact p.Prime]

theorem liesOver_or_conj (G : HTGroup p) (τ : G.F →+* PadicAlgCl p) :
    LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (IsCMField.complexConj G.F : G.F →+* G.F)) := by
  obtain ⟨hfr, hre⟩ := G.hKq
  let φ : G.F →+* ℂ := Classical.arbitrary _
  obtain ⟨x0, hx0K, hx0⟩ := hre φ
  set k0 : G.Kq := ⟨x0, hx0K⟩ with hk0
  have hli : LinearIndependent ℚ ![(1 : G.Kq), k0] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hF : (s : G.F) + (t : G.F) * x0 = 0 := by
      have := congrArg (fun z : G.Kq => (z : G.F)) hst
      simpa [Rat.smul_def, hk0] using this
    by_cases ht : t = 0
    · subst ht
      simp at hF
      exact ⟨hF, rfl⟩
    · exfalso
      apply hx0
      have e : x0 = ((-s / t : ℚ) : G.F) := by
        have ht' : (t : G.F) ≠ 0 := by exact_mod_cast ht
        push_cast
        field_simp
        linear_combination hF
      rw [e, map_ratCast]
      exact Complex.ratCast_im _
  let bs := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hmem : ∀ z : G.Kq, ∃ a b : ℚ, z = (a : G.Kq) + (b : G.Kq) * k0 := by
    intro z
    refine ⟨bs.repr z 0, bs.repr z 1, ?_⟩
    conv_lhs => rw [← bs.sum_repr z]
    simp [Fin.sum_univ_two, bs, Rat.smul_def]
  obtain ⟨a, b, hq⟩ := hmem (k0 * k0)
  have hx2 : x0 * x0 = (a : G.F) + (b : G.F) * x0 := by
    have := congrArg (fun z : G.Kq => (z : G.F)) hq
    simpa [hk0] using this
  set cj : G.F →+* G.F := (IsCMField.complexConj G.F : G.F →+* G.F) with hcj
  have hc2 : cj x0 * cj x0 = (a : G.F) + (b : G.F) * cj x0 := by
    have := congrArg cj hx2
    simpa [map_ratCast] using this
  have hne : cj x0 ≠ x0 := by
    intro h
    apply hx0
    have h1 : φ (cj x0) = starRingEnd ℂ (φ x0) := IsCMField.complexEmbedding_complexConj G.F φ x0
    rw [h] at h1
    exact Complex.conj_eq_iff_im.1 h1.symm
  have hcx : cj x0 = (b : G.F) - x0 := by
    have h : (cj x0 - x0) * (cj x0 + x0 - (b : G.F)) = 0 := by linear_combination hc2 - hx2
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · linear_combination h
  set ψ : G.Kq →+* PadicAlgCl p := (algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u with hψ
  have hz2 : τ x0 * τ x0 = (a : PadicAlgCl p) + (b : PadicAlgCl p) * τ x0 := by
    have := congrArg τ hx2
    simpa [map_ratCast] using this
  have hw2 : ψ k0 * ψ k0 = (a : PadicAlgCl p) + (b : PadicAlgCl p) * ψ k0 := by
    have := congrArg ψ hq
    simpa [map_ratCast] using this
  have hψk : ∀ k : G.Kq, algebraMap ℚ_[p] (PadicAlgCl p) (G.u k) = ψ k := fun k => rfl
  have h : (τ x0 - ψ k0) * (τ x0 + ψ k0 - (b : PadicAlgCl p)) = 0 := by linear_combination hz2 - hw2
  rcases mul_eq_zero.1 h with h | h
  · left
    intro k
    obtain ⟨a', b', hk⟩ := hmem k
    rw [hψk, hk]
    have e : ((((a' : G.Kq) + (b' : G.Kq) * k0 : G.Kq)) : G.F) = (a' : G.F) + (b' : G.F) * x0 := by
      simp [hk0]
    rw [e]
    simp only [map_add, map_mul, map_ratCast]
    linear_combination (b' : PadicAlgCl p) * h
  · right
    intro k
    obtain ⟨a', b', hk⟩ := hmem k
    rw [hψk, hk]
    have e : ((((a' : G.Kq) + (b' : G.Kq) * k0 : G.Kq)) : G.F) = (a' : G.F) + (b' : G.F) * x0 := by
      simp [hk0]
    rw [RingHom.comp_apply, e]
    simp only [map_add, map_mul, map_ratCast, hcx, map_sub]
    linear_combination (-(b' : PadicAlgCl p)) * h

theorem isRoot_inv (G : HTGroup p) (i : Fin G.m) (β y : G.Cˣ) (c : ℚˣ)
    (hyc : (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β) (ν : PadicAlgCl p)
    (hν : ((G.rho i (sh G y)).charpoly.map (algebraMap (G.Fw i) (PadicAlgCl p))).IsRoot ν) :
    ((G.rho i ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw i) (PadicAlgCl p))).IsRoot
      (ν * ((c : ℚ) : PadicAlgCl p)⁻¹) := by
  rw [← charpoly_rhoE] at hν ⊢
  rw [← Matrix.charpoly_toLin', ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hν ⊢
  obtain ⟨v, hv⟩ := hν.exists_hasEigenvector
  have hSv : rhoE G i (sh G y) *ᵥ v = ν • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  set s : PadicAlgCl p := ((c : ℚ) : PadicAlgCl p) with hs_def
  have hs : s ≠ 0 := by simp [s]
  have hT : rhoE G i (algebraMap ℚ G.C c) = Matrix.scalar (Fin G.n) s := by
    rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, rhoE_F, eq_ratCast, map_ratCast]
  have hsc : ∀ z : Fin G.n → PadicAlgCl p, Matrix.scalar (Fin G.n) s *ᵥ z = s • z := by
    intro z
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hM := congrArg (rhoE G i) hyc
  rw [map_mul, map_mul, map_mul, hT] at hM
  have hYi : rhoE G i ((y⁻¹ : G.Cˣ) : G.C) * rhoE G i (y : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hBi : rhoE G i ((β⁻¹ : G.Cˣ) : G.C) * rhoE G i (β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  set w := rhoE G i (β : G.C) *ᵥ v with hw
  have hw0 : w ≠ 0 := by
    intro h
    apply hv.2
    have := congrArg (fun z => rhoE G i ((β⁻¹ : G.Cˣ) : G.C) *ᵥ z) h
    simpa [w, Matrix.mulVec_mulVec, hBi] using this
  have key : s • (rhoE G i ((y⁻¹ : G.Cˣ) : G.C) *ᵥ w) = ν • w := by
    calc s • (rhoE G i ((y⁻¹ : G.Cˣ) : G.C) *ᵥ w)
        = rhoE G i ((y⁻¹ : G.Cˣ) : G.C) *ᵥ (Matrix.scalar (Fin G.n) s *ᵥ w) := by
          rw [hsc, Matrix.mulVec_smul]
      _ = rhoE G i ((y⁻¹ : G.Cˣ) : G.C) *ᵥ ((rhoE G i (y : G.C) * rhoE G i (β : G.C) *
            rhoE G i (sh G y)) *ᵥ v) := by
          rw [hM]
          simp only [hw, Matrix.mulVec_mulVec, mul_assoc]
      _ = (rhoE G i ((y⁻¹ : G.Cˣ) : G.C) * rhoE G i (y : G.C)) *ᵥ
            (rhoE G i (β : G.C) *ᵥ (rhoE G i (sh G y) *ᵥ v)) := by
          simp only [Matrix.mulVec_mulVec, mul_assoc]
      _ = ν • w := by rw [hYi, Matrix.one_mulVec, hSv, Matrix.mulVec_smul]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := w)
  refine ⟨?_, hw0⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have := congrArg (fun z => s⁻¹ • z) key
  simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at this
  rw [this, mul_comm]

end GlobalTheory.GlobEig

namespace GlobalTheory.GlobEig

theorem root_norm_le : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), IsSimple G → ∀ (β y : G.Cˣ) (c : ℚˣ),
    (y : G.C) * β * sh G y = algebraMap ℚ G.C c * β → ∀ B : ℝ, ‖((c : ℚ) : ℚ_[p])‖ ≤ B →
    ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ ≤ B →
    (∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w (y : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) →
    (∀ (w : Fin G.m) (μ : PadicAlgCl p),
      ((G.rho w ((y⁻¹ : G.Cˣ) : G.C)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ B) →
    ∀ μ : PadicAlgCl p, ((LinearMap.mulLeft ℚ (y : G.C)).charpoly.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ →
      ‖μ‖ ≤ B * B := by
  intro p _ G hS β y c hyc B hc hc' hy hyi μ hμ
  haveI : NoZeroDivisors G.C := ⟨fun {a b} hab => by
    by_contra h
    push_neg at h
    obtain ⟨u, hu⟩ := hS.1 a h.1
    apply h.2
    calc b = (((u⁻¹ : G.Cˣ) : G.C) * a) * b := by rw [← hu, Units.inv_mul, one_mul]
      _ = 0 := by rw [mul_assoc, hab, mul_zero]⟩
  haveI : IsDomain G.C := NoZeroDivisors.to_isDomain _
  have h0 := isRoot_minpoly_of_isRoot_charpoly (y : G.C) μ hμ
  obtain ⟨τ, hτ⟩ := exists_emb_isRoot (F := G.F) (y : G.C) μ h0
  have hcpos : 0 < ‖((c : ℚ) : ℚ_[p])‖ := norm_pos_iff.2 (by simp)
  have hprod : ‖((c : ℚ) : ℚ_[p])‖ * ‖(((c⁻¹ : ℚˣ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [← norm_mul, ← Rat.cast_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Rat.cast_one, norm_one]
  have hB0 : 0 ≤ B := hcpos.le.trans hc
  have hB1 : 1 ≤ B := by
    have h1 : 1 ≤ B * B := by
      rw [← hprod]
      exact mul_le_mul hc hc' (norm_nonneg _) hB0
    nlinarith
  rcases liesOver_or_conj G τ with hu | hu
  · obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G τ hu y μ hτ
    have h1 := hy i ν hν
    rw [hνμ] at h1
    nlinarith
  · have h2 := isRoot_minpoly_sh G y τ μ hτ
    obtain ⟨i, ν, hνμ, hν⟩ := exists_root_rho G _ hu (sh G y) μ h2
    have h3 := isRoot_inv G i β y c hyc ν hν
    have h4 := hyi i _ h3
    have hs : ‖((c : ℚ) : PadicAlgCl p)‖ = ‖((c : ℚ) : ℚ_[p])‖ := by
      rw [← PadicAlgCl.norm_extends, map_ratCast]
    rw [norm_mul, norm_inv, hs, hνμ, ← div_eq_mul_inv, div_le_iff₀ hcpos] at h4
    calc ‖μ‖ ≤ B * ‖((c : ℚ) : ℚ_[p])‖ := h4
      _ ≤ B * B := mul_le_mul_of_nonneg_left hc hB0

end GlobalTheory.GlobEig
