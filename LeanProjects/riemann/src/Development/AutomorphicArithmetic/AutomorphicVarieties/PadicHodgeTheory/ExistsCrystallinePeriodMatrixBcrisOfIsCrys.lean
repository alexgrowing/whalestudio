import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Generic

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V] [IsDomain B]

private theorem exists_inv_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  classical
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  have h2 : finrank K₀ ↥(DcrisK₀ PD ρ) = d := by
    rw [(isCrys_iff_finrank PD ρ).1 h, finrank_eq_card_basis v, Fintype.card_fin]
  let d₀ := Module.finBasisOfFinrankEq K₀ ↥(DcrisK₀ PD ρ) h2
  let b := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (b i) = b i := by
    intro g i
    have : b i = (d₀ i : B ⊗[Qp] V) := by simp [b, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  let e := Algebra.TensorProduct.basis B v
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    simp only [map_sum, sig_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext k i
  rw [Matrix.mul_apply]
  change _ = e.repr (b i) k
  conv_rhs => rw [← hd g i, hrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

private theorem exists_period_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ (M M' : Matrix (Fin d) (Fin d) B) (A : Matrix (Fin d) (Fin d) K₀), M * M' = 1 ∧ IsUnit A.det ∧
      M.map PD.φ = M * A.map (algebraMap K₀ B) ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  obtain ⟨M, M', hM, hg⟩ := exists_inv_matrix PD hf hu ρ v h
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g, (M' * M.map PD.φ).map (PD.actB g) = M' * M.map PD.φ := by
    intro g
    set R := (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) with hR
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : M'.map (PD.actB g) = M' * R := by
      have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
        rw [← Matrix.mul_assoc, hg g]
      rw [h1, Matrix.mul_one] at this
      rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
    have h3 : R * (M.map PD.φ).map (PD.actB g) = M.map PD.φ := by
      have h4 : R.map PD.φ = R := by
        ext i j
        simp [hR]
      have h5 : (M.map PD.φ).map (PD.actB g) = (M.map (PD.actB g)).map PD.φ := by
        ext i j
        simp [PD.φ_comm]
      rw [h5, ← h4, ← Matrix.map_mul, hg g]
    rw [Matrix.map_mul, h2, Matrix.mul_assoc, h3]
  choose A hA using fun i j => PD.invB ((M' * M.map PD.φ) i j) fun g => congrFun (congrFun (hinv g) i) j
  have hA' : (Matrix.of A).map (algebraMap K₀ B) = M' * M.map PD.φ := by
    ext i j
    exact hA i j
  refine ⟨M, M', Matrix.of A, hM, ?_, by rw [hA', ← Matrix.mul_assoc, hM, Matrix.one_mul], hg⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 : ((Matrix.of A).map (algebraMap K₀ B)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : (M' * M.map PD.φ) * (M'.map PD.φ * M) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.map PD.φ), ← Matrix.map_mul, hM,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM']
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, ← hA', h1, zero_mul, Matrix.det_one] at h3
  exact zero_ne_one h3

end Generic

theorem UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → ∃ (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 ∧ IsUnit A.det ∧ M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) ∧ (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) := by
  intro l _ K V _ _ _ ρ d e h
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨M, M', A, h1, h2, h3, h4⟩ := exists_period_matrix ((PP l).PD K)
    (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K) ρ e h
  refine ⟨M, M', A, h1, h2, ?_, fun g => ?_⟩
  · rw [← h3]
    ext i j
    exact ((PP l).PD_φ K _).symm
  · have h5 : M.map ((PP l).actQ (g : GQ l)) = M.map (((PP l).PD K).actB g) := by
      ext i j
      exact ((PP l).PD_actB K g _).symm
    rw [h5, h4]
