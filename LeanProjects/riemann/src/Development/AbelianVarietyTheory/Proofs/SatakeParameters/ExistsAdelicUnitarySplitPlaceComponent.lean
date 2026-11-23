import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

noncomputable section

namespace GlobalTheory.SplitLift

section General

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

open Formalism.UG

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_smul (σ : A →+* A) (a : A) (M : Matrix n n A) : cT σ (a • M) = σ a • cT σ M := by
  ext i j; simp [cT]

omit [Fintype n] [DecidableEq n] in
theorem conjTransposeBy_ringInvolution_involutive (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n A) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem exists_unitary (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (m m' : Matrix n n A)
    (h : e • (m * m') = e • (1 : Matrix n n A)) :
    ∃ g ∈ UJ σ J, (e + σ e) • ((g : Matrix n n A) - 1) = (g : Matrix n n A) - 1 ∧
      e • (g : Matrix n n A) = e • m := by
  have hKJ : K * J = 1 := mul_eq_one_comm.1 hJK
  have hK : cT σ K = K := by
    have h1 : cT σ K * J = 1 := by rw [← hJ, ← cT_mul, hJK, cT_one]
    calc cT σ K = cT σ K * (J * K) := by rw [hJK, mul_one]
      _ = K := by rw [← mul_assoc, h1, one_mul]
  have hee : σ e * σ e = σ e := by rw [← map_mul, he]
  have he'' : σ e * e = 0 := by rw [mul_comm, he']

  obtain ⟨x, hx⟩ : ∃ x, x = m - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = m' - 1 := ⟨_, rfl⟩
  have hm : m = 1 + x := by rw [hx]; abel
  have hm' : m' = 1 + y := by rw [hy]; abel
  have hab : (1 + e • x) * (1 + e • y) = 1 := by
    have h2 : e • (x + y + x * y) = 0 := by
      have : x + y + x * y = m * m' - 1 := by rw [hm, hm']; noncomm_ring
      rw [this, smul_sub, h, sub_self]
    calc (1 + e • x) * (1 + e • y) = 1 + (e • x + e • y + (e • x) * (e • y)) := by
          simp only [mul_add, add_mul, one_mul, mul_one]; abel
      _ = 1 := by
        rw [smul_mul_smul_comm, he, ← smul_add, ← smul_add, h2, add_zero]
  have hba : (1 + e • y) * (1 + e • x) = 1 := mul_eq_one_comm.1 hab
  let s : Matrix n n A → Matrix n n A := fun z => K * cT σ z * J
  have hs_mul : ∀ z w, s (z * w) = s w * s z := by
    intro z w
    show K * cT σ (z * w) * J = K * cT σ w * J * (K * cT σ z * J)
    rw [cT_mul]
    calc K * (cT σ w * cT σ z) * J = K * cT σ w * (J * K) * cT σ z * J := by rw [hJK]; noncomm_ring
      _ = _ := by noncomm_ring
  have hs_one : s 1 = 1 := by
    show K * cT σ 1 * J = 1
    rw [cT_one, mul_one, hKJ]
  have hs_e : ∀ z, s (1 + e • z) = 1 + σ e • s z := by
    intro z
    show K * cT σ (1 + e • z) * J = 1 + σ e • (K * cT σ z * J)
    rw [conjTransposeBy_ringInvolution_add, cT_one, conjTransposeBy_ringInvolution_smul, mul_add, add_mul, mul_one, hKJ, Matrix.mul_smul, Matrix.smul_mul]
  have hss : ∀ z, s (s z) = z := by
    intro z
    show K * cT σ (K * cT σ z * J) * J = z
    rw [cT_mul, cT_mul, conjTransposeBy_ringInvolution_involutive σ hσ, hJ, hK]
    calc K * (J * (z * K)) * J = (K * J) * z * (K * J) := by noncomm_ring
      _ = z := by rw [hKJ, one_mul, mul_one]
  have hcomm : ∀ z w : Matrix n n A, (1 + e • z) * (1 + σ e • w) = 1 + e • z + σ e • w ∧
      (1 + σ e • w) * (1 + e • z) = 1 + e • z + σ e • w := by
    intro z w
    constructor
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm e z (σ e) w, he', zero_smul]; simp
    · rw [mul_add, add_mul, add_mul, smul_mul_smul_comm (σ e) w e z, he'', zero_smul]; simp; abel
  have hu : s ((1 + e • x) * s (1 + e • y)) * ((1 + e • x) * s (1 + e • y)) = 1 := by
    have hc : s (1 + e • x) * (1 + e • x) = (1 + e • x) * s (1 + e • x) := by
      rw [hs_e, (hcomm _ _).1, (hcomm _ _).2]
    rw [hs_mul, hss]
    calc (1 + e • y) * s (1 + e • x) * ((1 + e • x) * s (1 + e • y))
        = (1 + e • y) * (s (1 + e • x) * (1 + e • x)) * s (1 + e • y) := by simp only [mul_assoc]
      _ = ((1 + e • y) * (1 + e • x)) * (s (1 + e • x) * s (1 + e • y)) := by rw [hc]; simp only [mul_assoc]
      _ = 1 := by rw [← hs_mul, hba, hs_one, one_mul]
  have hg : (1 + e • x) * s (1 + e • y) = 1 + e • x + σ e • s y := by rw [hs_e, (hcomm _ _).1]
  refine ⟨⟨_, _, mul_eq_one_comm.1 hu, hu⟩, ?_, ?_, ?_⟩
  · show cT σ ((1 + e • x) * s (1 + e • y)) * J * ((1 + e • x) * s (1 + e • y)) = J
    generalize (1 + e • x) * s (1 + e • y) = g at hu
    calc cT σ g * J * g = (J * K) * (cT σ g * J * g) := by rw [hJK, one_mul]
      _ = J * (s g * g) := by simp only [s, mul_assoc]
      _ = J := by rw [hu, mul_one]
  · show (e + σ e) • ((1 + e • x) * s (1 + e • y) - 1) = (1 + e • x) * s (1 + e • y) - 1
    have : (1 + e • x) * s (1 + e • y) - 1 = e • x + σ e • s y := by rw [hg]; abel
    rw [this, smul_add, smul_smul, smul_smul, add_mul, add_mul, he, he', he'', hee, add_zero, zero_add]
  · show e • ((1 + e • x) * s (1 + e • y)) = e • m
    rw [hg, hm, smul_add, smul_add, smul_add, smul_smul, smul_smul, he, he', zero_smul, add_zero]

theorem exists_unitary_prod {B C : Type} [CommRing B] [CommRing C] (p : A →+* B) (q : A →+* C) (φ : A ≃+* B × C)
    (hφ : ∀ z, (φ z).1 = p z ∧ (φ z).2 = q z)
    (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (J K : Matrix n n A) (hJ : cT σ J = J)
    (hJK : J * K = 1) (e : A) (he : e * e = e) (he' : e * σ e = 0) (hinf : p e = 0) (m m' : Matrix n n C)
    (h : q e • (m * m') = q e • (1 : Matrix n n C)) :
    ∃ g ∈ UJ σ J, (∀ i j, (e + σ e) * ((g : Matrix n n A) - 1) i j = ((g : Matrix n n A) - 1) i j) ∧
      q e • (g : Matrix n n A).map q = q e • m := by
  have lift : ∀ M : Matrix n n C, ∃ N : Matrix n n A, N.map q = M := by
    intro M
    refine ⟨Matrix.of fun i j => φ.symm (0, M i j), Matrix.ext fun i j => ?_⟩
    show q (φ.symm (0, M i j)) = M i j
    rw [← (hφ _).2, RingEquiv.apply_symm_apply]
  obtain ⟨N, rfl⟩ := lift m
  obtain ⟨N', rfl⟩ := lift m'
  have hN : e • (N * N') = e • (1 : Matrix n n A) := by
    refine Matrix.ext fun i j => φ.injective (Prod.ext ?_ ?_)
    · rw [(hφ _).1, (hφ _).1, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul, hinf, zero_mul, zero_mul]
    · rw [← Matrix.map_mul, ← Matrix.map_one q (map_zero _) (map_one _)] at h
      rw [(hφ _).2, (hφ _).2, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        map_mul, map_mul]
      exact congrFun (congrFun h i) j
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary σ hσ _ _ hJ hJK e he he' N N' hN
  refine ⟨g, hg, fun i j => congrFun (congrFun h1 i) j, Matrix.ext fun i j => ?_⟩
  have h3 : e * g.1 i j = e * N i j := congrFun (congrFun h2 i) j
  have h4 := congrArg q h3
  rw [map_mul, map_mul] at h4
  exact h4

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_lift : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ m m' : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), finPart D e • (m * m') = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) → ∃ g : GA D V, Formalism.L2.Theta.SuppAt e V g ∧ finPart D e • finMat D.sp.cm.sig V.gram g = finPart D e • m := by
  intro D V e he m m' h
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hφ' : ∀ z, (φ z).1 = infPart D z ∧ (φ z).2 = finPart D z := hφ
  have hinf : infPart D e = 0 := by
    obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
    have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
    rw [h6, RingHom.map_mul, h5, mul_zero]
  have hJK : JR (AF D.host.F) V.gram * (V.gram⁻¹).map (incA D) = 1 := by
    show V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.UnitaryGlue.gram_det_ne_zero V).isUnit,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ : Formalism.UG.cT (cA D) (JR (AF D.host.F) V.gram) = JR (AF D.host.F) V.gram := by
    refine Matrix.ext fun i j => ?_
    show cA D (incA D (V.gram j i)) = incA D (V.gram i j)
    rw [GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.gram_star]
  obtain ⟨g, hg, h1, h2⟩ := exists_unitary_prod (infPart D) (finPart D) φ hφ' (cA D) GlobalTheory.DualPairCheck.cA_cA _ _
    hJ hJK e he.1 he.2.1 hinf m m' h
  exact ⟨⟨g, hg⟩, h1, h2⟩

end GlobalTheory.SplitLift

end
