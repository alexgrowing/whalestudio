import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsArchimedeanAdeleChartOfRealChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRealPointUnitaryWithComponents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.TransvGroup

section Ring

variable {A : Type} [CommRing A] {n : ℕ}

theorem one_add_mul {N : Matrix (Fin n) (Fin n) A} (hN : N * N = 0) (a b : A) :
    (1 + a • N) * (1 + b • N) = 1 + (a + b) • N := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN,
    smul_zero, smul_zero, add_zero, add_smul, add_assoc, add_comm (b • N)]

theorem cT_one_add (c : A →+* A) {N J : Matrix (Fin n) (Fin n) A} (hN : N * N = 0)
    (hJ : Formalism.UG.cT c N * J = J * N) (a : A) :
    Formalism.UG.cT c (1 + a • N) * J * (1 + a • N) = J + (c a + a) • (J * N) := by
  have e : Formalism.UG.cT c (1 + a • N) = 1 + c a • Formalism.UG.cT c N := by
    ext i j
    simp only [Formalism.UG.cT, transpose_apply, map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
      map_mul, Matrix.one_apply, eq_comm (a := i)]
    split_ifs <;> simp
  rw [e, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hJ, ← Matrix.mul_smul]
  conv_lhs => rw [← Matrix.mul_one J, Matrix.mul_assoc J 1, Matrix.one_mul, ← Matrix.mul_add, Matrix.mul_assoc,
    one_add_mul hN]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]

theorem nil_sq (x y : Fin n → A) (J : Matrix (Fin n) (Fin n) A) (h : y ⬝ᵥ J *ᵥ x = 0) :
    vecMulVec x (y ᵥ* J) * vecMulVec x (y ᵥ* J) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, ← Matrix.dotProduct_mulVec, h, zero_smul, Matrix.vecMulVec_zero]

theorem nil_mulVec (x y : Fin n → A) (J : Matrix (Fin n) (Fin n) A) (h : y ⬝ᵥ J *ᵥ x = 0) :
    vecMulVec x (y ᵥ* J) *ᵥ x = 0 := by
  rw [Matrix.vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, h]
  simp

theorem nil_adj (c : A →+* A) (hc : ∀ a, c (c a) = a) (x : Fin n → A) (J : Matrix (Fin n) (Fin n) A)
    (hJ : ∀ i j, c (J i j) = J j i) :
    Formalism.UG.cT c (vecMulVec x ((fun i => c (x i)) ᵥ* J)) * J = J * vecMulVec x ((fun i => c (x i)) ᵥ* J) := by
  ext i j
  simp only [Formalism.UG.cT, transpose_apply, map_apply, Matrix.mul_apply, vecMulVec_apply, vecMul, dotProduct, map_mul,
    map_sum, hc, hJ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Ring

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}

theorem cT_map {m p : ℕ} (M : Matrix (Fin m) (Fin p) E) :
    Formalism.UG.cT (sigR R σ) (M.map (inclR (F := F) R)) = (Formalism.UG.cT (σ : E →+* E) M).map (inclR (F := F) R) := by
  funext i j
  simp [Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]

theorem sigR_tmul (s : R) (x : E) : sigR R σ (s ⊗ₜ[F] x) = s ⊗ₜ[F] σ x := rfl

theorem anti_eq [CharZero F] {δ : E} (hδ : σ δ = -δ) (hsp : ∀ x : E, ∃ u v : F, x = u • (1 : E) + v • δ)
    (a : R ⊗[F] E) (ha : sigR R σ a + a = 0) : ∃ s : R, a = s ⊗ₜ[F] δ := by
  obtain ⟨a₀, a₁, rfl⟩ := GlobalTheory.FockCompare.RealChart.tensor_span δ hsp a
  refine ⟨a₁, ?_⟩
  rw [map_add, sigR_tmul, sigR_tmul, hδ, map_one, TensorProduct.tmul_neg] at ha
  have h2 : (2 : F) • (a₀ ⊗ₜ[F] (1 : E)) = 0 := by
    rw [two_smul, ← ha]; abel
  rw [(smul_eq_zero_iff_right two_ne_zero).1 h2, zero_add]

variable {J N : Matrix (Fin n) (Fin n) E}

def tv (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (a : R ⊗[F] E) (ha : sigR R σ a + a = 0) :
    HA R σ J :=
  have h1 : N.map (inclR (F := F) R) * N.map (inclR (F := F) R) = 0 := by
    rw [← Matrix.map_mul, hN, Matrix.map_zero _ (map_zero _)]
  ⟨⟨1 + a • N.map (inclR (F := F) R), 1 + (-a) • N.map (inclR (F := F) R),
    by rw [one_add_mul h1, add_neg_cancel, zero_smul, add_zero],
    by rw [one_add_mul h1, neg_add_cancel, zero_smul, add_zero]⟩, by
      show Formalism.UG.cT (sigR R σ) (1 + a • N.map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
        (1 + a • N.map (inclR (F := F) R)) = J.map (inclR (F := F) R)
      rw [cT_one_add _ h1 (by rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]), ha, zero_smul, add_zero]⟩

theorem skew_of_mem (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hd : J.det ≠ 0)
    {i j : Fin n} (hij : N i j ≠ 0) (g : HR R σ J) (a : R ⊗[F] E)
    (hg : g.1.1 = 1 + a • N.map (inclR (F := F) R)) : sigR R σ a + a = 0 := by
  have h1 : N.map (inclR (F := F) R) * N.map (inclR (F := F) R) = 0 := by
    rw [← Matrix.map_mul, hN, Matrix.map_zero _ (map_zero _)]
  have h2 : Formalism.UG.cT (sigR R σ) g.1.1 * J.map (inclR (F := F) R) * g.1.1 = J.map (inclR (F := F) R) := g.2
  rw [hg, cT_one_add _ h1 (by rw [cT_map, ← Matrix.map_mul, ← Matrix.map_mul, hJ]), add_eq_left] at h2
  have h3 := congrArg (fun M => (J⁻¹).map (inclR (F := F) R) * M) h2
  simp only [Matrix.mul_smul, Matrix.mul_zero] at h3
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hd.isUnit,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul] at h3
  have h4 : (sigR R σ a + a) * inclR (F := F) R (N i j) = 0 := congrFun (congrFun h3 i) j
  have h5 := congrArg (· * inclR (F := F) R (N i j)⁻¹) h4
  simpa only [mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, mul_one, zero_mul] using h5

def coord (c : E →ₗ[F] F) : R ⊗[F] E →ₗ[R] R :=
  (TensorProduct.AlgebraTensorModule.rid F R R).toLinearMap ∘ₗ c.baseChange R

theorem coord_tmul (c : E →ₗ[F] F) (s : R) (x : E) : coord R c (s ⊗ₜ[F] x) = c x • s := by
  simp [coord]

end Tensor

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n : ℕ}
  {J N : Matrix (Fin n) (Fin n) E} {δ : E}

theorem skew_tmul (hδ : σ δ = -δ) (s : R) : sigR R σ (s ⊗ₜ[F] δ) + s ⊗ₜ[F] δ = 0 := by
  rw [sigR_tmul, hδ, TensorProduct.tmul_neg, neg_add_cancel]

def tvHom (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ) :
    Multiplicative R →* HR R σ J where
  toFun s := tv R σ hN hJ (s.toAdd ⊗ₜ[F] δ) (skew_tmul R σ hδ _)
  map_one' := Subtype.ext (Units.ext (by
    show 1 + ((0 : R) ⊗ₜ[F] δ) • N.map (inclR (F := F) R) = 1
    rw [TensorProduct.zero_tmul, zero_smul, add_zero]))
  map_mul' s t := Subtype.ext (Units.ext (by
    show 1 + ((s.toAdd + t.toAdd) ⊗ₜ[F] δ) • N.map (inclR (F := F) R) =
      (1 + (s.toAdd ⊗ₜ[F] δ) • N.map (inclR (F := F) R)) * (1 + (t.toAdd ⊗ₜ[F] δ) • N.map (inclR (F := F) R))
    rw [one_add_mul (by rw [← Matrix.map_mul, hN, Matrix.map_zero _ (map_zero _)]), TensorProduct.add_tmul]))

theorem tvHom_val (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ)
    (s : Multiplicative R) :
    (tvHom R σ hN hJ hδ s).1.1 = 1 + (s.toAdd ⊗ₜ[F] δ) • N.map (inclR (F := F) R) := rfl

theorem closure_eq [CharZero F] (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ)
    (hsp : ∀ x : E, ∃ u v : F, x = u • (1 : E) + v • δ) (hd : J.det ≠ 0) {i j : Fin n} (hij : N i j ≠ 0) :
    Subgroup.closure {g : HR R σ J | ∃ a : R ⊗[F] E, g.1.1 - 1 = a • N.map (inclR (F := F) R)} =
      (tvHom R σ hN hJ hδ).range := by
  rw [← Subgroup.closure_eq (tvHom R σ hN hJ hδ).range]
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha⟩
    rw [sub_eq_iff_eq_add'] at ha
    obtain ⟨s, rfl⟩ := anti_eq R σ hδ hsp a (skew_of_mem R σ hN hJ hd hij g a ha)
    exact ⟨Multiplicative.ofAdd s, Subtype.ext (Units.ext ha.symm)⟩
  · rintro ⟨s, rfl⟩
    exact ⟨_, by rw [tvHom_val, add_sub_cancel_left]⟩

def par (c : E →ₗ[F] F) (x : E) (i j : Fin n) (g : HR R σ J) : Multiplicative R :=
  Multiplicative.ofAdd (coord R c ((g.1.1 - 1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j * inclR (F := F) R x))

theorem par_tvHom (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ)
    {c : E →ₗ[F] F} (hc : c δ = 1) {i j : Fin n} (hij : N i j ≠ 0) (s : Multiplicative R) :
    par R σ c (N i j)⁻¹ i j (tvHom R σ hN hJ hδ s) = s := by
  rw [par, tvHom_val, add_sub_cancel_left, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_assoc, ← map_mul,
    mul_inv_cancel₀ hij, map_one, mul_one, coord_tmul, hc, one_smul]
  rfl

theorem tvHom_mem_iff (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ)
    {c : E →ₗ[F] F} (hc : c δ = 1) {i j : Fin n} (hij : N i j ≠ 0) (s : Multiplicative R) :
    tvHom R σ hN hJ hδ s ∈ HFinIn R σ J ↔ s.toAdd ∈ Set.range (algebraMap F R) := by
  constructor
  · rintro ⟨g, -, hg⟩
    have h1 : g.1.map (inclR (F := F) R) = (tvHom R σ hN hJ hδ s).1.1 := congrArg Units.val hg
    have h2 := par_tvHom R σ hN hJ hδ hc hij s
    rw [par, ← h1, ← Matrix.map_one (inclR (F := F) R) (map_zero _) (map_one _),
      ← Matrix.map_sub _ (map_sub _), Matrix.map_apply, ← map_mul] at h2
    refine ⟨c ((g.1 - 1 : Matrix (Fin n) (Fin n) E) i j * (N i j)⁻¹), ?_⟩
    rw [← h2, Algebra.algebraMap_eq_smul_one, ← coord_tmul]
    rfl
  · rintro ⟨f, hf⟩
    refine ⟨⟨1 + (f • δ) • N, 1 + (-(f • δ)) • N,
      by rw [one_add_mul hN, add_neg_cancel, zero_smul, add_zero],
      by rw [one_add_mul hN, neg_add_cancel, zero_smul, add_zero]⟩, ?_, Units.ext ?_⟩
    · show Formalism.UG.cT (σ : E →+* E) (1 + (f • δ) • N) * J * (1 + (f • δ) • N) = J
      have : (σ : E →+* E) (f • δ) + f • δ = 0 := by
        show σ (f • δ) + f • δ = 0
        rw [map_smul, hδ, smul_neg, neg_add_cancel]
      rw [cT_one_add _ hN hJ, this, zero_smul, add_zero]
    · show (1 + (f • δ) • N).map (inclR (F := F) R) = 1 + (s.toAdd ⊗ₜ[F] δ) • N.map (inclR (F := F) R)
      have : inclR (F := F) R (f • δ) = s.toAdd ⊗ₜ[F] δ := by
        rw [← hf, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        rfl
      rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), ← this]
      congr 1
      ext k l
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

variable [TopologicalSpace R] [IsTopologicalRing R] [Module.Finite F E]

theorem continuous_par (c : E →ₗ[F] F) (x : E) (i j : Fin n) :
    Continuous (par R σ c x i j : HA R σ J → Multiplicative R) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  have h1 : Continuous (coord R c) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous (fun k : HA R σ J => k.1.1) := Units.continuous_val.comp continuous_subtype_val
  exact continuous_ofAdd.comp (h1.comp (((hm.sub continuous_const).matrix_elem i j).mul continuous_const))

theorem continuous_tvHom (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ) :
    Continuous (tvHom R σ hN hJ hδ : Multiplicative R → HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  have h1 : Continuous fun s : Multiplicative R => (s.toAdd ⊗ₜ[F] δ : R ⊗[F] E) := by
    have h2 : Continuous fun a : Multiplicative R => a.toAdd • ((1 : R) ⊗ₜ[F] δ : R ⊗[F] E) :=
      continuous_smul.comp (continuous_toAdd.prodMk continuous_const)
    refine h2.congr fun a => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (h1.smul continuous_const)
  · exact continuous_const.add (h1.neg.smul continuous_const)

theorem exists_equiv [T2Space (HA R σ J)] (hN : N * N = 0) (hJ : Formalism.UG.cT (σ : E →+* E) N * J = J * N) (hδ : σ δ = -δ)
    (h0 : δ ≠ 0) {i j : Fin n} (hij : N i j ≠ 0) (Z : Subgroup (HA R σ J))
    (hmem : ∀ z : HA R σ J, z ∈ Z ↔ ∃ s, tvHom R σ hN hJ hδ s = z) :
    (∃ e : Multiplicative R ≃ₜ* Z, ∀ a, ((e a : Z) : HA R σ J) ∈ HFinIn R σ J ↔
      Multiplicative.toAdd a ∈ Set.range (algebraMap F R)) ∧ IsClosed (Z : Set (HA R σ J)) := by
  obtain ⟨c, hc⟩ := Module.Projective.exists_dual_eq_one F h0
  have hl := par_tvHom R σ hN hJ hδ hc hij
  have c1 := continuous_par (J := J) R σ c (N i j)⁻¹ i j
  have c2 := continuous_tvHom R σ hN hJ hδ
  refine ⟨⟨⟨⟨⟨fun s => ⟨tvHom R σ hN hJ hδ s, (hmem _).2 ⟨s, rfl⟩⟩,
      fun z => par R σ c (N i j)⁻¹ i j z.1, hl, fun z => ?_⟩,
      fun s t => Subtype.ext ((tvHom R σ hN hJ hδ).map_mul s t)⟩, c2.subtype_mk _, c1.comp continuous_subtype_val⟩,
      tvHom_mem_iff R σ hN hJ hδ hc hij⟩, ?_⟩
  · obtain ⟨z, hz⟩ := z
    obtain ⟨s, rfl⟩ := (hmem _).1 hz
    exact Subtype.ext (congrArg (tvHom R σ hN hJ hδ) (hl s))
  · have := Function.LeftInverse.isClosed_range (X := HA R σ J) hl c1 c2
    have e : (Z : Set (HA R σ J)) = Set.range (tvHom R σ hN hJ hδ : Multiplicative R → HA R σ J) := Set.ext hmem
    rw [e]
    exact this

end Group

section Main

open GlobalTheory.FockCompare

variable {D : D7}

abbrev nilM (V : HSp D) (ξ : Fin V.rank → D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E :=
  vecMulVec ξ ((fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram)

theorem nilM_sq {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) : nilM V ξ * nilM V ξ = 0 :=
  nil_sq _ _ _ h.2

theorem nilM_adj (V : HSp D) (ξ : Fin V.rank → D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (nilM V ξ) * V.gram = V.gram * nilM V ξ :=
  nil_adj _ (fun a => star_star a) ξ V.gram fun i j => V.herm.eq (V.frame i) (V.frame j)

theorem nilM_ne {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) : ∃ i j, nilM V ξ i j ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h.1
  have h1 : (fun i => (D.sp.cm.sig : D.host.E →+* D.host.E) (ξ i)) ᵥ* V.gram ≠ 0 := by
    intro h0
    have := congrFun (Matrix.eq_zero_of_vecMul_eq_zero (Formalism.L2.Theta.gram_det_ne V) h0) i
    exact hi ((map_eq_zero (D.sp.cm.sig : D.host.E →+* D.host.E)).1 this)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  exact ⟨i, j, mul_ne_zero hi hj⟩

theorem sig_sqrt (D : D7) : D.sp.cm.sig D.host.sqrtMinusD = -D.host.sqrtMinusD := RealChart.star_sqrtMinusD D

theorem ZI_eq {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) :
    ZI V ξ = (tvHom (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj V ξ) (sig_sqrt D)).range := by
  obtain ⟨i, j, hij⟩ := nilM_ne h
  exact closure_eq (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj V ξ) (sig_sqrt D) (RealChart.host_span D)
    (Formalism.L2.Theta.gram_det_ne V) hij

theorem map_one_add {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (a : A)
    (N : Matrix (Fin n) (Fin n) A) : (1 + a • N).map φ = 1 + φ a • N.map φ := by
  rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext k l
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem archM_eq {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (ξ : Fin V.rank → D.host.E) (z : GA D V) (a : AE D)
    (hz : (matHom V z).1 = 1 + a • (nilM V ξ).map (incA D)) (τ : D.what₂.Tau) :
    archM V (θ τ) z = 1 + θ τ (infPart D a) •
      vecMulVec (fun i => tauE D τ (ξ i)) (star (fun i => tauE D τ (ξ i)) ᵥ* gramAt D V τ) := by
  have e : archM V (θ τ) z = ((matHom V z).1).map ((θ τ).comp (infPart D)) := rfl
  rw [e, hz, map_one_add]
  congr 2
  ext k l
  have e2 : ∀ x, ((θ τ).comp (infPart D)) (incA D x) = tauE D τ x := comp_incA hθ τ
  have e3 : ∀ x, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) := tauE_star τ
  rw [Matrix.map_apply, Matrix.map_apply, e2]
  simp only [vecMulVec_apply, vecMul, dotProduct, map_mul, map_sum, e3, Pi.star_apply, gramAt, Matrix.map_apply]

theorem mem_ZI {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) (z : GA D V) :
    z ∈ ZI V ξ ↔ ∃ s, tvHom (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj V ξ) (sig_sqrt D) s = z := by
  rw [ZI_eq h]; rfl

theorem exists_skew {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) {z : GA D V} (hz : z ∈ ZI V ξ) :
    ∃ a : AE D, cA D a + a = 0 ∧ (matHom V z).1 = 1 + a • (nilM V ξ).map (incA D) := by
  obtain ⟨s, hs⟩ := (mem_ZI h z).1 hz
  refine ⟨_, skew_tmul (AF D.host.F) D.sp.cm.sig (sig_sqrt D) s.toAdd, ?_⟩
  rw [← hs]
  rfl

theorem inZe_archM {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ)
    {z : GA D V} (hz : z ∈ ZI V ξ) (τ : D.what₂.Tau) :
    InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (archM V (θ τ) z) := by
  obtain ⟨a, h1, e⟩ := exists_skew h hz
  have h2 := congrArg (fun a => θ τ (infPart D a)) h1
  simp only [RingHom.map_add, RingHom.map_zero] at h2
  rw [comp_cA hθ] at h2
  refine ⟨(θ τ (infPart D a)).im, ?_⟩
  rw [archM_eq hθ ξ z a e τ]
  congr 2
  have h3 := congrArg Complex.re h2
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at h3
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    linarith
  · simp

theorem exists_lift {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ)
    (m : D.what₂.Tau → Mt V.rank) (hm : ∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (m τ)) :
    ∃ z ∈ ZI V ξ, z ∈ GinfC V ∧ ∀ τ, archM V (θ τ) z = m τ := by
  choose s hs using hm
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨a, hf, hi⟩ : ∃ a : AE D, finPart D a = 0 ∧ ∀ τ, θ τ (infPart D a) = (s τ : ℂ) * Complex.I :=
    ⟨σ fun τ => (s τ : ℂ) * Complex.I, hσ.fin _, hσ.comp _⟩
  have hsk : cA D a + a = 0 := by
    refine hσ.ext _ ?_ fun τ => ?_
    · have e : finPart D (cA D a) = sigR (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D a) :=
        LiftUnitary.snd_sigR D.sp.cm.sig a
      rw [RingHom.map_add, e, hf, RingHom.map_zero, add_zero]
    · rw [RingHom.map_add, RingHom.map_add, comp_cA hθ, hi]
      simp
  obtain ⟨z, hz⟩ : ∃ z : GA D V, (matHom V z).1 = 1 + a • (nilM V ξ).map (incA D) :=
    ⟨tv (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj V ξ) a hsk, rfl⟩
  refine ⟨z, Subgroup.subset_closure ⟨a, by rw [hz, add_sub_cancel_left]⟩, ?_, fun τ => ?_⟩
  · refine Units.ext ?_
    show ((matHom V z).1).map (finPart D) = 1
    rw [hz, map_one_add, hf, zero_smul, add_zero]
  · rw [archM_eq hθ ξ z a hz, hi, hs]

theorem fixes {V : HSp D} {ξ : Fin V.rank → D.host.E} (h : IsoVec V ξ) {z : GA D V} (hz : z ∈ ZI V ξ) :
    (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  obtain ⟨a, -, e⟩ := exists_skew h hz
  have e2 : ((nilM V ξ).map (incA D)).mulVec (fun i => incA D (ξ i)) = 0 := by
    funext k
    have := RingHom.map_mulVec (incA D) (nilM V ξ) ξ k
    rw [nil_mulVec _ _ _ h.2] at this
    exact this.symm.trans (incA D).map_zero
  rw [e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, e2, smul_zero, add_zero]

theorem transvection_group : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ e : Multiplicative (AF D.host.F) ≃ₜ* ZI V ξ, (∀ a, ((e a : ZI V ξ) : GA D V) ∈ GQ V ↔ Multiplicative.toAdd a ∈ Set.range (algebraMap D.host.F (AF D.host.F)))) ∧ IsClosed (ZI V ξ : Set (GA D V)) ∧ (∀ z ∈ ZI V ξ, ∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (archM V (θ τ) z)) ∧ (∀ m : D.what₂.Tau → Mt V.rank, (∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (m τ)) → ∃ z ∈ ZI V ξ, z ∈ GinfC V ∧ ∀ τ, archM V (θ τ) z = m τ) ∧ ∀ z ∈ ZI V ξ, (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  intro D θ V hθ ξ h
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (HA (AF D.host.F) D.sp.cm.sig V.gram) :=
    (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram).2.2
  obtain ⟨i, j, hij⟩ := nilM_ne h
  obtain ⟨h1, h2⟩ := exists_equiv (AF D.host.F) D.sp.cm.sig (nilM_sq h) (nilM_adj V ξ) (sig_sqrt D)
    (RealChart.sqrtMinusD_ne D) hij (ZI V ξ) (mem_ZI h)
  exact ⟨h1, h2, fun z hz τ => inZe_archM hθ h hz τ, exists_lift hθ h, fun z hz => fixes h hz⟩

end Main

end GlobalTheory.HolDict.TransvGroup

end
