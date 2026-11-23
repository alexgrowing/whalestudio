import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHermPart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSumInvariantUnipotentTranslate
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermCoord

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] {r : ℕ}

def ct (σ : E →ₐ[F] E) (b : Matrix (Fin r) (Fin r) E) : Matrix (Fin r) (Fin r) E :=
  (b.map σ)ᵀ

def hermF (σ : E →ₐ[F] E) (r : ℕ) : Submodule F (Matrix (Fin r) (Fin r) E) where
  carrier := {b | ct σ b = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [ct, Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    rw [Matrix.add_apply, map_add, h1, h2, Matrix.add_apply]
  zero_mem' := by
    refine Matrix.ext fun i j => ?_
    simp [ct]
  smul_mem' := by
    intro c b hb
    simp only [Set.mem_setOf_eq] at *
    refine Matrix.ext fun i j => ?_
    have h1 := congrFun (congrFun hb i) j
    simp only [ct, Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    rw [Matrix.smul_apply, map_smul, h1, Matrix.smul_apply]

def tF (a b : Matrix (Fin r) (Fin r) E) : F :=
  (1 / 2) * Algebra.trace F E (Matrix.trace (a * b))

theorem tF_comm (a b : Matrix (Fin r) (Fin r) E) : (tF a b : F) = tF b a := by
  rw [tF, tF, Matrix.trace_mul_comm]

def tB (σ : E →ₐ[F] E) : LinearMap.BilinForm F (hermF σ r) :=
  LinearMap.mk₂ F (fun a b => tF a.1 b.1)
    (fun a b c => by
      simp only [tF, Submodule.coe_add, Matrix.add_mul, Matrix.trace_add, map_add, mul_add])
    (fun c a b => by
      simp only [tF, Submodule.coe_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]
      ring)
    (fun a b c => by
      simp only [tF, Submodule.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, mul_add])
    (fun c a b => by
      simp only [tF, Submodule.coe_smul, Matrix.mul_smul, Matrix.trace_smul, map_smul, smul_eq_mul]
      ring)

theorem tB_apply (σ : E →ₐ[F] E) (a b : hermF σ r) : tB σ a b = tF a.1 b.1 := rfl

variable [FiniteDimensional F E] [Algebra.IsSeparable F E] [CharZero F]

theorem exists_tF_ne (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {h : Matrix (Fin r) (Fin r) E}
    (hh : ct σ h = h) (h0 : h ≠ 0) : ∃ k ∈ hermF σ r, (tF h k : F) ≠ 0 := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, h i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Matrix.ext hc)
  obtain ⟨z, hz⟩ := Algebra.trace_surjective F E 1
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs : Algebra.trace F E (σ z) = Algebra.trace F E z := Algebra.trace_eq_of_algEquiv s z
  set m : Matrix (Fin r) (Fin r) E := Matrix.single j i (z * (h i j)⁻¹) with hm
  have hct : ct σ (ct σ m) = m := by
    refine Matrix.ext fun a b => ?_
    simp [ct, hσ]
  have hk : m + ct σ m ∈ hermF σ r := by
    refine Matrix.ext fun a b => ?_
    have e : ct σ (m + ct σ m) a b = σ (m b a) + σ (ct σ m b a) := by
      simp [ct]
    rw [e, Matrix.add_apply]
    have e2 : σ (ct σ m b a) = m a b := congrFun (congrFun hct a) b
    have e3 : σ (m b a) = ct σ m a b := rfl
    rw [e2, e3, add_comm]
  refine ⟨m + ct σ m, hk, ?_⟩
  have h1 : Matrix.trace (h * m) = z := by
    rw [hm, Matrix.trace_mul_single, op_smul_eq_mul, mul_comm z, ← mul_assoc, mul_inv_cancel₀ hij, one_mul]
  have h2 : Matrix.trace (h * ct σ m) = σ z := by
    have ht : ∀ X : Matrix (Fin r) (Fin r) E, Matrix.trace (ct σ X) = σ (Matrix.trace X) := fun X => by
      simp [ct, Matrix.trace, map_sum]
    have hmul : ct σ (m * h) = ct σ h * ct σ m := by
      simp only [ct]
      rw [Matrix.map_mul, Matrix.transpose_mul]
    have h3 : h * ct σ m = ct σ (m * h) := by rw [hmul, hh]
    rw [h3, ht, Matrix.trace_mul_comm, h1]
  rw [tF, Matrix.mul_add, Matrix.trace_add, h1, h2, map_add, hs, hz]
  norm_num

theorem tB_sep (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (a : hermF σ r)
    (h : ∀ b : hermF σ r, (tF a.1 b.1 : F) = 0) : a = 0 := by
  by_contra h0
  obtain ⟨k, hk, hne⟩ := exists_tF_ne σ hσ (r := r) a.2 (fun e => h0 (Subtype.ext e))
  exact hne (h ⟨k, hk⟩)

theorem tB_nondegenerate (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) :
    (tB σ : LinearMap.BilinForm F (hermF σ r)).Nondegenerate :=
  ⟨fun a h => tB_sep σ hσ a h, fun a h => tB_sep σ hσ a fun b => (tF_comm _ _).trans (h b)⟩

theorem exists_dual (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (r : ℕ) :
    ∃ (n : ℕ) (e e' : Fin n → Matrix (Fin r) (Fin r) E),
    (∀ i, ct σ (e i) = e i) ∧ (∀ i, ct σ (e' i) = e' i) ∧
    (∀ i j, (tF (e i) (e' j) : F) = if i = j then 1 else 0) ∧
    (∀ h : Matrix (Fin r) (Fin r) E, ct σ h = h → ∑ i, (tF (e' i) h : F) • e i = h) ∧
    (∀ h : Matrix (Fin r) (Fin r) E, ct σ h = h → ∑ i, (tF (e i) h : F) • e' i = h) := by
  classical
  let b := Module.finBasis F (hermF σ r)
  have hB := tB_nondegenerate (r := r) σ hσ
  let b' := (tB σ : LinearMap.BilinForm F (hermF σ r)).dualBasis hB b
  have hd : ∀ i j, (tF (b' i).1 (b j).1 : F) = if j = i then 1 else 0 := fun i j =>
    LinearMap.BilinForm.apply_dualBasis_left hB b i j
  have hrep : ∀ x : hermF σ r, ∀ i, b.repr x i = tF (b' i).1 x.1 := by
    intro x i
    conv_rhs => rw [← b.sum_repr x]
    have : (tF (b' i).1 (∑ j, b.repr x j • b j : hermF σ r).1 : F) =
        tB σ (b' i) (∑ j, b.repr x j • b j) := rfl
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · have := hd i i
      rw [tB_apply, this]; simp
    · intro j _ hj
      rw [tB_apply, hd, if_neg hj, mul_zero]
    · simp
  refine ⟨_, fun i => (b i).1, fun i => (b' i).1, fun i => (b i).2, fun i => (b' i).2, ?_, ?_, ?_⟩
  · intro i j
    rw [tF_comm, hd]
  · intro h hh
    have hx : (⟨h, hh⟩ : hermF σ r) = ∑ i, (tF (b' i).1 h : F) • b i := by
      conv_lhs => rw [← b.sum_repr ⟨h, hh⟩]
      exact Finset.sum_congr rfl fun i _ => by rw [hrep]
    simpa using congrArg Subtype.val hx.symm
  · intro h hh
    have hx : (⟨h, hh⟩ : hermF σ r) = ∑ i, (tF (b i).1 h : F) • b' i := by
      conv_lhs => rw [← b'.sum_repr ⟨h, hh⟩]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.BilinForm.dualBasis_repr_apply, tB_apply, tF_comm]
    simpa using congrArg Subtype.val hx.symm

end Field

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem sigR_smul_gen (σ : E →ₐ[F] E) (c : R) (x : R ⊗[F] E) : sigR R σ (c • x) = c • sigR R σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, TensorProduct.smul_tmul']
  | add x y h1 h2 => rw [smul_add, map_add, h1, h2, map_add, smul_add]

theorem alg_smul_tmul (c : F) (e : E) :
    algebraMap F R c • ((1 : R) ⊗ₜ[F] e) = (1 : R) ⊗ₜ[F] (c • e) := by
  rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul']

theorem smul_one_tmul (a : R) (e : E) : a • ((1 : R) ⊗ₜ[F] e) = a ⊗ₜ[F] e := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem hmid_herm {r : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (m : Matrix (Fin r) (Fin r) E) :
    ct σ ((1 / 2 : E) • (m + ct σ m)) = (1 / 2 : E) • (m + ct σ m) := by
  refine Matrix.ext fun i j => ?_
  have h2 : σ (2 : E) = 2 := map_ofNat σ 2
  simp [ct, hσ, add_comm, h2, mul_add]

end Gen

section Adelic

variable {D : D7} {r : ℕ}

def halfTrL (D : D7) : AE D →ₗ[AF D.host.F] AF D.host.F :=
  (algebraMap D.host.F (AF D.host.F) (1 / 2)) • Algebra.trace (AF D.host.F) (AE D)

theorem halfTrL_apply (z : AE D) : halfTrL D z = halfTr z := rfl

def uL (m : Matrix (Fin r) (Fin r) D.host.E) : Mx D r r →ₗ[AF D.host.F] AF D.host.F :=
  (halfTrL D) ∘ₗ (Matrix.traceLinearMap (Fin r) (AF D.host.F) (AE D)) ∘ₗ
    (LinearMap.mulLeft (AF D.host.F) (rat m : Mx D r r))

theorem uL_apply (m : Matrix (Fin r) (Fin r) D.host.E) (x : Mx D r r) :
    uL m x = halfTr (Matrix.trace (HMul.hMul (rat m) x : Mx D r r)) := rfl

theorem trace_rat (M : Matrix (Fin r) (Fin r) D.host.E) :
    Matrix.trace (rat M : Mx D r r) = incA D (Matrix.trace M) := by
  simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem uL_rat (m h : Matrix (Fin r) (Fin r) D.host.E) :
    uL m (rat h) = algebraMap D.host.F (AF D.host.F) (tF m h) := by
  rw [uL_apply, ← rat_mul, trace_rat, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA, tF]

theorem algebraMap_smul_rat (c : D.host.F) (M : Matrix (Fin r) (Fin r) D.host.E) :
    algebraMap D.host.F (AF D.host.F) c • (rat M : Mx D r r) = rat (c • M) :=
  Matrix.ext fun i j => alg_smul_tmul (R := AF D.host.F) c (M i j)

theorem rat_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin r) (Fin r) D.host.E) :
    (rat (∑ i ∈ s, f i) : Mx D r r) = ∑ i ∈ s, rat (f i) :=
  map_sum ((incA D).toAddMonoidHom.mapMatrix (m := Fin r) (n := Fin r)) f s

theorem adj_rsmul (a : AF D.host.F) (x : Mx D r r) : adj (a • x) = a • adj x :=
  Matrix.ext fun i j => sigR_smul_gen (R := AF D.host.F) D.sp.cm.sig a (x j i)

set_option synthInstance.maxHeartbeats 400000 in
theorem hermPart_smul (a : AF D.host.F) (x : Mx D r r) :
    GlobalTheory.CompanionTheory.HermVol.hermPart D r (a • x) = a • GlobalTheory.CompanionTheory.HermVol.hermPart D r x := by
  rw [GlobalTheory.CompanionTheory.HermVol.hermPart, GlobalTheory.CompanionTheory.HermVol.hermPart, adj_rsmul, ← smul_add]
  exact Matrix.ext fun i j => mul_smul_comm a (half D) _

theorem hermPart_ratm (m : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.CompanionTheory.HermVol.hermPart D r (rat m) = rat ((1 / 2 : D.host.E) • (m + ct D.sp.cm.sig m)) := by
  rw [GlobalTheory.CompanionTheory.HermVol.hermPart, rat_smul, rat_add]; rfl

theorem single_tmul (i j : Fin r) (a : AF D.host.F) (e : D.host.E) :
    (Matrix.single i j (a ⊗ₜ[D.host.F] e) : Mx D r r) = a • rat (Matrix.single i j e) := by
  refine Matrix.ext fun k l => ?_
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply_same]
    exact (smul_one_tmul (R := AF D.host.F) a e).symm.trans (congrArg (a • ·) (by simp [rat]; rfl))
  · show Matrix.single i j (a ⊗ₜ[D.host.F] e) k l = a • incA D (Matrix.single i j e k l)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ h, Matrix.single_apply_of_ne _ _ _ _ _ h, map_zero, smul_zero]

theorem mx_induction {P : Mx D r r → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (a : AF D.host.F) (m : Matrix (Fin r) (Fin r) D.host.E), P (a • rat m)) (x : Mx D r r) : P x := by
  have hs : ∀ {ι : Type} (s : Finset ι) (f : ι → Mx D r r), (∀ i, P (f i)) → P (∑ i ∈ s, f i) := by
    classical
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact hadd _ _ (hf a) ih
  have h1 : ∀ (i j : Fin r) (z : AE D), P (Matrix.single i j z) := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a e => rw [single_tmul]; exact hgen a _
    | add z w hz hw => rw [Matrix.single_add]; exact hadd _ _ hz hw
  rw [Matrix.matrix_eq_sum_single x]
  exact hs _ _ fun i => hs _ _ fun j => h1 i j _

theorem sum_uL_smul {n : ℕ} (m m' : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (hm : ∀ h : Matrix (Fin r) (Fin r) D.host.E, ct D.sp.cm.sig h = h → ∑ i, (tF (m' i) h : D.host.F) • m i = h)
    {x : Mx D r r} (hx : x ∈ hermA D r) : ∑ i, uL (m' i) x • (rat (m i) : Mx D r r) = x := by
  have key : ∀ y : Mx D r r, ∑ i, uL (m' i) (GlobalTheory.CompanionTheory.HermVol.hermPart D r y) • (rat (m i) : Mx D r r) =
      GlobalTheory.CompanionTheory.HermVol.hermPart D r y := by
    refine mx_induction ?_ ?_ ?_
    · have h0 : GlobalTheory.CompanionTheory.HermVol.hermPart D r (0 : Mx D r r) = 0 := by
        simp [GlobalTheory.CompanionTheory.HermVol.hermPart]
      simp [h0]
    · intro x y hx hy
      rw [GlobalTheory.CompanionTheory.HermVol.hermPart_add]
      simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy]
    · intro a g
      rw [hermPart_smul, hermPart_ratm]
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      congr 1
      simp only [uL_rat, algebraMap_smul_rat]
      rw [← rat_sum, hm _ (hmid_herm _ (fun x => star_star x) g)]
  have := key x
  rwa [GlobalTheory.CompanionTheory.HermVol.hermPart_of_mem hx] at this

end Adelic

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Main

variable {D : D7} {r : ℕ}

theorem continuous_halfTrL : Continuous (halfTrL D) :=
  IsModuleTopology.continuous_of_linearMap (R := AF D.host.F) (halfTrL D)

theorem continuous_uL (m : Matrix (Fin r) (Fin r) D.host.E) : Continuous (uL m) :=
  continuous_halfTrL.comp (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))

theorem continuous_smul_const (z : AE D) : Continuous fun a : AF D.host.F => a • z :=
  IsModuleTopology.continuous_of_linearMap (R := AF D.host.F)
    (LinearMap.toSpanSingleton (AF D.host.F) (AE D) z)

theorem continuous_smul_rat (M : Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun a : AF D.host.F => a • (rat M : Mx D r r) := by
  refine continuous_matrix fun k l => ?_
  simp only [Matrix.smul_apply]
  exact continuous_smul_const _

theorem pairing_comb {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E) (v : Fin n → AF D.host.F)
    (x : Mx D r r) :
    halfTr (Matrix.trace (HMul.hMul (∑ i, v i • (rat (m i) : Mx D r r)) x : Mx D r r)) =
      v ⬝ᵥ fun i => uL (m i) x := by
  let p : Mx D r r →ₗ[AF D.host.F] AF D.host.F :=
    (halfTrL D) ∘ₗ (Matrix.traceLinearMap (Fin r) (AF D.host.F) (AE D)) ∘ₗ
      (LinearMap.mulRight (AF D.host.F) x)
  have h := map_sum p (fun i => v i • (rat (m i) : Mx D r r)) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

theorem continuous_comb {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E) :
    Continuous fun v : Fin n → AF D.host.F => ∑ i, v i • (rat (m i) : Mx D r r) := by
  haveI : IsTopologicalAddGroup (Mx D r r) := (lattice_Mx D r r).1
  exact continuous_finset_sum _ fun i _ => (continuous_smul_rat (m i)).comp (continuous_apply i)

theorem comb_mem {n : ℕ} (m : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (hm : ∀ i, ct D.sp.cm.sig (m i) = m i) (v : Fin n → AF D.host.F) :
    ∑ i, v i • (rat (m i) : Mx D r r) ∈ hermA D r := by
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  show adj (v i • (rat (m i) : Mx D r r)) = _
  rw [adj_rsmul, ← rat_conjTranspose]
  exact congrArg (fun M => v i • (rat M : Mx D r r)) (hm i)

def cEquiv {n : ℕ} (e e' : Fin n → Matrix (Fin r) (Fin r) D.host.E)
    (he' : ∀ i, ct D.sp.cm.sig (e' i) = e' i)
    (hd : ∀ i j, (tF (e i) (e' j) : D.host.F) = if i = j then 1 else 0)
    (hrec : ∀ h : Matrix (Fin r) (Fin r) D.host.E, ct D.sp.cm.sig h = h →
      ∑ i, (tF (e i) h : D.host.F) • e' i = h) :
    (Fin n → AF D.host.F) ≃ₜ+ hermA D r where
  toFun v := ⟨∑ i, v i • (rat (e' i) : Mx D r r), comb_mem e' he' v⟩
  invFun b i := uL (e i) b.1
  left_inv v := by
    funext j
    simp only [map_sum, map_smul, uL_rat, hd, smul_eq_mul]
    simp
  right_inv b := Subtype.ext (sum_uL_smul e' e hrec b.2)
  map_add' v w := Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
  continuous_toFun := (continuous_comb e').subtype_mk _
  continuous_invFun := continuous_pi fun i => (continuous_uL (e i)).comp continuous_subtype_val

end Main

end GlobalTheory.CompanionTheory.HermCoord

namespace GlobalTheory.CompanionTheory.HermCoord

section Measure

variable {D : D7} {r : ℕ}

theorem isTamagawa_map {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)} (h : IsCovolOneH lam 𝓖) {n : ℕ}
    (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r)
    (h1 : ∀ w : Fin n → D.host.F, (c fun i => algebraMap D.host.F (AF D.host.F) (w i)).1 ∈ ratMx D r r)
    (h2 : ∀ b : hermA D r, b.1 ∈ ratMx D r r →
      ∃ w : Fin n → D.host.F, c.symm b = fun i => algebraMap D.host.F (AF D.host.F) (w i)) :
    GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  obtain ⟨t2, -, t3⟩ := Formalism.IndefR.Eqv.G5.af_facts D.host.F
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D r r
  haveI : IsTopologicalAddGroup (Mx D r r) := i1
  haveI : SecondCountableTopology (Mx D r r) := i3
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (AF D.host.F) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → AF D.host.F) := Pi.borelSpace
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  obtain ⟨hH, hF, hm⟩ := h
  haveI := hH
  have hc : Measurable c := c.continuous.measurable
  have hcs : Measurable c.symm := c.symm.continuous.measurable
  let me : hermA D r ≃ᵐ (Fin n → AF D.host.F) := c.symm.toHomeomorph.toMeasurableEquiv
  refine ⟨ContinuousAddEquiv.isAddHaarMeasure_map lam c.symm, c.symm '' 𝓖, ?_, ?_⟩
  · have e1 : lam.map c.symm (c.symm '' 𝓖) = lam (me ⁻¹' (c.symm '' 𝓖)) := me.map_apply _
    rw [e1, show me ⁻¹' (c.symm '' 𝓖) = 𝓖 from Set.preimage_image_eq _ c.symm.injective, hm]
  · let f : hermA D r ≃ (Fin n → AF D.host.F) := c.symm.toEquiv
    have hq : Measure.QuasiMeasurePreserving f.symm (lam.map c.symm) lam := by
      refine ⟨hc, ?_⟩
      have : (lam.map c.symm).map f.symm = lam := by
        show (lam.map c.symm).map c = lam
        rw [Measure.map_map hc hcs]
        have : (c ∘ c.symm) = id := funext fun x => c.apply_symm_apply x
        rw [this, Measure.map_id]
      rw [this]
    let eq : (AddMonoidHom.compLeft (algebraMap D.host.F (AF D.host.F)).toAddMonoidHom (Fin n)).range ≃
        ratHerm D r :=
      { toFun := fun g => ⟨c g.1, by
          obtain ⟨w, hw⟩ := g.2
          rw [← hw]
          exact h1 w⟩
        invFun := fun b => ⟨c.symm b.1, by
          obtain ⟨w, hw⟩ := h2 b.1 b.2
          exact ⟨w, hw.symm⟩⟩
        left_inv := fun g => Subtype.ext (c.symm_apply_apply g.1)
        right_inv := fun b => Subtype.ext (c.apply_symm_apply b.1) }
    refine hF.image_of_equiv f hq eq fun g x => ?_
    show c.symm (c g.1 + x) = g.1 + c.symm x
    exact (c.symm.toAddEquiv.map_add (c g.1) x).trans (congrArg (· + c.symm x) (c.symm_apply_apply g.1))

end Measure

section Target

theorem finEF (D : D7) : FiniteDimensional D.host.F D.host.E :=
  Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E

theorem coords : ∀ (D : D7) (r : ℕ) (lam : Measure (hermA D r)) (𝓖 : Set (hermA D r)), IsCovolOneH lam 𝓖 → ∃ (n : ℕ) (c : (Fin n → AF D.host.F) ≃ₜ+ hermA D r) (u : Mx D r r → Fin n → AF D.host.F) (R : (Fin n → AF D.host.F) → Mx D r r), Continuous u ∧ Continuous R ∧ (∀ x : Mx D r r, x ∈ hermA D r → R (u x) = x) ∧ (∀ (v : Fin n → AF D.host.F) (x : Mx D r r), halfTr (Matrix.trace (HMul.hMul (c v).1 x : Mx D r r)) = v ⬝ᵥ u x) ∧ GlobalTheory.SWLit.IsTamagawa D.host.F (Fin n) (lam.map c.symm) := by
  intro D r lam 𝓖 h
  haveI := finEF D
  obtain ⟨n, e, e', he, he', hd, hrec, hrec'⟩ := exists_dual (F := D.host.F) D.sp.cm.sig (fun x => star_star x) r
  refine ⟨n, cEquiv e e' he' hd hrec', fun x i => uL (e' i) x, fun w => ∑ i, w i • (rat (e i) : Mx D r r),
    continuous_pi fun i => continuous_uL (e' i), continuous_comb e, fun x hx => sum_uL_smul e e' hrec hx, ?_, ?_⟩
  · intro v x
    exact pairing_comb e' v x
  · refine isTamagawa_map h _ ?_ ?_
    · intro w
      show ∑ i, algebraMap D.host.F (AF D.host.F) (w i) • (rat (e' i) : Mx D r r) ∈ ratMx D r r
      simp only [algebraMap_smul_rat]
      rw [← rat_sum]
      exact rat_mem _
    · rintro b ⟨γ, hγ⟩
      replace hγ : rat γ = b.1 := hγ
      refine ⟨fun i => tF (e i) γ, funext fun i => ?_⟩
      show uL (e i) b.1 = _
      rw [← hγ, uL_rat]

end Target

end GlobalTheory.CompanionTheory.HermCoord
