import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasND

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.TW.Twp

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def rp (d : SD σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) : F := Algebra.trace F E (Yᵀ * d.A.J * W.map σ).trace

def eq (d : SD σ) (q : Ix d) : Matrix (Fin d.m) (Fin d.n) E := Matrix.of fun i j => if (i, j) = (q.1, q.2.1) then d.bs q.2.2 else 0

def rc (d : SD σ) : Matrix (Fin d.m) (Fin d.n) E ≃ₗ[F] (Ix d → F) where
  toFun Y k := d.bs.repr (Y k.1 k.2.1) k.2.2
  invFun a := Matrix.of fun i j => ∑ k, a (i, j, k) • d.bs k
  left_inv Y := by
    ext i j
    simp only [Matrix.of_apply]
    exact d.bs.sum_repr (Y i j)
  right_inv a := by
    funext ⟨i, j, k⟩
    simp only [Matrix.of_apply]
    exact congrFun (d.bs.repr_sum_self fun k' => a (i, j, k')) k
  map_add' Y Y' := by funext k; simp
  map_smul' c Y := by funext k; simp

theorem rp_add_left (d : SD σ) (Y Y' W : Matrix (Fin d.m) (Fin d.n) E) : rp d (Y + Y') W = rp d Y W + rp d Y' W := by
  simp only [rp, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, map_add]

theorem rp_smul_left (d : SD σ) (c : F) (Y W : Matrix (Fin d.m) (Fin d.n) E) : rp d (c • Y) W = c * rp d Y W := by
  simp only [rp, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, map_smul, smul_eq_mul]

def Lm (d : SD σ) (ε : ℤˣ) : (Ix d → F) →ₗ[F] (Ix d → F) where
  toFun a q := ((ε : ℤ) : F) * rp d ((rc d).symm a) (eq d q)
  map_add' a b := by
    funext q
    simp only [map_add, rp_add_left, Pi.add_apply]
    ring
  map_smul' c a := by
    funext q
    simp only [map_smul, rp_smul_left, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem ek_eq (d : SD σ) (q : Ix d) : ek d q = incM F (eq d q) := by
  obtain ⟨i0, j0, k0⟩ := q
  ext i j
  simp only [ek, SD.cmb, incM, Matrix.map_apply, eq, Matrix.of_apply]
  show _ = (1 : AF F) ⊗ₜ[F] _
  by_cases h : (i, j) = (i0, j0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [if_pos rfl, Finset.sum_eq_single k0]
    · simp
    · intro b _ hb
      have : ((i, j, k0) : Ix d) ≠ (i, j, b) := fun e => hb (by simp at e; exact e.symm)
      simp [this]
    · simp
  · rw [if_neg h, TensorProduct.tmul_zero]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ((i0, j0, k0) : Ix d) ≠ (i, j, k) := fun e => h (by simp at e; rw [e.1, e.2.1])
    simp [this]

theorem crd_eq_sum (d : SD σ) (Z : Mx F E d.m d.n) : Z = ∑ q, d.crd Z q • incM F (eq d q) := by
  conv_lhs => rw [← cmb_crd d Z, cmb_sum]
  simp only [ek_eq]

def ttL (d : SD σ) (X : Mx F E d.m d.n) : Mx F E d.m d.n →ₗ[AF F] AF F where
  toFun Z := d.tt (d.gram X Z)
  map_add' Z Z' := by
    have e : (Z + Z').map (cA σ) = Z.map (cA σ) + Z'.map (cA σ) := Matrix.map_add _ (map_add _) _ _
    simp only [SD.tt, SD.gram, e, Matrix.mul_add, Matrix.trace_add, map_add]
  map_smul' a Z := by
    have e : (a • Z).map (cA σ) = a • Z.map (cA σ) := Matrix.map_smul _ a (fun x => map_smul (cA σ) a x) _
    simp only [SD.tt, SD.gram, e, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]

theorem tt_gram_sum (d : SD σ) (X : Mx F E d.m d.n) (c : Ix d → AF F) (W : Ix d → Mx F E d.m d.n) :
    d.tt (d.gram X (∑ q, c q • W q)) = ∑ q, c q * d.tt (d.gram X (W q)) := by
  have h := map_sum (ttL d X) (fun q => c q • W q) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

omit [NumberField F] [NumberField E] in
theorem trace_tmul' (R : Type) [CommRing R] [Algebra F R] [FiniteDimensional F E] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem tt_gram_inc (d : SD σ) (Y W : Matrix (Fin d.m) (Fin d.n) E) :
    d.tt (d.gram (incM F Y) (incM F W)) = algebraMap F (AF F) (rp d Y W) := by
  have e : d.gram (incM F Y) (incM F W) = incM F (Yᵀ * d.A.J * W.map σ) := by
    rw [SD.gram, PositivityTheory.SiegelWeilFormula.TBij.cA_incM, ← PositivityTheory.SiegelWeilFormula.TBij.incM_transpose, ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul,
      ← PositivityTheory.SiegelWeilFormula.TBij.incM_mul]
  rw [e, SD.tt, rp]
  have h2 : (incM F (Yᵀ * d.A.J * W.map σ)).trace = (1 : AF F) ⊗ₜ[F] (Yᵀ * d.A.J * W.map σ).trace := by
    simp only [Matrix.trace, incM, Matrix.diag_apply, Matrix.map_apply, TensorProduct.tmul_sum]
    rfl
  rw [h2, trace_tmul', one_mul]

theorem pair_eq (d : SD σ) (ε : ℤˣ) (Y : Matrix (Fin d.m) (Fin d.n) E) (Z : Mx F E d.m d.n) :
    ((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z) = ∑ q, d.crd Z q * algebraMap F (AF F) (Lm d ε (rc d Y) q) := by
  conv_lhs => rw [crd_eq_sum d Z]
  rw [tt_gram_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [tt_gram_inc]
  simp only [Lm, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, map_mul, map_intCast]
  ring

theorem tr_single (d : SD σ) (M : Matrix (Fin d.n) (Fin d.m) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    (M * (eq d (i, j, k)).map σ).trace = M j i * σ (d.bs k) := by
  rw [Matrix.trace, Finset.sum_eq_single j]
  · rw [Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single i]
    · simp [eq]
    · intro b _ hb; simp [eq, hb]
    · simp
  · intro b _ hb
    rw [Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun c _ => by simp [eq, hb]
  · simp

theorem rp_eq (d : SD σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (i : Fin d.m) (j : Fin d.n) (k : Fin 2) :
    rp d Y (eq d (i, j, k)) = Algebra.trace F E ((Yᵀ * d.A.J) j i * σ (d.bs k)) := by
  rw [rp, tr_single]

theorem rp_nondeg (d : SD σ) (Y : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ q, rp d Y (eq d q) = 0) : Y = 0 := by
  have hσ : Function.Surjective σ := (AlgHom.bijective σ).2
  have key : ∀ (i : Fin d.m) (j : Fin d.n), (Yᵀ * d.A.J) j i = 0 := by
    intro i j
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    obtain ⟨e, rfl⟩ := hσ z
    rw [Algebra.traceForm_apply, ← d.bs.sum_repr e, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [AlgHom.map_smul_of_tower, mul_smul_comm, map_smul, ← rp_eq, h, smul_zero]
  have hdet : IsUnit d.A.J.det := isUnit_iff_ne_zero.2 (PositivityTheory.SiegelWeilFormula.KWhit.meas_detA d)
  have h0 : Yᵀ * d.A.J = 0 := by ext j i; exact key i j
  have h1 : Yᵀ = 0 := by
    have := congrArg (· * d.A.J⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one, Matrix.zero_mul] at this
    exact this
  rw [← Matrix.transpose_transpose Y, h1, Matrix.transpose_zero]

theorem Lm_inj (d : SD σ) (ε : ℤˣ) : Function.Injective (Lm d ε) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have hε : ((ε : ℤ) : F) ≠ 0 := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hY : (rc d).symm a = 0 := by
    refine rp_nondeg d _ fun q => ?_
    have := congrFun ha q
    simp only [Lm, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hε
  simpa using congrArg (rc d) hY

end PositivityTheory.SiegelWeilFormula.TW.Twp

end
