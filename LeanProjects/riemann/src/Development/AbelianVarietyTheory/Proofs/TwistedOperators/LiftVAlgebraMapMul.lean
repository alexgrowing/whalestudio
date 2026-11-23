import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqNormCompletionTensorOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_mul (v : Pl F) (x y : Fv F v) :
    GlobalTheory.LatVac.liftV v (x * y) = GlobalTheory.LatVac.liftV v x * GlobalTheory.LatVac.liftV v y :=
  Prod.ext (by show (0 : Ainf F) = 0 * 0; simp)
    (by show GlobalTheory.AdelicU.singleFin v (x * y) = GlobalTheory.AdelicU.singleFin v x * GlobalTheory.AdelicU.singleFin v y
        exact GlobalTheory.AdelicU.singleFin_mul v x y)

theorem liftV_algebraMap_mul (v : Pl F) (c : F) (x : Fv F v) :
    GlobalTheory.LatVac.liftV v (algebraMap F (Fv F v) c * x) = algebraMap F (AF F) c * GlobalTheory.LatVac.liftV v x := by
  rw [← Algebra.smul_def, map_smul, Algebra.smul_def]

def Mult {d : ℕ} (W : Spc F E d) (v : Pl F) (c : AE F E) : Prop :=
  ∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => c * z i) ∈ GlobalTheory.InertSph.latAt W v

theorem mult_of_gen {d : ℕ} (W : Spc F E d) (v : Pl F) (c : AE F E)
    (h : ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F → ∀ y ∈ W.L,
      (fun i => c * (a • fun j => inclR (F := F) (AF F) (y j)) i) ∈ GlobalTheory.InertSph.latAt W v) : Mult W v c := by
  intro z hz
  unfold GlobalTheory.InertSph.latAt at hz
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hai, y, hy, rfl⟩ := hx
    exact h a ha hai y hy
  | zero =>
    have : (fun i => c * (0 : Fin d → AE F E) i) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun i => c * (x + y) i) = (fun i => c * x i) + (fun i => c * y i) := by ext i; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : (fun i => c * (-x) i) = -(fun i => c * x i) := by ext i; simp
    rw [this]; exact neg_mem hx

theorem mult_algebraMap {d : ℕ} (W : Spc F E d) (v : Pl F) (f : AF F)
    (hf : evFin F v f ∈ v.adicCompletionIntegers F) : Mult W v (algebraMap (AF F) (AE F E) f) := by
  refine mult_of_gen W v _ fun a ha hai y hy => ?_
  have e : (fun i => algebraMap (AF F) (AE F E) f * (a • fun j => inclR (F := F) (AF F) (y j)) i) =
      (f * a) • fun j => inclR (F := F) (AF F) (y j) := by
    ext i; simp only [Pi.smul_apply, Algebra.smul_def, map_mul, mul_assoc]
  rw [e]
  refine AddSubgroup.subset_closure ⟨f * a, ?_, ?_, y, hy, rfl⟩
  · intro u hu
    have := ha u hu
    rw [smul_eq_mul] at this ⊢
    rw [mul_left_comm, this, mul_zero]
  · rw [map_mul]; exact mul_mem hf hai

theorem mult_inclR {d : ℕ} (W : Spc F E d) (v : Pl F) (o : 𝓞 E) :
    Mult W v (inclR (F := F) (AF F) (o : E)) := by
  refine mult_of_gen W v _ fun a ha hai y hy => ?_
  have e : (fun i => inclR (F := F) (AF F) (o : E) * (a • fun j => inclR (F := F) (AF F) (y j)) i) =
      a • fun j => inclR (F := F) (AF F) ((o • y) j) := by
    ext i
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rw [show (algebraMap (𝓞 E) E o) = (o : E) from rfl]
    ring
  rw [e]
  exact AddSubgroup.subset_closure ⟨a, ha, hai, o • y, W.L.smul_mem o hy, rfl⟩

theorem mult_add {d : ℕ} {W : Spc F E d} {v : Pl F} {c c' : AE F E} (h : Mult W v c) (h' : Mult W v c') :
    Mult W v (c + c') := fun z hz => by
  have : (fun i => (c + c') * z i) = (fun i => c * z i) + (fun i => c' * z i) := by ext i; simp [add_mul]
  rw [this]; exact add_mem (h z hz) (h' z hz)

theorem mult_mul {d : ℕ} {W : Spc F E d} {v : Pl F} {c c' : AE F E} (h : Mult W v c) (h' : Mult W v c') :
    Mult W v (c * c') := fun z hz => by
  have := h _ (h' z hz)
  simpa [mul_assoc] using this

end GlobalTheory.SplitConj
end

noncomputable section

namespace GlobalTheory.SplitConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open IsDedekindDomain.HeightOneSpectrum in

theorem exists_idem_coeffs (v : Pl F) (b c : 𝓞 F) (hc : c ∈ v.asIdeal) (hb : b ∉ v.asIdeal) :
    ∃ m k : v.adicCompletionIntegers F,
      m * m - algebraMap (𝓞 F) _ c * (k * k) = m ∧ m * k + m * k - algebraMap (𝓞 F) _ b * (k * k) = k ∧
      m + m - algebraMap (𝓞 F) _ b * k = 1 := by
  set ι := algebraMap (𝓞 F) (v.adicCompletionIntegers F) with hι
  have hunit : ∀ e : 𝓞 F, e ∉ v.asIdeal → IsUnit (ι e) := fun e he => by
    by_contra h
    exact he ((GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff v e).1 ((IsLocalRing.mem_maximalIdeal _).2 h))
  obtain ⟨r, hr⟩ := GlobalTheory.InertUnitNorm.exists_root_quadratic_of_approx v (ι b) (ι c) 0
    ((GlobalTheory.InertUnitNorm.mem_maximalIdeal_iff_valued_lt_one v _).1
      (by simpa using (GlobalTheory.InertUnitNorm.algebraMap_mem_maximalIdeal_iff v c).2 hc))
    (by simpa using hunit b hb)
  have hD : b ^ 2 - 4 * c ∉ v.asIdeal := by
    intro h
    have h4 : 4 * c ∈ v.asIdeal := Ideal.mul_mem_left _ _ hc
    have : b ^ 2 ∈ v.asIdeal := by simpa using Ideal.add_mem _ h h4
    exact hb (v.isPrime.mem_of_pow_mem 2 this)
  have hsq : (2 * r + ι b) ^ 2 = ι (b ^ 2 - 4 * c) := by
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    linear_combination 4 * hr
  have hd : IsUnit (2 * r + ι b) := (isUnit_pow_iff two_ne_zero).1 (hsq ▸ hunit _ hD)
  obtain ⟨dinv, hdinv⟩ := hd.exists_right_inv
  refine ⟨(ι b + r) * dinv, dinv, ?_, ?_, ?_⟩
  · linear_combination (ι b + r) * dinv * hdinv - dinv ^ 2 * hr
  · linear_combination dinv * hdinv
  · linear_combination hdinv

theorem inclR_algebraMap (x : F) :
    inclR (F := F) (AF F) (algebraMap F E x) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) x) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact Algebra.TensorProduct.includeRight.commutes x

theorem cA_inclR (σ : E →ₐ[F] E) (y : E) : cA σ (inclR (F := F) (AF F) y) = inclR (F := F) (AF F) (σ y) := by
  show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] y) = (1 : AF F) ⊗ₜ[F] σ y
  simp

theorem exists_adelic_idem (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F) (a : 𝓞 E) (b c : 𝓞 F)
    (hq : (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0)
    (hσa : σ (a : E) = -algebraMap F E (b : F) - a) (hc : c ∈ v.asIdeal) (hb : b ∉ v.asIdeal) :
    ∃ Eid : AE F E, Eid * Eid = Eid ∧ Eid + cA σ Eid = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) ∧
      Eid * cA σ Eid = 0 ∧ ∀ z ∈ GlobalTheory.InertSph.latAt W v, (fun i => Eid * z i) ∈ GlobalTheory.InertSph.latAt W v := by
  obtain ⟨m, k, h1, h2, h3⟩ := exists_idem_coeffs v b c hc hb
  have co : ∀ e : 𝓞 F, ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) e : v.adicCompletionIntegers F) : Fv F v) =
      algebraMap F (Fv F v) (e : F) := GlobalTheory.InertUnitNorm.coe_algebraMap_adicCompletionIntegers v
  have c1 := congrArg (fun t : v.adicCompletionIntegers F => (t : Fv F v)) h1
  have c2 := congrArg (fun t : v.adicCompletionIntegers F => (t : Fv F v)) h2
  have c3 := congrArg (fun t : v.adicCompletionIntegers F => (t : Fv F v)) h3
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, co, OneMemClass.coe_one] at c1 c2 c3
  set L := GlobalTheory.LatVac.liftV (F := F) v
  set ιA := algebraMap (AF F) (AE F E)
  set M : AF F := L (m : Fv F v)
  set K : AF F := L (k : Fv F v)
  set e1 : AF F := L 1
  set b' : AF F := algebraMap F (AF F) (b : F)
  set c' : AF F := algebraMap F (AF F) (c : F)
  have r1 : M * M - c' * (K * K) = M := by
    have := congrArg L c1
    rwa [map_sub, liftV_mul, liftV_algebraMap_mul, liftV_mul] at this
  have r2 : M * K + M * K - b' * (K * K) = K := by
    have := congrArg L c2
    rwa [map_sub, map_add, liftV_mul, liftV_algebraMap_mul, liftV_mul] at this
  have r3 : M + M - b' * K = e1 := by
    have := congrArg L c3
    rwa [map_sub, map_add, liftV_algebraMap_mul] at this
  have r4 : e1 * M = M := by rw [← liftV_mul, one_mul]
  have r5 : e1 * K = K := by rw [← liftV_mul, one_mul]
  set j : AE F E := inclR (F := F) (AF F) (a : E)
  have hj : j * j + ιA b' * j + ιA c' = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hq
    simp only [map_add, map_mul, map_pow, inclR_algebraMap, map_zero, pow_two] at this
    exact this
  have hσj : cA σ j = -ιA b' - j := by
    rw [cA_inclR, hσa, map_sub, map_neg, inclR_algebraMap]
  have hσι : ∀ x : AF F, cA σ (ιA x) = ιA x := fun x => (cA σ).commutes x
  set Eid := ιA M + ιA K * j
  have hσE : cA σ Eid = ιA M + ιA K * (-ιA b' - j) := by
    simp only [Eid, map_add, map_mul, hσι, hσj]
  have s1 := congrArg ιA r1
  have s2 := congrArg ιA r2
  have s3 := congrArg ιA r3
  have s4 := congrArg ιA r4
  have s5 := congrArg ιA r5
  simp only [map_sub, map_add, map_mul] at s1 s2 s3 s4 s5
  have E1 : Eid * Eid = Eid := by
    linear_combination s1 + s2 * j + ιA K * ιA K * hj
  have E2 : Eid + cA σ Eid = ιA e1 := by
    rw [hσE]; linear_combination s3
  refine ⟨Eid, E1, E2, ?_, ?_⟩
  · have : cA σ Eid = ιA e1 - Eid := by rw [← E2]; ring
    rw [this]
    linear_combination s4 + j * s5 - E1
  · have hM : Mult W v (ιA M) := mult_algebraMap W v M (by
      rw [show M = L (m : Fv F v) from rfl, GlobalTheory.LatVac.evFin_liftV]; exact m.2)
    have hK : Mult W v (ιA K) := mult_algebraMap W v K (by
      rw [show K = L (k : Fv F v) from rfl, GlobalTheory.LatVac.evFin_liftV]; exact k.2)
    exact mult_add hM (mult_mul hK (mult_inclR W v a))

end GlobalTheory.SplitConj
end

noncomputable section

namespace GlobalTheory.SplitConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem diag_antiT_sum (d : ℕ) :
    (2 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
      (diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
          ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) +
        (GlobalTheory.InertDbl.antiCols d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
          ((GlobalTheory.InertDbl.antiCols d : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
  have h1 : ∀ (P Q R S : Matrix (Fin d) (Fin d) (AE F E)),
      (Matrix.fromRows P Q : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
          ((Matrix.fromRows R S : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) =
        Matrix.fromBlocks (P * Rᵀ) (P * Sᵀ) (Q * Rᵀ) (Q * Sᵀ) := by
    intro P Q R S
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.transpose_apply]
  rw [diagCols, GlobalTheory.InertDbl.antiCols, h1, h1, Matrix.fromBlocks_add, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp [two_smul]

theorem conj_eq_sq {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl F} (n : GlobalTheory.InertDbl.UD σ W)
    (hn : n ∈ GlobalTheory.InertDbl.NabD σ W v) (s : GlobalTheory.InertDbl.UD σ W) (x y : AE F E) (w : AF F) (hw : evFin F v w = 0)
    (hyx : y - 2 * x = algebraMap (AF F) (AE F E) w)
    (hd : GlobalTheory.InertDbl.matD s * diagCols (Fin d) = diagCols (Fin d) * (x • (1 : Matrix (Fin d) (Fin d) (AE F E))))
    (ha : GlobalTheory.InertDbl.matD s * GlobalTheory.InertDbl.antiCols d = GlobalTheory.InertDbl.antiCols d * (y • (1 : Matrix (Fin d) (Fin d) (AE F E)))) :
    s * n * s⁻¹ = n * n := by
  obtain ⟨⟨hAt, -⟩, hna, b, hnb⟩ := hn
  let D : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := diagCols (Fin d)
  let A : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E) := GlobalTheory.InertDbl.antiCols d
  let Mn : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.InertDbl.matD n
  let Ms : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.InertDbl.matD s
  have hnb' : Mn * D = D + A * b := hnb
  have hna' : Mn * A = A := hna
  have hd' : Ms * D = x • D := by
    have : Ms * D = D * (x • (1 : Matrix (Fin d) (Fin d) (AE F E))) := hd
    rw [this, Matrix.mul_smul, Matrix.mul_one]
  have ha' : Ms * A = y • A := by
    have : Ms * A = A * (y • (1 : Matrix (Fin d) (Fin d) (AE F E))) := ha
    rw [this, Matrix.mul_smul, Matrix.mul_one]
  have hAt' : w • (Mn - 1) = 0 := hAt w hw
  have hb : w • b = 0 := by
    have h3 : (Mn - 1) * D = A * b := by rw [Matrix.sub_mul, hnb', Matrix.one_mul, add_sub_cancel_left]
    have h4 : A * (w • b) = 0 := by rw [Matrix.mul_smul, ← h3, ← Matrix.smul_mul, hAt', Matrix.zero_mul]
    ext i j
    have h5 := congrFun (congrFun h4 (Sum.inl i)) j
    simp only [A, GlobalTheory.InertDbl.antiCols, Matrix.fromRows_mul, Matrix.one_mul] at h5
    simpa using h5
  have hyb : y • b = (2 * x) • b := by
    have : y = 2 * x + algebraMap (AF F) (AE F E) w := by rw [← hyx]; ring
    rw [this, add_smul, algebraMap_smul, hb, add_zero]
  have hyAb : y • (A * b) = (2 * x) • (A * b) := by rw [← Matrix.mul_smul, hyb, Matrix.mul_smul]
  have e1 : Ms * Mn * D = x • D + (2 * x) • (A * b) := by
    rw [Matrix.mul_assoc, hnb', Matrix.mul_add, hd', ← Matrix.mul_assoc, ha', Matrix.smul_mul, hyAb]
  have e2 : Mn * Mn * Ms * D = x • D + (2 * x) • (A * b) := by
    rw [Matrix.mul_assoc, hd', Matrix.mul_smul, Matrix.mul_assoc, hnb', Matrix.mul_add, hnb', ← Matrix.mul_assoc Mn A b, hna',
      smul_add, smul_add, two_mul, add_smul]
    abel
  have e3 : Ms * Mn * A = Mn * Mn * Ms * A := by
    rw [Matrix.mul_assoc, hna', ha', Matrix.mul_assoc, ha', Matrix.mul_smul, Matrix.mul_assoc, hna', hna']
  have key : ∀ Z : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E), (2 : AF F) • Z = Z * D * Dᵀ + Z * A * Aᵀ := by
    intro Z
    have hsum : (2 : AF F) • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = D * Dᵀ + A * Aᵀ := diag_antiT_sum d
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← hsum, Matrix.mul_smul, Matrix.mul_one]
  have h2 : (2 : AF F) • (Ms * Mn) = (2 : AF F) • (Mn * Mn * Ms) := by
    rw [key, key, e1, e2, e3]
  have hXY : Ms * Mn = Mn * Mn * Ms := by
    have := congrArg (fun Z => (⅟2 : AF F) • Z) h2
    simp only [smul_smul, invOf_mul_self, one_smul] at this
    exact this
  have hsn : s * n = n * n * s := Subtype.ext (Units.ext hXY)
  rw [hsn, mul_inv_cancel_right]

end GlobalTheory.SplitConj
end
