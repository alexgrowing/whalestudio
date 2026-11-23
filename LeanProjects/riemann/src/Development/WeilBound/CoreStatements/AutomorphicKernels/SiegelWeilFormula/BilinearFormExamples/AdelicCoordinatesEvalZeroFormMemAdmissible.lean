import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa

open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

set_option linter.unusedSectionVars false

theorem adelicCoordinatesEvalZeroForm_mem_admissible (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) * g (fun i => ((0 : κ → AF F) i).2) = _
  have e1 : ∀ i, ((0 : κ → AF F) i).1 = 0 := fun _ => rfl
  have e2 : (fun i => ((0 : κ → AF F) i).2) = (0 : κ → FiniteAdeleRing (𝓞 F) F) := rfl
  simp only [e1, e2, map_zero]
  simp [mul_comm]
  left; rfl

theorem incM_mul' {a b c : Type} [Fintype b] (X : Matrix a b E) (Y : Matrix b c E) :
    incM F (X * Y) = incM F X * incM F Y := Matrix.map_mul

theorem incM_transpose' {a b : Type} (X : Matrix a b E) : incM F Xᵀ = (incM F X)ᵀ := Matrix.transpose_map

theorem incM_add' {a b : Type} (X Y : Matrix a b E) : incM F (X + Y) = incM F X + incM F Y := by
  ext i j; simp [incM]

theorem frame_decomp {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (v : Matrix (Fin m) (Fin n ⊕ Fin n) E) :
    v = (v * (b⁻¹).1ᵀ).toCols₁ * b.1.toCols₁ᵀ + (v * (b⁻¹).1ᵀ).toCols₂ * b.1.toCols₂ᵀ := by
  rw [← Matrix.fromCols_mul_fromRows, ← Matrix.transpose_fromCols, Matrix.fromCols_toCols, Matrix.fromCols_toCols,
    Matrix.mul_assoc, ← Matrix.transpose_mul, b.mul_inv, Matrix.transpose_one, Matrix.mul_one]

theorem crdB_incM {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Matrix (Fin m) (Fin n) E) (k : Fin m × Fin n × Fin 2) :
    crdB bs (incM F X) k = algebraMap F (AF F) (bs.repr (X k.1 k.2.1) k.2.2) := by
  simp [crdB, incM, inclR, Algebra.TensorProduct.basis_repr_tmul]

theorem diag_eq {n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (t : GL (Fin n) E) (ht : b.1.toCols₁ = diagCols (Fin n) * t.1) :
    (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) = incM F b.1.toCols₁ * incM F (t⁻¹).1 := by
  have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t.1 : Matrix (Fin n) (Fin n) E) := ht
  have e3 : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t.1 : Matrix (Fin n) (Fin n) E) * (t⁻¹).1 =
      diagCols (Fin n) := by
    rw [Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
  rw [← incM_mul', ht', e3]
  ext i j; rcases i with i | i <;> by_cases h : i = j <;> simp [incM, diagCols, h]

theorem fst_diag {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E) (hb : IsFrame2 σ Y b)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2))
    (hd : IsAdapted bs A Y b dd) (z : Matrix (Fin m) (Fin n) (AE F E)) :
    (dd.e (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ)).1 = 0 := by
  obtain ⟨t, ht⟩ := hb.2
  have e : z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ =
      (z * (incM F (t⁻¹).1)ᵀ) * (incM F b.1.toCols₁)ᵀ + (0 : Matrix (Fin m) (Fin n) (AE F E)) * (incM F b.1.toCols₂)ᵀ := by
    rw [diag_eq b t ht, Matrix.transpose_mul, Matrix.zero_mul, add_zero, Matrix.mul_assoc]
  rw [e, hd]
  funext k; simp [crdB]

theorem trace_inclR' [FiniteDimensional F E] (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def EkE {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (k : Fin m × Fin n × Fin 2) : Matrix (Fin m) (Fin n) E :=
  Matrix.single k.1 k.2.1 (bs k.2.2)

theorem Ek_eq {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (k : Fin m × Fin n × Fin 2) : Ek bs k = incM F (EkE bs k) := by
  ext i j; by_cases h1 : k.1 = i <;> by_cases h2 : k.2.1 = j <;> simp [Ek, EkE, incM, h1, h2, inclR]

theorem Bf_incM [FiniteDimensional F E] {m n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (X Z : Matrix (Fin m) (Fin n) E) :
    Bf σ J (incM F X) (incM F Z) = algebraMap F (AF F) (Algebra.trace F E (Xᵀ * J * Z.map σ).trace) := by
  have h1 : (incM F Z).map (cA σ) = incM F (Z.map σ) := by ext; rfl
  rw [Bf, h1, ← incM_transpose', ← incM_mul', ← incM_mul', ← trace_inclR']
  congr 1
  rw [Matrix.trace, Matrix.trace, map_sum]
  rfl

theorem e_rat {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2))
    (hd : IsAdapted bs A Y b dd) (v : Matrix (Fin m) (Fin n ⊕ Fin n) E) :
    ∃ c : Fin m × Fin n × Fin 2 → F, dd.e (incM F v) =
      (fun k => algebraMap F (AF F) (bs.repr ((v * (b⁻¹).1ᵀ).toCols₂ k.1 k.2.1) k.2.2),
        fun k => algebraMap F (AF F) (c k)) := by
  have : FiniteDimensional F E := Module.Finite.of_basis bs
  set Q := v * (b⁻¹).1ᵀ
  have hv : incM F v = incM F Q.toCols₁ * (incM F b.1.toCols₁)ᵀ + incM F Q.toCols₂ * (incM F b.1.toCols₂)ᵀ := by
    conv_lhs => rw [frame_decomp b v]
    rw [incM_add', incM_mul', incM_mul', incM_transpose', incM_transpose']
  refine ⟨fun k => Algebra.trace F E (Q.toCols₁ᵀ * A.J * (EkE bs k).map σ).trace, ?_⟩
  rw [hv, hd]
  refine Prod.ext (funext fun k => crdB_incM bs _ k) (funext fun k => ?_)
  show Bf σ A.J (incM F Q.toCols₁) (Ek bs k) = _
  rw [Ek_eq, Bf_incM]

theorem evaluation_zero_unipotent_kill {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E) (hb : IsFrame2 σ Y b)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2))
    (hd : IsAdapted bs A Y b dd) (ψ : AddChar (AF F) ℂ) (z : Matrix (Fin m) (Fin n) (AE F E))
    (Φ : (Fin m × Fin n × Fin 2 → AF F) → ℂ) :
    ev0 _ (dd.rho ψ (z * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E))ᵀ) Φ) = ev0 _ Φ := by
  have h0 := fst_diag bs A Y b hb dd hd z
  simp [ev0, Darboux.rho, schr, h0]

def Cm {n : ℕ} (b : GL (Fin n ⊕ Fin n) E) : Matrix (Fin n) (Fin n) E :=
  (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) E) (-1) * (b⁻¹).1ᵀ).toCols₂

theorem toCols₂_anti {m n : ℕ} (b : GL (Fin n ⊕ Fin n) E) (y : Matrix (Fin m) (Fin n) E) :
    (Matrix.fromCols y (-y) * (b⁻¹).1ᵀ).toCols₂ = y * Cm b := by
  have e : Matrix.fromCols y (-y) = y * Matrix.fromCols (1 : Matrix (Fin n) (Fin n) E) (-1) := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_one]
  rw [e, Matrix.mul_assoc]
  rfl

theorem Cm_inj {m n : ℕ} {σ : E →ₐ[F] E} {Y : Spc F E n} (b : GL (Fin n ⊕ Fin n) E) (hb : IsFrame2 σ Y b)
    (y : Matrix (Fin m) (Fin n) E) (hy : y * Cm b = 0) : y = 0 := by
  obtain ⟨t, ht⟩ := hb.2
  have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t.1 : Matrix (Fin n) (Fin n) E) := ht
  have h := frame_decomp b (Matrix.fromCols y (-y))
  rw [toCols₂_anti, hy, Matrix.zero_mul, add_zero, ht', Matrix.transpose_mul, ← Matrix.mul_assoc, diagCols,
    Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.mul_fromCols, Matrix.mul_one] at h
  obtain ⟨h1, h2⟩ := Matrix.fromCols_inj h
  ext i j
  have := congrFun (congrFun (h1.trans h2.symm) i) j
  simp only [Matrix.neg_apply, Matrix.zero_apply] at this ⊢
  linear_combination (1 / 2 : E) * this

def xiEquiv {m n : ℕ} {σ : E →ₐ[F] E} {Y : Spc F E n} (bs : Module.Basis (Fin 2) F E) (b : GL (Fin n ⊕ Fin n) E)
    (hb : IsFrame2 σ Y b) : Matrix (Fin m) (Fin n) E ≃ (Fin m × Fin n × Fin 2 → F) :=
  let L : Matrix (Fin m) (Fin n) E →ₗ[E] Matrix (Fin m) (Fin n) E :=
    { toFun := fun y => y * Cm b, map_add' := fun y y' => Matrix.add_mul y y' _, map_smul' := fun c y => Matrix.smul_mul c y _ }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact fun y hy => Cm_inj b hb y hy
  (Equiv.ofBijective L ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).trans
    { toFun := fun X k => bs.repr (X k.1 k.2.1) k.2.2
      invFun := fun c => Matrix.of fun i j => bs.equivFun.symm fun t => c (i, j, t)
      left_inv := fun X => by
        ext i j
        show bs.equivFun.symm (bs.equivFun (X i j)) = X i j
        exact bs.equivFun.symm_apply_apply _
      right_inv := fun c => by
        funext k
        show bs.equivFun (bs.equivFun.symm fun t => c (k.1, k.2.1, t)) k.2.2 = c k
        rw [LinearEquiv.apply_symm_apply] }

theorem xiEquiv_apply {m n : ℕ} {σ : E →ₐ[F] E} {Y : Spc F E n} (bs : Module.Basis (Fin 2) F E)
    (b : GL (Fin n ⊕ Fin n) E) (hb : IsFrame2 σ Y b) (y : Matrix (Fin m) (Fin n) E) (k : Fin m × Fin n × Fin 2) :
    xiEquiv bs b hb y k = bs.repr ((Matrix.fromCols y (-y) * (b⁻¹).1ᵀ).toCols₂ k.1 k.2.1) k.2.2 := by
  rw [toCols₂_anti]; rfl

theorem invOf_two_alg (x : F) : ⅟(2 : AF F) * algebraMap F (AF F) x = algebraMap F (AF F) (2⁻¹ * x) := by
  rw [map_mul]
  congr 1

theorem evaluation_zero_antisymmetric {m n : ℕ} {σ : E →ₐ[F] E} (bs : Module.Basis (Fin 2) F E) (A : Spc F E m) (Y : Spc F E n)
    (b : GL (Fin n ⊕ Fin n) E) (hb : IsFrame2 σ Y b)
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2))
    (hd : IsAdapted bs A Y b dd) (ψ : AddChar (AF F) ℂ) (hψ : ∀ x : F, ψ (algebraMap F (AF F) x) = 1)
    (Φ : (Fin m × Fin n × Fin 2 → AF F) → ℂ) (y : Matrix (Fin m) (Fin n) E) :
    ev0 _ (dd.rho ψ (incM F (Matrix.fromCols y (-y))) Φ) = Φ fun k => algebraMap F (AF F) (xiEquiv bs b hb y k) := by
  obtain ⟨c, hc⟩ := e_rat bs A Y b dd hd (Matrix.fromCols y (-y))
  set a : Fin m × Fin n × Fin 2 → F := xiEquiv bs b hb y
  have ha : (dd.e (incM F (Matrix.fromCols y (-y)))) = (fun k => algebraMap F (AF F) (a k), fun k => algebraMap F (AF F) (c k)) := by
    rw [hc]; congr 1; funext k
    show _ = algebraMap F (AF F) (xiEquiv bs b hb y k)
    rw [xiEquiv_apply]
  have hdot : (fun k => algebraMap F (AF F) (a k)) ⬝ᵥ (fun k => algebraMap F (AF F) (c k)) = algebraMap F (AF F) (a ⬝ᵥ c) := by
    simp [dotProduct, map_sum]
  simp only [ev0, LinearMap.coe_mk, AddHom.coe_mk, Darboux.rho, schr, ha, zero_dotProduct, zero_add, hdot, invOf_two_alg, hψ,
    one_mul]

theorem sEv : SEv := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε dd hd
  refine ⟨adelicCoordinatesEvalZeroForm_mem_admissible _, fun z Φ _ => evaluation_zero_unipotent_kill bs A Y b hb dd hd B.ψ z Φ, fun Φ hΦ => ?_⟩
  have hψ : ∀ x : F, B.ψ (algebraMap F (AF F) x) = 1 := hB.std.2.1
  have hs := (summable_of_mem_schA F hΦ).hasSum
  have h := (Equiv.hasSum_iff (xiEquiv (m := m) bs b hb)).mpr hs
  have e1 : thetaSum F Φ = ∑' ξ : Fin m × Fin n × Fin 2 → F, Φ fun i => algebraMap F (AF F) (ξ i) := rfl
  rw [e1]
  convert h using 1
  funext y
  exact evaluation_zero_antisymmetric bs A Y b hb dd hd B.ψ hψ Φ y

end PositivityTheory.SiegelWeilFormula.Ldexa

end
