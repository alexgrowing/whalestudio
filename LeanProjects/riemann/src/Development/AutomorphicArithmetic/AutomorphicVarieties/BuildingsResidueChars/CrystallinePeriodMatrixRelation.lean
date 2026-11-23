import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineVectorBasisExpansion
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

private theorem specRoot_semi {R K U : Type} [Field R] [Field K] [Algebra R K] [AddCommGroup U] [Module R U]
    {d : ℕ} (Φ : (Fin d → K) → U) (hadd : ∀ a b, Φ (a + b) = Φ a + Φ b)
    (hsm : ∀ (r : R) a, Φ (r • a) = r • Φ a) (T : Module.End R U) (F : Matrix (Fin d) (Fin d) K)
    (h : ∀ c, T (Φ c) = Φ (F.mulVec c)) (q : R[X]) (c : Fin d → K) :
    aeval T q (Φ c) = Φ ((aeval F q).mulVec c) := by
  have hp : ∀ (n : ℕ) (c : Fin d → K), (T ^ n) (Φ c) = Φ ((F ^ n).mulVec c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ', Module.End.mul_apply, ih, h, Matrix.mulVec_mulVec, pow_succ']
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, LinearMap.add_apply, hp, hq, Matrix.add_mulVec, hadd]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def, LinearMap.smul_apply, hp,
      Matrix.smul_mulVec, hsm]

private theorem specRoot_spec {R K L : Type} [Field R] [Field K] [Field L] [Algebra R K] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsAlgClosed L] {d : ℕ} (F : Matrix (Fin d) (Fin d) K) (q : R[X])
    (hq : q ≠ 0) (c : Fin d → K) (hc : c ≠ 0) (h : (aeval F q).mulVec c = 0) :
    ∃ β ∈ spectrum L (F.map (algebraMap K L)), aeval β q = 0 := by
  have h1 : (aeval F q).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h⟩
  have h2 : (algebraMap K L).mapMatrix (aeval F q) =
      aeval (F.map (algebraMap K L)) (q.map (algebraMap R L)) := by
    refine Polynomial.map_aeval_eq_aeval_map (φ := algebraMap R L)
      (ψ := (algebraMap K L).mapMatrix) ?_ q F
    ext r i j
    simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.algebraMap_matrix_apply]
    split_ifs
    · simp [← IsScalarTower.algebraMap_apply]
    · simp
  have h3 : ¬ IsUnit (aeval (F.map (algebraMap K L)) (q.map (algebraMap R L))) := by
    rw [← h2, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, h1, map_zero]
    exact not_isUnit_zero
  have hq' : q.map (algebraMap R L) ≠ 0 := Polynomial.map_ne_zero hq
  have hs := (IsAlgClosed.splits (q.map (algebraMap R L))).eq_prod_roots
  obtain ⟨β, hβ, e⟩ := spectrum.exists_mem_of_not_isUnit_aeval_prod (p := q.map (algebraMap R L))
    (a := F.map (algebraMap K L)) (fun hu => h3 (by
      rw [hs, map_mul, aeval_C]
      exact ((IsUnit.mk0 _ (leadingCoeff_ne_zero.2 hq')).map _).mul hu))
  exact ⟨β, hβ, by rwa [eval_map_algebraMap] at e⟩

theorem UpperTheory.crystalline_period_matrix_relation :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ F : Matrix (Fin d) (Fin d) ↥(K0 K), M.map (((PP l).φB)^[f]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ x ∈ Dcris ((PP l).PD K) ρ, x ≠ 0 → ∀ q : ℚ_[l][X], q ≠ 0 → aeval ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) q x = 0 → ∃ β ∈ spectrum (Om l) (F.map (algebraMap ↥(K0 K) (Om l))), aeval β q = 0 := by
  intro l _ K f hσ V _ _ _ ρ d e M M' hMM hρ F hF x hx hx0 q hq h0
  obtain ⟨c, hc⟩ := UpperTheory.crystalline_vector_basis_expansion K ρ e M M' hMM hρ x hx
  have hMM' : M' * M = 1 := mul_eq_one_comm.1 hMM
  let j := algebraMap ↥(K0 K) (Bcr l)
  let Φ : (Fin d → ↥(K0 K)) → V ⊗[ℚ_[l]] Bcr l := fun c =>
    ∑ i, e i ⊗ₜ[ℚ_[l]] (M.mulVec (fun k => j (c k)) i)
  have hfix : ∀ (k : ℕ) (c : ↥(K0 K)), ((PP l).φB)^[k] (j c) = j ((((PP l).PD K).σ)^[k] c) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih =>
      intro c
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]
  have hT : ∀ (k : ℕ) (v : V) (b : Bcr l),
      ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ k) (v ⊗ₜ[ℚ_[l]] b) =
        v ⊗ₜ[ℚ_[l]] (((PP l).φB)^[k] b) := by
    intro k
    induction k with
    | zero => intro v b; rfl
    | succ k ih =>
      intro v b
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply', ← (PP l).PD_φ K]
      rfl
  let ψ : Bcr l →+* Bcr l := (((PP l).φB ^ f : Bcr l →ₐ[ℚ_[l]] Bcr l) : Bcr l →+* Bcr l)
  have hψ : (ψ : Bcr l → Bcr l) = ((PP l).φB)^[f] := AlgHom.coe_pow _ _
  have key := specRoot_semi Φ (fun a b => by
      simp only [Φ, Pi.add_apply, map_add, ← Finset.sum_add_distrib, ← TensorProduct.tmul_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib])
    (fun (r : ℚ_[l]) a => by
      simp only [Φ, Finset.smul_sum, ← TensorProduct.tmul_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Pi.smul_apply, Algebra.smul_def, map_mul, j,
        ← IsScalarTower.algebraMap_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    ((φVB ((PP l).PD K) (LL := ℚ_[l]) (V := V) : Module.End ℚ_[l] (V ⊗[ℚ_[l]] Bcr l)) ^ f) F
    (fun c => by
      simp only [Φ, map_sum, hT]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [← hψ, RingHom.map_mulVec, hψ, hF, ← Matrix.mulVec_mulVec]
      have e1 : ((PP l).φB)^[f] ∘ (fun k => j (c k)) = j ∘ c := by
        funext m
        exact (hfix f _).trans (congrArg j (hσ _))
      have e2 : (F.map j).mulVec (j ∘ c) = fun k => j (F.mulVec c k) := by
        funext k
        exact (RingHom.map_mulVec j F c k).symm
      rw [e1, e2]) q c
  have hxc : x = Φ c := hc
  rw [← hxc, h0] at key
  refine specRoot_spec F q hq c ?_ ?_
  · rintro rfl
    apply hx0
    rw [hc]
    simp [Matrix.mulVec, dotProduct]
  · set y := (aeval F q).mulVec c
    have h1 := TensorProduct.sum_tmul_basis_left_eq_zero e
      (Finsupp.equivFunOnFinite.symm (M.mulVec (fun k => j (y k)))) (by
        rw [Finsupp.sum_fintype _ _ (fun i => TensorProduct.tmul_zero _ _)]
        exact key.symm)
    have h2 : M.mulVec (fun k => j (y k)) = 0 := by
      funext i
      exact DFunLike.congr_fun h1 i
    have h3 := congrArg M'.mulVec h2
    rw [Matrix.mulVec_mulVec, hMM', Matrix.one_mulVec, Matrix.mulVec_zero] at h3
    haveI : Nontrivial (Bcr l) := ⟨⟨1, 0, fun h => ((PP l).PD K).not_mem_filtration_two (by
      rw [← mul_one ((PP l).PD K).t, h, mul_zero, map_zero]; exact Submodule.zero_mem _)⟩⟩
    funext k
    exact j.injective ((congrFun h3 k).trans (map_zero j).symm)
