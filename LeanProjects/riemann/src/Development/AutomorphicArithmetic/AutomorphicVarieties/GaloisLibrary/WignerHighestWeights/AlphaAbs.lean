import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelML
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelGrp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.TelDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.EpsGrp
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.EpsDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem rp_eq {X M : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (x : Fin n → X),
      rp n b x = (List.ofFn fun i => MulOpposite.op (b i (x i))).prod.unop := by
  intro n
  induction n with
  | zero => intro b x; rw [rp_zero]; simp
  | succ n ih =>
    intro b x
    rw [rp_succ, ih, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    rfl

private noncomputable def sh {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M :=
  A + (c • Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight 1

private theorem sh_apply {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    sh A c x = A x + (c * x.trace) • (1 : Module.End ℂ M) := rfl

private theorem trace_single' {n : ℕ} (i j : Fin n) :
    (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h]

private theorem sh_single {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    sh A c (Matrix.single i j 1) = Formalism.REAL.Tm (fun i j => A (Matrix.single i j 1)) c i j := by
  rw [sh_apply, trace_single', Formalism.REAL.Tm]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private theorem sh_single_op {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    MulOpposite.op (sh (-B) c (Matrix.single i j 1)) =
      Formalism.REAL.Tm (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) c i j := by
  rw [sh_apply, trace_single', Formalism.REAL.Tm]
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private noncomputable def epsL {M : Type} [AddCommGroup M] [Module ℂ M] (n : ℕ) :
    ((Fin n → Matrix (Fin n) (Fin n) ℂ) → M) →ₗ[ℂ] M where
  toFun := eps
  map_add' u v := by simp [eps, Finset.sum_add_distrib]
  map_smul' c u := by simp [eps, Finset.smul_sum, smul_comm c]

private theorem map_eps {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (κ : Module.End ℂ M)
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M) : κ (eps μ) = eps fun x => κ (μ x) := by
  simp only [eps, map_sum, map_zsmul]

theorem UpperTheory.V.AlgRepEndIrreducible.alphaAbs :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (arg : Fin n → ℂ),
      (∀ x y, Commute (A x) (B y)) →
      ∃ α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M,
        (∀ (m : M) (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M), (∀ x, f x = A x m + B x m) →
          α f = Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct (fun i j => A (Matrix.single i j 1)) arg m -
            (Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) arg).unop m) ∧
        (∀ (κ : Module.End ℂ M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 → (∀ x, κ * A x = A (g * x * g') * κ) →
          (∀ x, κ * B x = B (g * x * g') * κ) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
            (∀ x, κ (f x) = f' (g * x * g')) → κ (α f) = α f') ∧
        ∀ (D : Module.End ℂ M) (y : Matrix (Fin n) (Fin n) ℂ), (∀ x, D * A x - A x * D = A (y * x - x * y)) →
          (∀ x, D * B x - B x * D = B (y * x - x * y)) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
            (∀ x, D (f x) = f' x + f (y * x - x * y)) → D (α f) = α f' := by
  intro M _ _ n A B arg hc
  obtain ⟨T, hT⟩ := telML (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
  let α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M :=
    { toFun := fun f => eps (T f)
      map_add' := fun u v => by rw [map_add]; exact (epsL n).map_add _ _
      map_smul' := fun c u => by rw [map_smul]; exact (epsL n).map_smul _ _ }
  have hα : ∀ f, α f = eps (T f) := fun _ => rfl
  refine ⟨α, fun m f hf => ?_, fun κ g g' hg hA hB f f' hf => ?_, fun D y hA hB f f' hf => ?_⟩
  · have h := telSum (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
      (fun i j x y => by
        rw [sh_apply, sh_apply]
        exact ((hc x y).neg_right.add_right ((Commute.one_right _).smul_right _)).add_left
          ((Commute.one_left _).smul_left _)) m f
      (fun i x => by rw [hf, sh_apply, sh_apply]; simp)
    rw [hα]
    unfold eps Formalism.HermitianLatticeCounting.P.doublyAntisymmetrizedProduct Formalism.HermitianLatticeCounting.P.orderedTermProduct
    simp only [hT, h, rp_eq, units, sh_single_op]
    simp only [sh_single, ← zsmul_eq_mul, smul_smul, Finset.unop_sum,
      MulOpposite.unop_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (g * x * g').trace = x.trace := fun x => by
      rw [Matrix.trace_mul_cycle, hg, one_mul]
    have h := telGrp (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) κ
      (fun x => g * x * g')
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, hA]; simp)
      (fun i x => by
        rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, mul_neg, hB]
        simp) f f' hf
    rw [hα, hα, map_eps, ← epsGrp M n (T f') g g' hg]
    simp only [hT, h]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (y * x - x * y).trace = 0 := fun x => by
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    have h := telDer (Matrix (Fin n) (Fin n) ℂ) M n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) D
      (fun x => y * x - x * y)
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, ← hA]; simp)
      (fun i x => by
        rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, ← hB]
        simp
        abel) f f' hf
    have e : (fun x => D (T f x)) =
        ⇑(T f') + fun x => ∑ k, T f (Function.update x k (y * x k - x k * y)) := by
      funext x
      simp only [hT, h, Pi.add_apply]
    rw [hα, hα, map_eps, e]
    refine ((epsL n).map_add _ _).trans ?_
    exact (congrArg (eps (T f') + ·) (epsDer M n (T f) y)).trans (add_zero _)
