import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationIntegralLattice
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineFrobeniusAlgebraicElements
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem key {Q V B B' : Type} [Field Q] [AddCommGroup V] [Module Q V] [CommRing B] [Algebra Q B]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (T : V →ₗ[Q] V) (c : B →ₗ[Q] B')
    (w w' : Fin n → B) (h : ∀ i, ∑ j, algebraMap Q B (e.repr (T (e j)) i) * w' j = w i) :
    ∑ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (w i) := by
  have h1 : ∀ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (algebraMap Q B (e.repr (T (e j)) i) * w' j) := by
    intro j
    conv_lhs => rw [← e.sum_repr (T (e j))]
    rw [sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul, ← Algebra.smul_def, map_smul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tmul_sum, ← map_sum, h]

private theorem eq_zero {Q V B' : Type} [Field Q] [AddCommGroup V] [Module Q V]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (w : Fin n → B')
    (h : ∑ i, e i ⊗ₜ[Q] w i = 0) (k : Fin n) : w k = 0 := by
  have := congrArg (fun x => TensorProduct.lid Q B' (LinearMap.rTensor B' (e.coord k) x)) h
  simpa [map_sum, Finsupp.single_apply, ite_smul] using this

private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (k : ℕ) (v : LL) (b : P.R.B) :
    (phiV P LL LL ^ k) (v ⊗ₜ C b) = v ⊗ₜ C ((P.φB ^ k) b) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, AlgHom.mul_apply]

theorem UpperTheory.weilDeligne_unramified_period :
    UpperTheory.V.Af.Wd.UnrPer := by
  intro l _ K L η hη hI
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  have hη' : Continuous fun g => (η g : ↥L.1) := continuous_induced_rng.2 hη
  obtain ⟨n, e, M, hMc, hM⟩ := UpperTheory.galois_representation_integral_lattice l ↥(GK K) ↥L.1 (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η))
    (fun x => hη'.mul continuous_const)
  obtain ⟨W, hW, hWg, hWφ⟩ := UpperTheory.crystalline_frobenius_algebraic_elements l K n M hMc (fun g hg => by
    rw [← map_one M]
    ext i j
    apply PadicInt.ext
    rw [hM, hM, map_one]
    congr 2
    change (η g : ↥L.1) * e j = e j
    rw [hI g hg, Units.val_one, one_mul])
  haveI := nontrivial_B (V.Loc.PP l)
  haveI : Nonempty (Fin n) := e.index_nonempty
  let j₀ : Fin n := Classical.arbitrary _
  let c : V.Loc.Bcr l →ₗ[ℚ_[l]] Bst (V.Loc.PP l) := (CAlgHom : V.Loc.Bcr l →ₐ[ℚ_[l]] Bst (V.Loc.PP l)).toLinearMap
  have hk : ∀ (g : ↥(GK K)) (f : V.Loc.Bcr l → V.Loc.Bcr l),
      (M g).map (fun z => algebraMap ℚ_[l] (V.Loc.Bcr l) (z : ℚ_[l])) * W.map f = W →
      ∑ j, ((η g : ↥L.1) * e j) ⊗ₜ[ℚ_[l]] (C (f (W j j₀)) : Bst (V.Loc.PP l)) = ∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀) := by
    intro g f h
    refine key e (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η) g) c (fun i => W i j₀) (fun i => f (W i j₀)) fun i => ?_
    have := congrFun (congrFun h i) j₀
    simpa only [Matrix.mul_apply, Matrix.map_apply, hM] using this
  refine ⟨∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀), fun h0 => ?_, fun g => ?_, fun g k hg => ?_⟩
  · refine hW.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_)
    exact C_eq_zero.1 (eq_zero e (fun i => (C (W i j₀) : Bst (V.Loc.PP l))) h0 i)
  · rw [map_sum]
    simp only [stRep_tmul, actSt_C]
    exact hk g _ (hWg g)
  · rw [map_sum, Finset.smul_sum]
    simp only [phiV_pow, smul_tmul']
    exact hk g _ (hWφ g k hg)
