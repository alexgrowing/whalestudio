import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} (X : Lie E a) (φ : Sm E a)
    (h : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.1 γ), fun u hu => ?_, fun m hm => ?_⟩
  · exact (LinearMap.congr_fun (lie_rt_fin X u) φ).symm.trans (congrArg (lie E a X) (h.2.1 u hu))
  · rw [lie_one_comm, h.2.2 m hm, map_smul]

private theorem adj_span (Ξ : AlgRep E a) (r : ℝ) (P : Sm E a → Prop) (hP : ∀ X φ, P φ → P (lie E a X φ)) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}) :
    smAdj Ξ r X m ∈ Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    rw [smAdj, adj_apply, smA_apply, smB_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩)
      (Submodule.subset_span ⟨_, _, hP X φ hφ, rfl⟩))
      (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private theorem k_adj (Ξ : AlgRep E a) (r : ℝ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    smK Ξ k * smAdj Ξ r (toL X) = smAdj Ξ r (toL (k.1 * X * star k.1)) * smK Ξ k := by
  obtain ⟨-, -, -, hA, hB, -⟩ := smAB E a Ξ
  refine LinearMap.ext fun m => ?_
  have h1 := LinearMap.congr_fun (hA k X) m
  have h2 := LinearMap.congr_fun (hB k X) m
  simp only [Module.End.mul_apply] at h1 h2 ⊢
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, (ellFacts E a).2.2.1 k X, LinearMap.map_smul_of_tower]

end

theorem UpperTheory.V.Cj.H.delLev :
    UpperTheory.V.Cj.H.DelLev := by
  intro E _ _ _ a n e he U Ξ r q ω
  refine ⟨fun h => ⟨delCochain E a n e he _ _ _ (fun k X => k_adj Ξ r k X.1) q ω h.equiv, fun X i hi => ?_, fun X => ?_⟩,
    fun h X => ?_⟩
  · rw [del_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.basic (Matrix.vecCons (e j) X) i.succ hi, map_zero]
  · rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ level_lie _ _ (h.val _)
  · refine mem_tens.1 (span_le_tens (P := fun φ => φ ∈ sqSub E a r) (fun _ h => h) ?_)
    rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ ((sqLie E a r).2) _ _ (mem_span_of_cmp (h _))
