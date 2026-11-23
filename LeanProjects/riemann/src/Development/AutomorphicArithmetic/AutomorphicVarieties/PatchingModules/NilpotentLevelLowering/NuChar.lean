import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqRec
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
private theorem roots_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) (hu : u ≠ 0) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  refine Polynomial.funext fun x => ?_
  have h1 := congrArg (eval (x / u)) hM
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
  have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
      field_simp
    · simp [Matrix.diagonal_apply_ne _ hab]
  rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
    Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
  simp
  field_simp

open Polynomial in
private theorem charpoly_smul_prod {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype ι]
    (f : Module.End ℂ V) (u : ℂ) (hu : u ≠ 0) (c : ι → ℂ) (h : f.charpoly = ∏ i, (X - C (c i))) :
    (u • f).charpoly = ∏ i, (X - C (c i * u)) := by
  have hr : f.charpoly.roots = Finset.univ.val.map c := by
    rw [h, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V), map_smul, roots_smul_matrix _ _ hu,
    LinearMap.charpoly_toMatrix, hr, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

private theorem absPow_neg_nat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i : ℕ) (x : kˣ) : (absPow k (-(i : ℂ)) x : ℂ) = (resCard k : ℂ) ^ ((i : ℤ) * ord k x) := by
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
  congr 1
  ring

theorem UpperTheory.V.Pa.Lev.nuChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin hB a) (ε : EpsFamily Bq) (rc : IrrGL (w.adicCompletion E) → WD hB), Laws a ha ε rc → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (χ : (Fin n → (w.adicCompletion E)ˣ) →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → torusChar ψ = χ * ((deltaHalf (w.adicCompletion E) fun _ : Fin n => Unit).comp (leviTorus (w.adicCompletion E) (Fin n)).toMonoidHom) → IsSubquotient σ.ρ (prinSeries ψ) → ∀ g : Weil hB, (rc (algNorm σ)).charPol g = ∏ i : Fin n, (Polynomial.X - Polynomial.C ((resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) * (χ (Pi.mulSingle i (a g)) : ℂ))) := by
  intro l _ E Ω _ _ _ _ _ Bq w hB _ a ha ε rc L n σ ψ χ hψ hχ hs g
  have H := UpperTheory.V.AlgebraTools.jqRec E Ω Bq w hB a ha ε rc L n ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  rw [algNorm, IrrGL.nu, L.tw_eq]
  change (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g = _ at H
  generalize rc (IrrGL.of σ.ρ σ.smooth σ.irred) = x at H ⊢
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.charPol_mk] at H
  rw [WD.lpTwist_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_prod _ _ (Units.ne_zero _) _ H]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have h1 : torusChar ψ (Pi.mulSingle i (a g)) = ψ i (a g) := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → (w.adicCompletion E)ˣ) j,
      Matrix.GeneralLinearGroup.det (leviTorus (w.adicCompletion E) (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv t)
  have h2 : deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
      (leviTorus (w.adicCompletion E) (Fin n) (Pi.mulSingle i (a g))) =
      absPow (w.adicCompletion E) ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (a g) := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  rw [← h1, hχ, ← absPow_neg_nat]
  have h3 : -((i : ℕ) : ℂ) = (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  rw [h3, absPow_add]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  erw [h2]
  ring
