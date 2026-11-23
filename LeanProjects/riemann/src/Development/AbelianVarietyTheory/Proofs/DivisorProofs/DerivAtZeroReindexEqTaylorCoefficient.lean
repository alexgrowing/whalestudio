import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.WordDerivativeBlocks
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.DerivReindex

open GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials

theorem wordDeriv_eq {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (dir : Λ → W) (l : List Λ)
    (F : W → ℂ) (p : W) {n : ℕ} (h : l.length = n) :
    iteratedFDeriv ℂ n F p (fun i => dir (l.get ⟨i, by rw [h]; exact i.2⟩)) = wordDeriv dir l F p := by
  subst h; rfl

theorem wordDeriv_comp {Λ Λ' W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] (dir : Λ → W) (dir' : Λ' → W') (g : Λ → Λ')
    (T : W →L[ℂ] W') (hT : ∀ x, T (dir x) = dir' (g x)) (l : List Λ) (F : W' → ℂ)
    (hF : ContDiff ℂ l.length F) :
    wordDeriv dir l (F ∘ T) 0 = wordDeriv dir' (l.map g) F 0 := by
  rw [← wordDeriv_eq dir' (l.map g) F 0 (n := l.length) (by simp), wordDeriv,
    T.iteratedFDeriv_comp_right hF 0 le_rfl, map_zero,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  simp [hT]

theorem derivAt0_reindex : ∀ (D : D7) (ι : Type) [Fintype ι] (e : ι ≃ D.what₂.Tau) (a b : ℕ) (F : TaylorLogMetric.VC D a b → ℂ), Differentiable ℂ F → ∀ m : DVar ι a b →₀ ℕ, derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D F (Finsupp.equivMapDomain (e.prodCongr (Equiv.refl (Fin b × Fin a))) m) := by
  intro D ι _ e a b F hF m
  have han : AnalyticOnNhd ℂ F Set.univ := GlobalTheory.SCV.analyticOnNhd_of_differentiable hF _
  set g := e.prodCongr (Equiv.refl (Fin b × Fin a)) with hg
  let T : VCx ι a b →L[ℂ] TaylorLogMetric.VC D a b :=
    ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hT : ∀ x, T (coordX x) = TaylorLogMetric.coordV D (g x) := by
    intro x
    funext τ i j
    change coordX x (e.symm τ) i j = _
    unfold coordX TaylorLogMetric.coordV
    exact @if_congr _ _ _ (_) (_) _ _ _ _ (and_congr_left' e.symm_apply_eq) rfl rfl
  have hne : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h1 : derivAt0 (fun z : VCx ι a b => F fun τ => z (e.symm τ)) m
      = wordDeriv coordX m.toMultiset.toList (F ∘ T) 0 :=
    wordDeriv_eq coordX m.toMultiset.toList (F ∘ T) 0 (Multiset.length_toList _)
  have h2 : TaylorLogMetric.taylor D F (Finsupp.equivMapDomain g m)
      = wordDeriv (TaylorLogMetric.coordV D) (Finsupp.equivMapDomain g m).toMultiset.toList F 0 /
        (m.prod fun _ n => (n.factorial : ℂ)) := by
    rw [TaylorLogMetric.taylor, Finsupp.prod_equivMapDomain]
    congr 1
    exact wordDeriv_eq _ _ F 0 (Multiset.length_toList _)
  rw [h1, h2, mul_div_cancel₀ _ hne, wordDeriv_comp coordX (TaylorLogMetric.coordV D) g T hT _ F han.contDiff]
  refine wordDeriv_perm _ (han 0 trivial) ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map, Finsupp.equivMapDomain_eq_mapDomain]

end GlobalTheory.DerivReindex
