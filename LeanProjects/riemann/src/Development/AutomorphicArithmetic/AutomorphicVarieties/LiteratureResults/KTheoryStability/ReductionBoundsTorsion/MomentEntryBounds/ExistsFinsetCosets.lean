import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
import GroundTheory.AutomorphicForms.ReductionSiegel
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits
import GroundTheory.AutomorphicForms.ReductionLocalVolume
import GroundTheory.GlobalFields.Adele.Discrete

noncomputable section

set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL GroundTheory.Automorphic
open scoped NumberField.AdeleRing

namespace PositivityTheory.KB.MomentRationality.RedGL

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem exists_bound_omega {ω : Set (AdelicGLn.AdelicGL L N)} (hω : IsCompact ω) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ ∀ b ∈ ω, ∀ (w : InfinitePlace L) (i j : Fin N),
      ‖((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖ ≤ M0 ∧
        ‖((Reduction.infAt w b⁻¹ : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖ ≤ M0 := by
  classical
  let e : InfinitePlace L → Fin N → Fin N → AdelicGLn.AdelicGL L N → ℝ := fun w i j b =>
    ‖((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) i j‖
  have hc : ∀ w i j, Continuous (e w i j) := by
    intro w i j
    have h1 : Continuous (Reduction.infAt (K := L) (n := N) w) := by
      unfold Reduction.infAt
      exact (continuous_apply w).comp
        (continuous_fst.comp (AdelicGLn.restrictedProductEquiv L N).continuous)
    have h2 : Continuous fun b : AdelicGLn.AdelicGL L N =>
        ((Reduction.infAt w b : GL (Fin N) w.Completion) : Matrix (Fin N) (Fin N) w.Completion) :=
      (Units.continuous_val (M := Matrix (Fin N) (Fin N) w.Completion)).comp h1
    exact continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp h2))
  let F : AdelicGLn.AdelicGL L N → ℝ := fun b => ∑ w, ∑ i, ∑ j, (e w i j b + e w i j b⁻¹)
  have hF : Continuous F := by
    refine continuous_finset_sum _ fun w _ => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => ?_
    exact (hc w i j).add ((hc w i j).comp continuous_inv)
  obtain ⟨M, hM⟩ := (hω.image hF).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun b hb w i j => ?_⟩
  have hFb : F b ≤ max M 0 := (hM ⟨b, hb, rfl⟩).trans (le_max_left _ _)
  have hnn : ∀ w i j, 0 ≤ e w i j b + e w i j b⁻¹ := fun w i j =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hterm : e w i j b + e w i j b⁻¹ ≤ F b := by
    calc e w i j b + e w i j b⁻¹ ≤ ∑ j', (e w i j' b + e w i j' b⁻¹) :=
          Finset.single_le_sum (f := fun j' => e w i j' b + e w i j' b⁻¹)
            (fun j' _ => hnn w i j') (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (e w i' j' b + e w i' j' b⁻¹) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (e w i' j' b + e w i' j' b⁻¹))
            (fun i' _ => Finset.sum_nonneg fun j' _ => hnn w i' j') (Finset.mem_univ i)
      _ ≤ F b :=
          Finset.single_le_sum (f := fun w' => ∑ i', ∑ j', (e w' i' j' b + e w' i' j' b⁻¹))
            (fun w' _ => Finset.sum_nonneg fun i' _ => Finset.sum_nonneg fun j' _ => hnn w' i' j')
            (Finset.mem_univ w)
  refine ⟨?_, ?_⟩
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hterm.trans hFb)
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans (hterm.trans hFb)

theorem exists_gm_of_fin (γ : GL (Fin N) L)
    (h : (AdelicGLn.prodEquiv L N (AdelicGLn.diagonal L N γ)).2 ∈ AdelicGLn.integralFiniteGL L N) :
    ∃ δ : Gm L N, toK L N δ = γ := by
  have hint : ∀ x : L, algebraMap L (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) x ∈
      GroundTheory.Global.integralFiniteAdeles (𝓞 L) L → x ∈ (algebraMap (𝓞 L) L).range := by
    intro x hx
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro v
    have h := hx v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    rwa [show (algebraMap L (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L) x) v =
        (x : v.adicCompletion L) from rfl,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := (Submonoid.mem_units_iff _ _).1 h
  have h1 : ∀ i j, (γ : Matrix (Fin N) (Fin N) L) i j ∈ (algebraMap (𝓞 L) L).range := by
    intro i j
    apply hint
    have := congrFun (congrFun hP i) j
    rw [show algebraMap L (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)
        ((γ : Matrix (Fin N) (Fin N) L) i j) =
        ((AdelicGLn.prodEquiv L N (AdelicGLn.diagonal L N γ)).2 :
          Matrix (Fin N) (Fin N) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) i j from rfl, ← this]
    exact (P i j).2
  have h2 : ∀ i j, ((γ⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) i j ∈
      (algebraMap (𝓞 L) L).range := by
    intro i j
    apply hint
    have := congrFun (congrFun hQ i) j
    rw [show algebraMap L (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)
        (((γ⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) i j) =
        ((AdelicGLn.prodEquiv L N (AdelicGLn.diagonal L N γ⁻¹)).2 :
          Matrix (Fin N) (Fin N) (IsDedekindDomain.FiniteAdeleRing (𝓞 L) L)) i j from rfl,
      map_inv, map_inv, Prod.snd_inv, ← this]
    exact (Q i j).2
  choose A hA using h1
  choose B hB using h2
  have hinj : Function.Injective (algebraMap (𝓞 L) L) := FaithfulSMul.algebraMap_injective _ _
  have hAm : (Matrix.of A).map (algebraMap (𝓞 L) L) = (γ : Matrix (Fin N) (Fin N) L) := by
    ext i j
    exact hA i j
  have hBm : (Matrix.of B).map (algebraMap (𝓞 L) L) =
      ((γ⁻¹ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) := by
    ext i j
    exact hB i j
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, hAm, hBm, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBA : Matrix.of B * Matrix.of A = 1 := by
    apply Matrix.map_injective hinj
    dsimp only
    rw [Matrix.map_mul, hAm, hBm, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨Matrix.of A, Matrix.of B, hAB, hBA⟩, ?_⟩
  ext i j
  exact hA i j

theorem exists_finset_cosets {C : Set (AdelicGLn.FiniteAdelicGL L N)} (hC : IsCompact C) :
    ∃ R : Finset (GL (Fin N) L), ∀ γ : GL (Fin N) L,
      (AdelicGLn.prodEquiv L N (AdelicGLn.diagonal L N γ)).2 ∈ C →
        ∃ g ∈ R, ∃ δ : Gm L N, toK L N δ = g⁻¹ * γ := by
  classical
  set U := AdelicGLn.integralFiniteGL L N with hU
  let p : GL (Fin N) L → AdelicGLn.FiniteAdelicGL L N := fun γ =>
    (AdelicGLn.prodEquiv L N (AdelicGLn.diagonal L N γ)).2
  have hp : ∀ a b : GL (Fin N) L, p (a⁻¹ * b) = (p a)⁻¹ * p b := by
    intro a b
    simp only [p, map_mul, map_inv, Prod.snd_mul, Prod.snd_inv]
  let V : C → Set (AdelicGLn.FiniteAdelicGL L N) := fun c => {x | (c : AdelicGLn.FiniteAdelicGL L N)⁻¹ * x ∈ U}
  have hV : ∀ c, IsOpen (V c) := fun c =>
    (AdelicGLn.isOpen_integralFiniteGL L N).preimage (continuous_const.mul continuous_id)
  have hcov : C ⊆ ⋃ c, V c := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    show x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hV hcov
  let g : C → GL (Fin N) L := fun c =>
    if h : ∃ γ : GL (Fin N) L, p γ ∈ C ∧ p γ ∈ V c then h.choose else 1
  refine ⟨t.image g, fun γ hγ => ?_⟩
  obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hγ)
  have hex : ∃ γ : GL (Fin N) L, p γ ∈ C ∧ p γ ∈ V c := ⟨γ, hγ, hc⟩
  have hg : g c = hex.choose := dif_pos hex
  have hgV : p (g c) ∈ V c := by
    rw [hg]
    exact hex.choose_spec.2
  refine ⟨g c, Finset.mem_image_of_mem g hct, ?_⟩
  apply exists_gm_of_fin
  show p ((g c)⁻¹ * γ) ∈ U
  rw [hp]
  have h1 : ((c : AdelicGLn.FiniteAdelicGL L N)⁻¹ * p (g c))⁻¹ *
      ((c : AdelicGLn.FiniteAdelicGL L N)⁻¹ * p γ) ∈ U :=
    U.mul_mem (U.inv_mem hgV) hc
  simpa [mul_assoc] using h1

end PositivityTheory.KB.MomentRationality.RedGL

end
