import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc

noncomputable section

open NumberField GlobalTheory.CuspRep PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness

private theorem exists_detect {U : Type} (C : Submodule ℂ (U → ℂ)) [FiniteDimensional ℂ C] :
    ∃ s : Finset U, ∀ f ∈ C, (∀ a ∈ s, f a = 0) → f = 0 := by
  let ev : U → Module.Dual ℂ C := fun a => (LinearMap.proj a).comp C.subtype
  have hfg : (Submodule.span ℂ (ev '' Set.univ)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s, -, rfl⟩ := Finset.subset_set_image_iff.1 ht
  refine ⟨s, fun f hf h0 => funext fun a => ?_⟩
  have hle : Submodule.span ℂ (ev '' Set.univ) ≤ LinearMap.ker (Module.Dual.eval ℂ C ⟨f, hf⟩) := by
    rw [e, Submodule.span_le]
    intro l hl
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hl)
    exact h0 b hb
  exact hle (Submodule.subset_span ⟨a, trivial, rfl⟩)

private theorem eq_zero_of_grid {ι U : Type} [Fintype ι] (C : ι → Submodule ℂ (U → ℂ)) (s : ι → Finset U)
    (hs : ∀ i, ∀ f ∈ C i, (∀ a ∈ s i, f a = 0) → f = 0) (F : (ι → U) → ℂ)
    (hF : ∀ i k, (fun a => F (Function.update k i a)) ∈ C i) (h0 : ∀ k, (∀ i, k i ∈ s i) → F k = 0) (k : ι → U) :
    F k = 0 := by
  have key : ∀ (T : Finset ι) (k : ι → U), (∀ i, i ∉ T → k i ∈ s i) → F k = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun k hk => h0 k fun i => hk i (Finset.notMem_empty i)
    | insert i T _ ih =>
      intro k hk
      have h := hs i _ (hF i k) fun a ha => ih _ fun j hj => by
        by_cases e : j = i
        · subst e
          simpa using ha
        · rw [Function.update_of_ne e]
          exact hk j (by simp [e, hj])
      simpa using congrFun h (k i)
  exact key Finset.univ k fun i hi => absurd (Finset.mem_univ i) hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def glue (k : InfinitePlace E → Un n) : Kinf E n :=
  ⟨Matrix.of fun i j v => (k v).1 i j, Matrix.mem_unitaryGroup_iff'.2 <| by
    ext i j v
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 (k v).2) i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.star_apply, h]
    split_ifs <;> rfl⟩

private theorem glue_mul (k k' : InfinitePlace E → Un n) : glue (k * k') = glue k * glue k' := by
  apply Subtype.ext
  ext i j v
  show ((k v).1 * (k' v).1) i j = ((glue k).1 * (glue k').1) i j v
  simp only [glue, Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply]

private theorem glue_surj (x : Kinf E n) : ∃ k, glue k = x := by
  refine ⟨fun v => ⟨Matrix.of fun i j => x.1 i j v, Matrix.mem_unitaryGroup_iff'.2 ?_⟩, rfl⟩
  ext i j
  have h := congrFun (congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 x.2) i) j) v
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Finset.sum_apply, Pi.mul_apply, Pi.star_apply] at h
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, Matrix.of_apply, h]
  split_ifs <;> rfl

private theorem along_glue (w : InfinitePlace E) (a : Un n) (φ : GA E n → ℂ) (g : GA E n) :
    along w g φ a.1 = φ (g * infGL E n (Unitary.toUnits (glue (Function.update 1 w a)))) := by
  rw [← chart_val φ g]
  show chart φ g _ = chart φ g _
  congr 1
  funext i j v
  show atW w a.1 i j v = ((Function.update (1 : InfinitePlace E → Un n) w a) v).1 i j
  by_cases e : v = w
  · subst e
    simp [atW]
  · simp [atW, e]

private def box (C : InfinitePlace E → Submodule ℂ (Un n → ℂ)) : Submodule ℂ (Kinf E n → ℂ) where
  carrier := {f | ∀ w x, (fun a => f (x * glue (Function.update 1 w a))) ∈ C w}
  add_mem' hf hg w x := (C w).add_mem (hf w x) (hg w x)
  zero_mem' w _ := (C w).zero_mem
  smul_mem' c _ hf w x := (C w).smul_mem c (hf w x)

private theorem box_fin (C : InfinitePlace E → Submodule ℂ (Un n → ℂ)) [∀ w, FiniteDimensional ℂ (C w)] :
    FiniteDimensional ℂ (box C) := by
  choose s hs using fun w => exists_detect (C w)
  let L : box C →ₗ[ℂ] ((∀ w, s w) → ℂ) := (LinearMap.funLeft ℂ ℂ fun k => glue fun w => (k w).1).comp (box C).subtype
  refine FiniteDimensional.of_injective L ((injective_iff_map_eq_zero L).2 fun f hf => Subtype.ext (funext fun x => ?_))
  obtain ⟨k, rfl⟩ := glue_surj x
  refine eq_zero_of_grid C s hs (fun k => f.1 (glue k)) (fun w k => ?_) (fun k hk => congrFun hf fun w => ⟨k w, hk w⟩) k
  convert f.2 w (glue (Function.update k w 1)) using 3 with a
  rw [← glue_mul]
  congr 1
  funext v
  by_cases e : v = w
  · subst e
    simp
  · simp [e]

private def coef (M : KMod n) : Module.Dual ℂ (M.V →L[ℂ] M.V) →ₗ[ℂ] (Un n → ℂ) where
  toFun l a := l (M.ρ a⁻¹)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem iso_coef {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (σ : Un n →* (V →ₗ[ℂ] V)) (M : KMod n)
    (l : V →ₗ[ℂ] ℂ) {u : V} (hu : u ∈ isoSp σ M) : (fun a => l (σ a u)) ∈ LinearMap.range (coef M) := by
  let L : V →ₗ[ℂ] (Un n → ℂ) := LinearMap.pi fun a => l.comp (σ a)
  have hle : isoSp σ M ≤ (LinearMap.range (coef M)).comap L := by
    refine iSup_le fun t => ?_
    rintro _ ⟨ξ, rfl⟩
    refine ⟨l.comp (t.1.comp (ContinuousLinearMap.compL ℂ M.V M.V ℂ ξ).toLinearMap), funext fun a => ?_⟩
    exact congrArg l (t.2 a ξ)
  exact hle hu

private theorem cap_scalar (π : CuspSub E n) (τ : E →+* ℂ) (z : ℂ) : ∃ c : ℂ, ∀ φ ∈ π.V, cap τ z φ = c • φ := by
  refine π.exists_scalar (Algebra.subset_adjoin ⟨τ, z, rfl⟩) ?_
  rintro (k | k | X)
  exacts [commute_cap_finRep τ z k, GlobalTheory.CapAdInv.cap_commute_rt_infGL E n τ z _, commute_cap_lie τ z X]

end UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.GSp4Splitting.RealLieFiniteness PositivityTheory.Rg.BcB.E.E3.fintype in
theorem UpperTheory.V.Z.GSp4Splitting.rlFin :
    RlFin := by
  intro E _ _ _ n _ π _ K hK _ _ _ _ μf _ D M
  choose c hc using cap_scalar π
  let W := box fun w => LinearMap.range (coef (M w))
  haveI : FiniteDimensional ℂ W := box_fin _
  haveI := wl_fin W
  haveI := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n K hK _ (sig W) (sig_cont W) c
  let j : D.U →ₗ[ℂ] Sm E n := π.V.subtype ∘ₗ D.i
  have hj : Function.Injective j := π.V.injective_subtype.comp D.inj
  have hm : ∀ u ∈ (⨅ w, isoSp (D.σ w) (M w) : Submodule ℂ D.U),
      j u ∈ Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c) := fun u hu => by
    refine Submodule.subset_span ⟨(π.cusp _ (D.i u).2).1, (D.rng _).1 ⟨u, rfl⟩, coeff_mem W _ fun g w x => ?_,
      fun τ z => hc τ z _ (D.i u).2⟩
    convert iso_coef (D.σ w) (M w)
      ((LinearMap.proj (g * infGL E n (Unitary.toUnits x))).comp ((Sm E n).subtype.comp j))
      ((Submodule.mem_iInf _).1 hu w) using 2 with a
    refine Eq.trans ?_ ((D.hσ w a u _).trans (along_glue w a _ _)).symm
    simp only [map_mul, mul_assoc]
    rfl
  exact FiniteDimensional.of_injective (j.restrict hm) fun a b e =>
    Subtype.ext (hj (congrArg (fun y : Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (sig W) c) => y.1) e))
