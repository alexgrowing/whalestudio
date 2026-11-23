import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma exists_cube {ι Y : Type} [Finite ι] [TopologicalSpace Y] {y₀ : Y} {W : Set (ι → Y)}
    (hW : W ∈ 𝓝 (fun _ => y₀ : ι → Y)) :
    ∃ U ∈ 𝓝 y₀, ∀ y : ι → Y, (∀ i, y i ∈ U) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy => hsub fun i _ => Set.mem_iInter.1 (hy i) i⟩

private noncomputable def fin0 {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) : A F := (0, x)

private lemma continuous_finiteAdeleEmbed {F : Type} [Field F] [NumberField F] :
    Continuous (fin0 (F := F)) :=
  show Continuous fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from
    continuous_const.prodMk continuous_id

private noncomputable def oneAdd {F : Type} [Field F] [NumberField F]
    (X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (A F) :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + fin0 (X (i, j))

private lemma continuous_oneAdd {F : Type} [Field F] [NumberField F] :
    Continuous (oneAdd (F := F)) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.add (continuous_finiteAdeleEmbed.comp (continuous_apply _))

private lemma oneAdd_zero {F : Type} [Field F] [NumberField F] :
    oneAdd (F := F) (fun _ => 0) = 1 := by
  ext i j : 2
  change (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + 0 = _
  exact add_zero _

theorem UpperTheory.ConvolutionTheory.R2.C.unrOf :
    ∀ (F : Type) [Field F] [NumberField F] (P : G1 F → Prop), (∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → P g) → ∀ᶠ v in cofinite, ∀ g, At v g → IntAt v g → P g := by
  intro F _ _ P h
  have hind : IsInducing (fun g : G1 F => (g : Matrix (Fin 2) (Fin 2) (A F))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing
  rw [Filter.Eventually, hind.nhds_eq_comap, Filter.mem_comap] at h
  obtain ⟨S, hS, hSP⟩ := h
  have h1 : S ∈ 𝓝 (oneAdd (F := F) fun _ => 0) := by
    rw [oneAdd_zero]; simpa using hS
  have h2 := continuous_oneAdd.continuousAt.preimage_mem_nhds h1
  obtain ⟨U, hU, hUS⟩ := exists_cube h2
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hU
  have hfin : ((idealSupport J : Finset _) : Set (HeightOneSpectrum (𝓞 F))).Finite :=
    Finset.finite_toSet _
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  by_contra hvJ
  apply hv
  intro g hg hint
  have hone : ∀ i j, ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij]
    · simp [Matrix.one_apply, hij]
  set X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F :=
    fun p => (g p.1 p.2).2 - ((1 : Matrix (Fin 2) (Fin 2) (A F)) p.1 p.2).2 with hX
  have hXm : ∀ p, X p ∈ U := by
    intro p
    apply hJ
    rw [SetLike.mem_coe, mem_idealFiniteAdeles]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [count_eq_zero_of_not_mem_idealSupport J (by simpa using hvJ)]
      simp only [neg_zero, WithZero.exp_zero]
      exact sub_mem (hint p.1 p.2) (hone p.1 p.2)
    · have : X p w = 0 := by
        have := hg.2 w hw p.1 p.2
        simp only [hX]
        exact sub_eq_zero.2 this
      rw [this, map_zero]
      exact zero_le
  have hgX : (g : Matrix (Fin 2) (Fin 2) (A F)) = oneAdd X := by
    ext i j : 2
    apply Prod.ext
    · have : (oneAdd X i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 + 0 := rfl
      rw [this, add_zero]
      exact hg.1 i j
    · have : (oneAdd X i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 + X (i, j) := rfl
      rw [this, hX]
      simp
  apply hSP
  · show (g : Matrix (Fin 2) (Fin 2) (A F)) ∈ S
    rw [hgX]
    exact hUS X hXm
  · exact hg.1
