import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryKTypeFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompactStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsOpenIsCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegBump

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutMult
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.IsoTypes

section Abstract

variable {G K : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {ρ : G →* (K →L[ℂ] K)}

theorem finiteDimensional_types (hρ : IsUnitaryRep ρ) (hc : EnoughCompact ρ)
    (hiso : ∀ W (hW : IsIrredSubrep ρ W), isoPart hW.1.rep ρ ⊤ = ⊤)
    {C V : Type} [Group C] [AddCommGroup V] [Module ℂ V] (j : C →* G) (τ : Representation ℂ C V)
    (hfd : ∀ W (hW : IsIrredSubrep ρ W), FiniteDimensional ℂ ↥(⨆ (T : V →ₗ[ℂ] W)
      (_ : ∀ k w, T (τ k w) = hW.1.rep (j k) (T w)), LinearMap.range T : Submodule ℂ W)) :
    FiniteDimensional ℂ ↥(⨆ (T : V →ₗ[ℂ] K) (_ : ∀ k w, T (τ k w) = ρ (j k) (T w)),
      LinearMap.range T : Submodule ℂ K) := by
  classical
  obtain ⟨ι, W, hW, hs⟩ := exists_isHilbertSum hρ fun _ => hc.exists_irred_le hρ
  have hcomp : ∀ i, CompleteSpace (W i) := fun i => (hW i).1.completeSpace
  have hfin : Finite ι := by
    by_cases hne : Nonempty ι
    · obtain ⟨i0⟩ := hne
      have hπ := isIrrUnitary_rep hρ (hW i0)
      have hset := (multIn_eq_ncard hρ hπ (hc.multIn_lt hρ hπ) hW hs).1
      have huniv : {i | IsCopy (hW i0).1.rep ρ (W i)} = Set.univ := Set.eq_univ_of_forall fun i => by
        refine ⟨(hW i).1, ?_⟩
        by_contra hn
        have hπi := isIrrUnitary_rep hρ (hW i)
        have hS : (W i).subtypeL ∈ homIn (hW i).1.rep ρ ⊤ := mem_homIn_top.2 fun _ _ => rfl
        have hle : isoPart (hW i0).1.rep ρ ⊤ ≤ (W i)ᗮ :=
          isoPart_le (Submodule.isClosed_orthogonal _) fun T hT x =>
            (Submodule.mem_orthogonal _ _).2 fun u hu =>
              inner_eq_zero_of_not_uEquiv hπ hπi hρ hn hT hS x ⟨u, hu⟩
        rw [hiso _ (hW i0), top_le_iff, Submodule.orthogonal_eq_top_iff] at hle
        exact (hW i).2.1 hle
      exact Set.finite_univ_iff.1 (huniv ▸ hset)
    · haveI := not_nonempty_iff.1 hne
      infer_instance
  have := Fintype.ofFinite ι
  have hsum : ∀ x : K, ∑ i, (W i).starProjection x = x := fun x => by
    refine hs.OrthogonalFamily.sum_projection_of_mem_iSup x ?_
    have h1 := hs.hasSum_linearIsometryEquiv_symm (hs.linearIsometryEquiv x)
    rw [LinearIsometryEquiv.symm_apply_apply] at h1
    rw [h1.unique (hasSum_fintype _)]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i (Subtype.prop _)
  let Q : ι → Submodule ℂ K := fun i => (⨆ (T : V →ₗ[ℂ] W i)
    (_ : ∀ k w, T (τ k w) = (hW i).1.rep (j k) (T w)), LinearMap.range T : Submodule ℂ (W i)).map (W i).subtype
  have hQ : ∀ i, FiniteDimensional ℂ (Q i) := fun i => by
    have := hfd _ (hW i)
    infer_instance
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Q i) (iSup₂_le fun T hT => ?_)
  rintro _ ⟨w, rfl⟩
  rw [← hsum (T w)]
  refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
  let Ti : V →ₗ[ℂ] W i := LinearMap.codRestrict (W i) ((W i).starProjection.toLinearMap ∘ₗ T)
    fun w => (W i).starProjection_apply_mem _
  refine ⟨Ti w, Submodule.mem_iSup_of_mem Ti (Submodule.mem_iSup_of_mem (fun k w => Subtype.ext ?_) ⟨w, rfl⟩), rfl⟩
  change (W i).starProjection (T (τ k w)) = ρ (j k) ((W i).starProjection (T w))
  rw [hT, (hW i).1.starProjection_apply hρ]

theorem isoPart_eq_top {Γ G' L P : Type} [Group Γ] [Group G'] [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] [CompleteSpace L] [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    {R : Γ →* (L →L[ℂ] L)} (i : G →* Γ) (j : G' →* Γ) (hτ : IsUnitaryRep (R.comp i))
    (hcomm : ∀ a b, i a * j b = j b * i a) (hdec : ∀ γ, ∃ a b, γ = i a * j b)
    {H X : Submodule ℂ L} (hH : IsIrredSubrep R H) (hXH : X ≤ H) (hX : IsSubrep (R.comp i) X)
    {π : G →* (P →L[ℂ] P)} (h0 : homIn π hX.rep ⊤ ≠ ⊥) : isoPart π hX.rep ⊤ = ⊤ := by
  have := hX.completeSpace
  have hI : IsSubrep hX.rep (isoPart π hX.rep ⊤) := isSubrep_isoPart
  have hstab : ∀ S ∈ homIn hX.rep hX.rep ⊤, ∀ x ∈ isoPart π hX.rep ⊤, S x ∈ isoPart π hX.rep ⊤ := fun S hS x hx =>
    isoPart_le (W := (isoPart π hX.rep ⊤).comap (S : X →ₗ[ℂ] X)) (hI.1.preimage S.continuous)
      (fun T hT y => apply_mem_isoPart (T := S ∘L T) (mem_homIn_top.2 fun g x => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [hT.2, hS.2]) y) hx
  let Y : Submodule ℂ L := (isoPart π hX.rep ⊤).map X.subtype
  have hYc : IsClosed (Y : Set L) := hX.1.isClosedEmbedding_subtypeVal.isClosedMap _ hI.1
  let Sb : G' → (X →L[ℂ] X) := fun b =>
    ((X.starProjection ∘L R (j b)) ∘L X.subtypeL).codRestrict X fun v => X.starProjection_apply_mem _
  have hSb : ∀ b, Sb b ∈ homIn hX.rep hX.rep ⊤ := fun b => mem_homIn_top.2 fun a x => Subtype.ext (by
    change X.starProjection (R (j b) (R (i a) x)) = R (i a) (X.starProjection (R (j b) x))
    have e : R (j b) (R (i a) x) = R (i a) (R (j b) (x : L)) := by
      have := congrArg (fun S : L →L[ℂ] L => S (x : L)) (congrArg R (hcomm a b))
      simpa using this.symm
    rw [e]
    exact hX.starProjection_apply hτ a _)
  let Z : Submodule ℂ L := (⨆ γ, Y.map (R γ : L →ₗ[ℂ] L)).topologicalClosure
  have hZ : IsSubrep R Z := isSubrep_topologicalClosure fun g v hv => by
    have h1 : (⨆ γ, Y.map (R γ : L →ₗ[ℂ] L)) ≤ (⨆ γ, Y.map (R γ : L →ₗ[ℂ] L)).comap (R g : L →ₗ[ℂ] L) :=
      iSup_le fun γ => by
        rintro _ ⟨y, hy, rfl⟩
        refine Submodule.mem_iSup_of_mem (g * γ) ⟨y, hy, ?_⟩
        simp
    exact h1 hv
  have hYZ : Y ≤ Z := fun y hy => Submodule.le_topologicalClosure _
    (Submodule.mem_iSup_of_mem 1 ⟨y, hy, by simp⟩)
  have hZH : Z ≤ H := Submodule.topologicalClosure_minimal _ (iSup_le fun γ => by
    rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    exact hH.1.2 γ _ (hXH x.2)) hH.1.1
  have hZ0 : Z ≠ ⊥ := by
    obtain ⟨T, hT, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨x, hx⟩ : ∃ x, T x ≠ 0 := by
      by_contra! hn
      exact hT0 (ContinuousLinearMap.ext hn)
    refine (Submodule.ne_bot_iff _).2 ⟨_, hYZ ⟨_, apply_mem_isoPart hT x, rfl⟩, fun e => hx (Subtype.ext e)⟩
  have hZe : Z = H := (hH.2.2 Z hZH hZ).resolve_left hZ0
  have hQZ : Z ≤ Y.comap (X.starProjection : L →ₗ[ℂ] L) :=
    Submodule.topologicalClosure_minimal _ (iSup_le fun γ => by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨a, b, rfl⟩ := hdec γ
      have e : R (i a * j b) (x : L) = R (j b) (R (i a) x) := by
        rw [hcomm]; simp
      have h1 : hX.rep a x ∈ isoPart π hX.rep ⊤ := hI.2 a x hx
      exact ⟨_, hstab _ (hSb b) _ h1, by
        change X.starProjection (R (j b) (R (i a) x)) = X.starProjection (R (i a * j b) (x : L))
        rw [e]⟩) (hYc.preimage X.starProjection.continuous)
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, e⟩ := hQZ (hZe ▸ hXH x.2)
  have e' : y = x := Subtype.ext (e.trans (Submodule.starProjection_eq_self_iff.2 x.2))
  exact e' ▸ hy

theorem commute_of_inner_eq_integral {Γ : Type} [MeasurableSpace Γ] {μ : Measure Γ} {p : Γ → G} {f : Γ → ℂ}
    {A : K →L[ℂ] K} (hA : ∀ y x, ⟪y, A x⟫_ℂ = ∫ g, f g * ⟪y, ρ (p g) x⟫_ℂ ∂μ) {S : K →L[ℂ] K}
    (hS : S ∈ homIn ρ ρ ⊤) (x : K) : A (S x) = S (A x) := ext_inner_left ℂ fun y => by
  rw [← ContinuousLinearMap.adjoint_inner_left S, hA, hA]
  refine integral_congr_ae (.of_forall fun g => ?_)
  change f g * _ = f g * _
  rw [← hS.2, ContinuousLinearMap.adjoint_inner_left]

theorem apply_ne_zero_of_inner_eq_integral {Γ : Type} [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ]
    [OpensMeasurableSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (hρ : IsUnitaryRep ρ) {p : Γ → G} (hp : Continuous p) (hp1 : p 1 = 1) {f : Γ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (h0 : 0 ≤ f) (h1 : f 1 ≠ 0) {A : K →L[ℂ] K} {v : K} (hv : v ≠ 0)
    (hpos : ∀ g, f g ≠ 0 → 0 < (⟪v, ρ (p g) v⟫_ℂ).re)
    (hA : ⟪v, A v⟫_ℂ = ∫ g, (f g : ℂ) * ⟪v, ρ (p g) v⟫_ℂ ∂μ) : A v ≠ 0 := by
  intro e
  have hcc : Continuous fun g => ⟪v, ρ (p g) v⟫_ℂ :=
    continuous_const.inner ((hρ.continuous_apply v).comp hp)
  have hc : Continuous fun g => (⟪v, ρ (p g) v⟫_ℂ).re := Complex.continuous_re.comp hcc
  have hcf : Continuous fun g => (f g : ℂ) := Complex.continuous_ofReal.comp hf
  have hcs : HasCompactSupport fun g => (f g : ℂ) := hs.comp_left (g := Complex.ofReal) rfl
  have h3 := integral_re (𝕜 := ℂ) (μ := μ) ((hcf.mul hcc).integrable_of_hasCompactSupport hcs.mul_right)
  have h4 : 0 < (⟪v, ρ (p 1) v⟫_ℂ).re := by
    simpa [hp1] using (re_inner_self_pos (𝕜 := ℂ)).2 hv
  refine ((hf.mul hc).integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) hs.mul_right (fun g => ?_)
    (mul_ne_zero h1 h4.ne')).ne' ?_
  · by_cases hg : f g = 0
    · simp [hg]
    · exact mul_nonneg (h0 g) (hpos g hg).le
  · rw [e, inner_zero_right] at hA
    simpa [← hA] using h3

end Abstract

section Abstract2

variable {G Γ G' L : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ] [Group G']
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

theorem finiteDimensional_types_of_irred {R : Γ →* (L →L[ℂ] L)} (i : G →* Γ) (j : G' →* Γ)
    (hτ : IsUnitaryRep (R.comp i)) (hcomm : ∀ a b, i a * j b = j b * i a) (hdec : ∀ γ, ∃ a b, γ = i a * j b)
    {H X : Submodule ℂ L} (hH : IsIrredSubrep R H) (hXH : X ≤ H) (hX : IsSubrep (R.comp i) X)
    (hc : EnoughCompact hX.rep) {C V : Type} [Group C] [AddCommGroup V] [Module ℂ V] (e : C →* G)
    (τ : Representation ℂ C V)
    (hadm : ∀ (P : Type) [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] (σ : G →* (P →L[ℂ] P)),
      IsUnitaryRep σ → IsTopIrreducible σ → FiniteDimensional ℂ ↥(⨆ (T : V →ₗ[ℂ] P)
        (_ : ∀ k w, T (τ k w) = σ (e k) (T w)), LinearMap.range T : Submodule ℂ P)) :
    FiniteDimensional ℂ ↥(⨆ (T : V →ₗ[ℂ] L)
      (_ : (∀ k w, T (τ k w) = R (i (e k)) (T w)) ∧ ∀ w, T w ∈ X), LinearMap.range T : Submodule ℂ L) := by
  have hρ := hX.isUnitaryRep hτ
  have hcpl := hX.completeSpace
  have hfd := finiteDimensional_types hρ hc
    (fun W' hW' => isoPart_eq_top i j hτ hcomm hdec hH hXH hX (fun h0 => hW'.2.1 (by
        have h1 : W'.subtypeL ∈ homIn hW'.1.rep hX.rep ⊤ := mem_homIn_top.2 fun _ _ => rfl
        rw [h0, Submodule.mem_bot] at h1
        exact eq_bot_iff.2 fun x hx => by
          simpa using DFunLike.congr_fun h1 ⟨x, hx⟩)))
    e τ (fun W' hW' => by
      have := hW'.1.completeSpace
      exact hadm W' hW'.1.rep (hW'.1.isUnitaryRep hρ) (hW'.1.isIrredSubrep_iff.1 hW'))
  refine Submodule.finiteDimensional_of_le (S₂ := (⨆ (T : V →ₗ[ℂ] X)
    (_ : ∀ k w, T (τ k w) = hX.rep (e k) (T w)), LinearMap.range T : Submodule ℂ X).map X.subtype)
    (iSup₂_le fun T hT => ?_)
  rintro _ ⟨w, rfl⟩
  let T' : V →ₗ[ℂ] X := T.codRestrict _ hT.2
  exact ⟨T' w, Submodule.mem_iSup_of_mem T' (Submodule.mem_iSup_of_mem (fun k w => Subtype.ext (hT.1 k w)) ⟨w, rfl⟩), rfl⟩

def compress (X : Submodule ℂ L) [X.HasOrthogonalProjection] (T : L →L[ℂ] L) : X →L[ℂ] X :=
  ((X.starProjection ∘L T) ∘L X.subtypeL).codRestrict X fun _ => X.starProjection_apply_mem _

omit [CompleteSpace L] in

theorem inner_compress (X : Submodule ℂ L) [X.HasOrthogonalProjection] (T : L →L[ℂ] L) (y x : X) :
    ⟪y, compress X T x⟫_ℂ = ⟪(y : L), T x⟫_ℂ := by
  change ⟪(y : L), X.starProjection (T x)⟫_ℂ = _
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 y.2]

omit [CompleteSpace L] in

theorem isCompactOperator_compress {X Y : Submodule ℂ L} [X.HasOrthogonalProjection] (hXY : X ≤ Y)
    {T : L →L[ℂ] L} {T' : Y →L[ℂ] Y} (hT : ∀ y : Y, (T' y : L) = T y) (hc : IsCompactOperator T') :
    IsCompactOperator (compress X T) := by
  let i₁ : X →L[ℂ] Y := X.subtypeL.codRestrict Y fun x => hXY x.2
  let i₂ : Y →L[ℂ] X := (X.starProjection ∘L Y.subtypeL).codRestrict X fun _ => X.starProjection_apply_mem _
  have e2 : compress X T = i₂ ∘L T' ∘L i₁ := by
    ext x
    change X.starProjection (T x) = X.starProjection _
    exact congrArg _ (hT (i₁ x)).symm
  rw [e2]
  exact (hc.comp_clm i₁).clm_comp i₂

theorem enoughCompact_of_testFn [IsTopologicalGroup Γ] [MeasurableSpace Γ] [OpensMeasurableSpace Γ] {μ : Measure Γ}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {R : Γ →* (L →L[ℂ] L)} (hR : IsUnitaryRep R) (i : G →* Γ)
    (hτ : IsUnitaryRep (R.comp i)) {p : Γ → G} (hp : Continuous p) (hp1 : p 1 = 1) {X Y : Submodule ℂ L} (hXY : X ≤ Y)
    (hX : IsSubrep (R.comp i) X) (hY : IsSubrep R Y)
    (hc : ∀ f : Γ → ℂ, Continuous f → HasCompactSupport f → IsCompactOperator (repOp hY.rep μ f))
    (htest : ∀ v : X, v ≠ 0 → ∃ f : Γ → ℝ, Continuous f ∧ HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      (∀ g, f g ≠ 0 → ∀ x ∈ X, R g x = R (i (p g)) x) ∧ ∀ g, f g ≠ 0 → 0 < (⟪v, hX.rep (p g) v⟫_ℂ).re) :
    EnoughCompact hX.rep := by
  intro v hv
  have hcpl := hX.completeSpace
  obtain ⟨f, hf, hfs, hf0, hf1, hfR, hpos⟩ := htest v hv
  have hfc : Continuous fun g => (f g : ℂ) := Complex.continuous_ofReal.comp hf
  have hfcs : HasCompactSupport fun g => (f g : ℂ) := hfs.comp_left (g := Complex.ofReal) rfl
  have hA : ∀ y x : X, ⟪y, compress X (repOp R μ fun g => (f g : ℂ)) x⟫_ℂ =
      ∫ g, (f g : ℂ) * ⟪y, hX.rep (p g) x⟫_ℂ ∂μ := by
    intro y x
    rw [inner_compress, hR.inner_repOp hfc hfcs]
    refine integral_congr_ae (.of_forall fun g => ?_)
    by_cases h0 : f g = 0
    · simp [h0]
    · change (f g : ℂ) * _ = (f g : ℂ) * ⟪(y : L), R (i (p g)) x⟫_ℂ
      rw [hfR g h0 x x.2]
  refine ⟨_, isCompactOperator_compress hXY (hY.coe_repOp_rep (hR.isRepOp (μ := μ) hfc hfcs)).2 (hc _ hfc hfcs),
    fun S hS x => commute_of_inner_eq_integral hA hS x, ?_⟩
  exact apply_ne_zero_of_inner_eq_integral (μ := μ) (hX.isUnitaryRep hτ) hp hp1 hf hfs hf0 hf1 hv hpos (hA v v)

end Abstract2

section Concrete

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

omit [IsTotallyComplex E] in

theorem continuous_finGL : Continuous (finGL E a) := by
  have hs : Continuous (sFin E) := (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sFin E))) (continuous_const.add (continuous_id.matrix_map hs))

omit [IsTotallyComplex E] in

theorem locallyCompactSpace_GL : LocallyCompactSpace (GL (Fin a) (Cinf E)) := by
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Cinf E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Cinf E))
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Cinf E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_testFn {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) :
    ∃ f : GA E a → ℝ, Continuous f ∧ HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      ∀ g, f g ≠ 0 → GeneralLinearGroup.map (pInf E) g ∈ N ∧ GeneralLinearGroup.map (pFin E) g ∈ U := by
  classical
  haveI := locallyCompactSpace_GL (E := E) (a := a)
  obtain ⟨φ, hφ, hφs, hφ0, hφ1, hφN⟩ := GlobalTheory.CompanionTheory.Bump.exists_nonneg_bump (1 : GL (Fin a) (Cinf E)) N hN
  have hpi := ContAut.continuous_map_pInf E a
  have hpf := ContAut.continuous_map_pFin E a
  let χ : GL (Fin a) (Af E) → ℝ := (U : Set (GL (Fin a) (Af E))).indicator fun _ => 1
  have hχ : Continuous χ := by
    refine continuous_indicator (fun x hx => ?_) continuousOn_const
    rw [IsClopen.frontier_eq ⟨U.isClosed_of_isOpen hU, hU⟩] at hx
    exact absurd hx (Set.notMem_empty _)
  refine ⟨fun g => φ (GeneralLinearGroup.map (pInf E) g) * χ (GeneralLinearGroup.map (pFin E) g),
    (hφ.comp hpi).mul (hχ.comp hpf), ?_, fun g => ?_, ?_, fun g h => ⟨hφN (left_ne_zero_of_mul h),
      Set.mem_of_indicator_ne_zero (right_ne_zero_of_mul h)⟩⟩
  · refine HasCompactSupport.intro (K := (fun p : GL (Fin a) (Cinf E) × GL (Fin a) (Af E) =>
      infGL E a p.1 * finGL E a p.2) '' (tsupport φ ×ˢ (U : Set (GL (Fin a) (Af E)))))
      ((hφs.isCompact.prod hUc).image ((continuous_infGL.comp continuous_fst).mul
        (continuous_finGL.comp continuous_snd))) fun g hg => ?_
    by_contra h0
    have h1 : φ (GeneralLinearGroup.map (pInf E) g) ≠ 0 := left_ne_zero_of_mul h0
    have h2 : χ (GeneralLinearGroup.map (pFin E) g) ≠ 0 := right_ne_zero_of_mul h0
    exact hg ⟨(_, _), ⟨subset_tsupport _ h1, Set.mem_of_indicator_ne_zero h2⟩, infGL_mul_finGL g⟩
  · exact mul_nonneg (hφ0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · have h1 : χ 1 = 1 := Set.indicator_of_mem (one_mem U) _
    simpa [h1] using hφ1

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def fixedPart (H : Submodule ℂ (L2 (latticeGL E a) μ)) (U : Subgroup (GL (Fin a) (Af E))) :
    Submodule ℂ (L2 (latticeGL E a) μ) where
  carrier := {F | F ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) F = F}
  add_mem' := fun h h' => ⟨H.add_mem h.1 h'.1, fun u hu => by rw [map_add, h.2 u hu, h'.2 u hu]⟩
  zero_mem' := ⟨H.zero_mem, fun _ _ => map_zero _⟩
  smul_mem' := fun c _ h => ⟨H.smul_mem c h.1, fun u hu => by rw [map_smul, h.2 u hu]⟩

variable {μ}

theorem fixedPart_le (H : Submodule ℂ (L2 (latticeGL E a) μ)) (U : Subgroup (GL (Fin a) (Af E))) :
    fixedPart μ H U ≤ H := fun _ h => h.1

theorem isSubrep_fixedPart {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hH : IsSubrep (R (latticeGL E a) μ) H)
    (U : Subgroup (GL (Fin a) (Af E))) :
    IsSubrep ((R (latticeGL E a) μ).comp (infGL E a)) (fixedPart μ H U) := by
  constructor
  · have e : (fixedPart μ H U : Set (L2 (latticeGL E a) μ)) =
        (H : Set (L2 (latticeGL E a) μ)) ∩ ⋂ u ∈ U, {F | R (latticeGL E a) μ (finGL E a u) F = F} := by
      ext F
      simp [fixedPart]
    rw [e]
    exact hH.1.inter (isClosed_biInter fun u _ =>
      isClosed_eq (R (latticeGL E a) μ (finGL E a u)).continuous continuous_id)
  · rintro y F ⟨h1, h2⟩
    refine ⟨hH.2 _ _ h1, fun u hu => ?_⟩
    have e := congrArg (fun S : L2 (latticeGL E a) μ →L[ℂ] L2 (latticeGL E a) μ => S F)
      (congrArg (R (latticeGL E a) μ) (infGL_comm y u))
    simp only [map_mul, ContinuousLinearMap.mul_apply, h2 u hu] at e
    exact e.symm

theorem R_apply_of_mem {H : Submodule ℂ (L2 (latticeGL E a) μ)} {U : Subgroup (GL (Fin a) (Af E))}
    {F : L2 (latticeGL E a) μ} (hF : F ∈ fixedPart μ H U) {g : GA E a}
    (hg : GeneralLinearGroup.map (pFin E) g ∈ U) :
    R (latticeGL E a) μ g F = R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g)) F := by
  conv_lhs => rw [← infGL_mul_finGL g, map_mul, ContinuousLinearMap.mul_apply, hF.2 _ hg]

theorem enoughCompact_fixedPart {H : Submodule ℂ (L2 (latticeGL E a) μ)} (hHc : H ≤ L2cusp μ)
    (hH : IsSubrep (R (latticeGL E a) μ) H) {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) : EnoughCompact (isSubrep_fixedPart hH U).rep := by
  have hR := isUnitaryRep_R (latticeGL E a) μ
  have hτ : IsUnitaryRep ((R (latticeGL E a) μ).comp (infGL E a)) := isUnitaryRep_comp hR continuous_infGL
  refine enoughCompact_of_testFn (μ := μ) hR (infGL E a) hτ (ContAut.continuous_map_pInf E a) (map_one _)
    ((fixedPart_le H U).trans hHc) (isSubrep_fixedPart hH U) (isSubrep_L2cusp μ) (GlobalTheory.T.cuspidal_convolution_compact E a μ) fun v hv => ?_
  have hρ := (isSubrep_fixedPart hH U).isUnitaryRep hτ
  have hcv : Continuous fun x : GL (Fin a) (Cinf E) => (⟪v, (isSubrep_fixedPart hH U).rep x v⟫_ℂ).re :=
    Complex.continuous_re.comp (continuous_const.inner (hρ.continuous_apply v))
  have h1v : 0 < (⟪v, (isSubrep_fixedPart hH U).rep 1 v⟫_ℂ).re := by
    simpa using (re_inner_self_pos (𝕜 := ℂ)).2 hv
  obtain ⟨f, hf, hfs, hf0, hf1, hfg⟩ := exists_testFn ((isOpen_lt continuous_const hcv).mem_nhds h1v) hU hUc
  exact ⟨f, hf, hfs, hf0, hf1, fun g h x hx => R_apply_of_mem hx (hfg g h).2, fun g h => (hfg g h).1⟩

end Concrete

theorem finiteDimensional_isotypic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧ ∀ w, T w ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (T w) = T w), LinearMap.range T : Submodule ℂ (L2 (latticeGL E a) μ)) := by
  intro E _ _ _ a μ _ _ H hH hI U hU W _ _ _ ρ
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
  have hU' : IsOpen ((U ⊓ K0 : Subgroup _) : Set (GL (Fin a) (Af E))) := hU.inter hK0o
  have hU'c : IsCompact ((U ⊓ K0 : Subgroup _) : Set (GL (Fin a) (Af E))) :=
    hK0c.inter_left (U.isClosed_of_isOpen hU)
  have hfd := finiteDimensional_types_of_irred (infGL E a) (finGL E a)
    (isUnitaryRep_comp (isUnitaryRep_R (latticeGL E a) μ) continuous_infGL) infGL_comm
    (fun g => ⟨_, _, (infGL_mul_finGL g).symm⟩) hI (fixedPart_le H _) (isSubrep_fixedPart hI.1 (U ⊓ K0))
    (enoughCompact_fixedPart hH hI.1 hU' hU'c) (Unitary.toUnits : Kinf E a →* GL (Fin a) (Cinf E)) ρ
    (fun P _ _ _ σ h1 h2 => GlobalTheory.T.unitary_K_type_finite E a P σ h1 h2 W ρ)
  have key : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {S T : Submodule ℂ M}, FiniteDimensional ℂ T → S ≤ T →
      FiniteDimensional ℂ S := fun _ h => Submodule.finiteDimensional_of_le h
  exact key hfd (iSup₂_le fun T hT =>
    le_iSup₂_of_le (f := fun (T : W →ₗ[ℂ] L2 (latticeGL E a) μ) (_ : (∀ k w, T (ρ k w) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (T w)) ∧ ∀ w, T w ∈ fixedPart μ H (U ⊓ K0)) => LinearMap.range T) T
      ⟨hT.1, fun w => ⟨(hT.2 w).1, fun u hu => (hT.2 w).2 u hu.1⟩⟩ le_rfl)

end GlobalTheory.CompanionTheory.IsoTypes

end
